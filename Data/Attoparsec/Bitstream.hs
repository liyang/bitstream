{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | TODO: @scan@
module Data.Attoparsec.Bitstream
    ( -- * Parser types
      Parser, Result, IResult (..), compareResults
    , module Data.Attoparsec.Bitstream
    -- * Combinators
    , try, (<?>), choice, count, option
    , many', many1, many1', manyTill, manyTill'
    , sepBy, sepBy', sepBy1, sepBy1'
    , skipMany, skipMany1, eitherP, match
    -- * State observation and manipulation functions
    , endOfInput, atEnd
    ) where

import Prelude hiding (takeWhile)

import Control.Applicative
import Control.Monad
import Data.Bits
import Data.Monoid
import Data.String

import Data.Attoparsec.Combinator as AP
import Data.Attoparsec.Internal
import Data.Attoparsec.Internal.Types hiding (Parser, Failure, Success)
import qualified Data.Attoparsec.Internal.Types as AP

import Data.Attoparsec.Bitstream.Internal
import Data.Bitstream (Bitstream)
import qualified Data.Bitstream as B hiding (Bitstream)
import qualified Data.Bitstream.Generic as B
import qualified Data.Bitstream.Lazy as L

instance (bs ~ Bitstream lr, B.Bitstream bs) => IsString (Parser lr bs) where
    fromString = string

-- * Running parsers
{- {{{ -}

-- | Run a parser.
parse :: (bs ~ Bitstream lr, B.Bitstream bs) => Parser lr a -> bs -> Result lr a
parse m s = runParser m s (Pos 0) Incomplete failK successK
{-# INLINE parse #-}

-- | If a parser has returned a 'Partial' result, supply it with more
-- input.
feed :: (bs ~ Bitstream lr, B.Bitstream bs) => Result lr r -> bs -> Result lr r
feed = AP.feed
{-# INLINE feed #-}

-- | Run a parser that cannot be resupplied via a 'Partial' result.
--
-- This function does not force a parser to consume all of its input.
-- Instead, any residual input will be discarded.  To force a parser
-- to consume all of its input, use something like this:
--
-- @
--'parseOnly' (myParser '<*' 'endOfInput')
-- @
parseOnly :: (bs ~ Bitstream lr, B.Bitstream bs) =>
    Parser lr a -> bs -> Either String a
parseOnly m s = case runParser m s (Pos 0) Complete failK successK of
    Fail _ _ err -> Left err
    Done _ a -> Right a
    _ -> error "parseOnly: impossible error!"
{-# INLINE parseOnly #-}

-- | Run a parser with an initial input string, and a monadic action
-- that can supply more input if needed.
parseWith :: (bs ~ Bitstream lr, B.Bitstream bs, Monad m) => m bs
    -- ^ An action that will be executed to provide the parser with more
    -- input, if necessary. The action must return an 'B.empty' string when
    -- there is no more input available.
    -> Parser lr a -> bs
    -- ^ Initial input for the parser.
    -> m (Result lr a)
parseWith refill p s = step $ parse p s where
    step (Partial k) = step . k =<< refill
    step r = return r
{-# INLINE parseWith #-}

-- | Run a parser and print its result to standard output.
parseTest :: (bs ~ Bitstream lr, B.Bitstream bs, Show a, Show bs) =>
    Parser lr a -> bs -> IO ()
parseTest p s = print (parse p s)

{- }}} -}

-- ** Result conversion
{- {{{ -}

-- | Convert a 'Result' value to a 'Maybe' value. A 'Partial' result
-- is treated as failure.
maybeResult :: Result lr r -> Maybe r
maybeResult (Done _ r) = Just r
maybeResult _ = Nothing

-- | Convert a 'Result' value to an 'Either' value. A 'Partial'
-- result is treated as failure.
eitherResult :: Result lr r -> Either String r
eitherResult (Done _ r) = Right r
eitherResult (Fail _ _ msg) = Left msg
eitherResult _ = Left "Result: incomplete input"

{- }}} -}

-- * Parsing individual bits
{- {{{ -}

-- | Match a specific bit.
bool :: (bs ~ Bitstream lr, B.Bitstream bs) => Bool -> Parser lr Bool
bool c = satisfy (c ==) <?> show c
{-# INLINE bool #-}

-- | Match any bit.
anyBool :: (bs ~ Bitstream lr, B.Bitstream bs) => Parser lr Bool
anyBool = satisfy $ const True
{-# INLINE anyBool #-}

-- | Match any bit except the given one.
notBool :: (bs ~ Bitstream lr, B.Bitstream bs) => Bool -> Parser lr Bool
notBool c = satisfy (/= c) <?> "not " ++ show c
{-# INLINE notBool #-}

-- | The parser @satisfy p@ succeeds for any bit for which the
-- predicate @p@ returns 'True'. Returns the bit that is actually
-- parsed.
--
-- >digit = satisfy isDigit
-- >    where isDigit w = w >= 48 && w <= 57
satisfy :: (bs ~ Bitstream lr, B.Bitstream bs) =>
    (Bool -> Bool) -> Parser lr Bool
satisfy p = do
  h <- peekBool'
  if p h then h <$ advance 1 else fail "satisfy"
{-# INLINE satisfy #-}

-- | The parser @satisfyWith f p@ transforms a byte, and succeeds if
-- the predicate @p@ returns 'True' on the transformed value. The
-- parser returns the transformed byte that was parsed.
satisfyWith :: (bs ~ Bitstream lr, B.Bitstream bs) =>
    (Bool -> a) -> (a -> Bool) -> Parser lr a
satisfyWith f p = do
  h <- peekBool'
  let c = f h
  if p c then c <$ advance 1 else fail "satisfyWith"
{-# INLINE satisfyWith #-}

-- | The parser @skip p@ succeeds for any bit for which the predicate
-- @p@ returns 'True'.
--
-- >skipDigit = skip isDigit
-- >    where isDigit w = w >= 48 && w <= 57
skip :: (bs ~ Bitstream lr, B.Bitstream bs) => (Bool -> Bool) -> Parser lr ()
skip p = do
  h <- peekBool'
  if p h
    then advance 1
    else fail "skip"

{- }}} -}

-- ** Lookahead
{- {{{ -}

-- | Match any bit, to perform lookahead. Returns 'Nothing' if end of
-- input has been reached. Does not consume any input.
--
-- /Note/: Because this parser does not fail, do not use it with
-- combinators such as 'Control.Applicative.many', because such
-- parsers loop until a failure occurs.  Careless use will thus result
-- in an infinite loop.
peekBool :: (bs ~ Bitstream lr, B.Bitstream bs) => Parser lr (Maybe Bool)
peekBool = AP.Parser $ \ t pos@(Pos pos_) more _nope yupp -> case () of
    _| pos_ < B.length t -> let !w = t B.!! pos_ in yupp t pos more (Just w)
     | more == Complete -> yupp t pos more Nothing
     | otherwise -> prompt t pos more
        (\ t' pos' more' -> yupp t' pos' more' Nothing)
        (\ t' pos' more' -> let !w = t B.!! pos_ in yupp t' pos' more' (Just w))
{-# INLINE peekBool #-}

-- | Match any bit, to perform lookahead.  Does not consume any
-- input, but will fail if end of input has been reached.
peekBool' :: (bs ~ Bitstream lr, B.Bitstream bs) => Parser lr Bool
peekBool' = AP.Parser $ \ t pos more nope yupp -> if lengthAtLeast pos 1 t
    then yupp t pos more (t B.!! fromPos pos)
    else ensureSuspended 1 t pos more nope
        (\ t' pos' more' bs' -> yupp t' pos' more' $! B.head bs')
{-# INLINE peekBool' #-}

{- }}} -}

-- * Efficient bitstring handling
{- {{{ -}

-- | @string s@ parses a sequence of bits that identically match
-- @s@. Returns the parsed string (i.e. @s@).  This parser consumes no
-- input if it fails (even if a partial match).
--
-- /Note/: The behaviour of this parser is different to that of the
-- similarly-named parser in Parsec, as this one is all-or-nothing.
-- To illustrate the difference, the following parser will fail under
-- Parsec given an input of @\"for\"@:
--
-- >string "foo" <|> string "for"
--
-- The reason for its failure is that the first branch is a
-- partial match, and will consume the letters @\'f\'@ and @\'o\'@
-- before failing.  In attoparsec, the above parser will /succeed/ on
-- that input, because the failed first branch will consume nothing.
string :: forall lr bs. (bs ~ Bitstream lr, B.Bitstream bs) =>
    String -> Parser lr bs
string expect = takeWith len $ if len <= finiteBitSize (0 :: Int)
        then p (0 :: Int) else p (0 :: Integer) where
    len = length expect

    p :: (Integral t, Bits t) => t -> bs -> Bool
    p t = \ bs -> B.toBits bs .&. mask == bits `asTypeOf` t where
        (mask, bits) = foldl maskbits (0, 0) expect
        maskbits ((`shiftL` 1) -> !m, (`shiftL` 1) -> !b) c = case c of
            '0' -> o; 'o' -> o; 'O' -> o; 'n' -> o; 'N' -> o
            '1' -> i; 'i' -> i; 'I' -> i; 'y' -> i; 'Y' -> i
            _ -> (m, b)
          where
            o = (m .|. 1, b)
            i = (m .|. 1, b .|. 1)
{-# INLINE string #-}

-- | Skip past input for as long as the predicate returns 'True'.
skipWhile :: (bs ~ Bitstream lr, B.Bitstream bs) =>
    (Bool -> Bool) -> Parser lr ()
skipWhile p = go where
    go = do
        t <- B.takeWhile p <$> get
        continue <- inputSpansChunks (B.length t)
        when continue go
{-# INLINE skipWhile #-}

-- | Consume exactly @n@ bits of input.
take :: (bs ~ Bitstream lr, B.Bitstream bs) => Int -> Parser lr bs
take n = takeWith n (const True)
{-# INLINE take #-}

-- | Consume input as long as the predicate returns 'True', and return
-- the consumed input.
--
-- This parser does not fail.  It will return an empty string if the
-- predicate returns 'False' on the first byte of input.
--
-- /Note/: Because this parser does not fail, do not use it with
-- combinators such as 'Control.Applicative.many', because such
-- parsers loop until a failure occurs.  Careless use will thus result
-- in an infinite loop.
takeWhile :: (bs ~ Bitstream lr, B.Bitstream bs) =>
    (Bool -> Bool) -> Parser lr bs
takeWhile p = B.concat . reverse <$> go [] where
    go acc = do
        s <- B.takeWhile p <$> get
        continue <- inputSpansChunks (B.length s)
        if continue then go (s:acc) else return (s:acc)
{-# INLINE takeWhile #-}

-- | Consume input as long as the predicate returns 'True', and return
-- the consumed input.
--
-- This parser requires the predicate to succeed on at least one byte
-- of input: it will fail if the predicate never returns 'True' or if
-- there is no input left.
takeWhile1 :: forall lr bs. (bs ~ Bitstream lr, B.Bitstream bs) =>
    (Bool -> Bool) -> Parser lr bs
takeWhile1 p = do
    (`when` demandInput) =<< endOfChunk
    s <- B.takeWhile p <$> get
    let len = B.length s
    if len == 0 then fail "takeWhile1" else do
        advance len
        eoc <- endOfChunk
        if eoc then mappend s <$> takeWhile p else return s
  where
    endOfChunk :: Parser lr Bool
    endOfChunk = AP.Parser $ \ t pos more _nope yupp ->
        yupp t pos more (fromPos pos == B.length t)
    {-# INLINE endOfChunk #-}

-- | Consume input as long as the predicate returns 'False'
-- (i.e. until it returns 'True'), and return the consumed input.
--
-- This parser does not fail.  It will return an empty string if the
-- predicate returns 'True' on the first byte of input.
--
-- /Note/: Because this parser does not fail, do not use it with
-- combinators such as 'Control.Applicative.many', because such
-- parsers loop until a failure occurs.  Careless use will thus result
-- in an infinite loop.
takeTill :: (bs ~ Bitstream lr, B.Bitstream bs) =>
    (Bool -> Bool) -> Parser lr bs
takeTill p = takeWhile (not . p)
{-# INLINE takeTill #-}

{- }}} -}

-- ** Consume all remaining input
{- {{{ -}

-- | Consume all remaining input and return it as a single stream.
takeBitstream :: (bs ~ Bitstream lr, B.Bitstream bs) => Parser lr bs
takeBitstream = B.concat <$> takeRest

-- | Consume all remaining input and return it as a single lazy stream.
takeLazyBitstream :: (bs ~ Bitstream lr, B.Bitstream bs) =>
    Parser lr (L.Bitstream lr)
takeLazyBitstream = L.fromChunks <$> takeRest

{- }}} -}

