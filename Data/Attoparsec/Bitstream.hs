{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
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
import Prelude.Unicode

import Control.Applicative
import Control.Monad
import Data.Bits
import Data.Char
import Data.Monoid
import Data.String
import Data.Word

import Data.Attoparsec.Combinator as AP
#if TRUE_NAME
import Data.Attoparsec.ByteString (compareResults)
import Data.Attoparsec.Types hiding (Parser)
#else
import Data.Attoparsec.Internal hiding (demandInput, prompt)
import Data.Attoparsec.Internal.Types hiding (Parser, Failure, Success)
#endif

import Data.Attoparsec.Bitstream.Internal
import Data.Bitstream (Bitstream)
import qualified Data.Bitstream as B hiding (Bitstream)
import qualified Data.Bitstream.Generic as B
import qualified Data.Bitstream.Lazy as L
import Data.Bitstream.Packet (Packet)

instance (α ~ Bitstream d, B.Bitstream α) ⇒ IsString (Parser d α) where
    fromString = pattern

-- * Running parsers
{- {{{ -}

-- | Run a parser.
parse ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d a → α → Result d a
parse m s = runParser m s (toPos 0) isIncomplete failK successK
{-# INLINE parse #-}

-- | If a parser has returned a 'Partial' result, supply it with more
-- input.
feed ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Result d r → α → Result d r
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
parseOnly ∷ (α ~ Bitstream d, B.Bitstream α) ⇒
    Parser d a → α → Either String a
parseOnly m s = case runParser m s (toPos 0) isComplete failK successK of
    Fail _ _ err → Left err
    Done _ a → Right a
    _ → error "parseOnly: impossible error!"
{-# INLINE parseOnly #-}

-- | Run a parser with an initial input string, and a monadic action
-- that can supply more input if needed.
parseWith ∷ (α ~ Bitstream d, B.Bitstream α, Monad m) ⇒ m α
    -- ^ An action that will be executed to provide the parser with more
    -- input, if necessary. The action must return an 'B.∅' string when
    -- there is no more input available.
    → Parser d a → α
    -- ^ Initial input for the parser.
    → m (Result d a)
parseWith refill p s = step $ parse p s where
    step (Partial k) = step ∘ k =<< refill
    step r = return r
{-# INLINE parseWith #-}

-- | Run a parser and print its result to standard output.
parseTest ∷ (α ~ Bitstream d, B.Bitstream α, Show a, Show α) ⇒
    Parser d a → α → IO ()
parseTest p s = print (parse p s)

{- }}} -}

-- ** Result conversion
{- {{{ -}

-- | Convert a 'Result' value to a 'Maybe' value. A 'Partial' result
-- is treated as failure.
maybeResult ∷ Result d r → Maybe r
maybeResult (Done _ r) = Just r
maybeResult _ = Nothing

-- | Convert a 'Result' value to an 'Either' value. A 'Partial'
-- result is treated as failure.
eitherResult ∷ Result d r → Either String r
eitherResult (Done _ r) = Right r
eitherResult (Fail _ _ msg) = Left msg
eitherResult _ = Left "Result: incomplete input"

{- }}} -}

-- * Parsing individual bits
{- {{{ -}

-- | Match a specific bit.
bool ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Bool → Parser d Bool
bool c = satisfy (c ≡) <?> show c
{-# INLINE bool #-}

-- | Match any bit.
anyBool ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d Bool
anyBool = satisfy $ const True
{-# INLINE anyBool #-}

-- | Match any bit except the given one.
notBool ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Bool → Parser d Bool
notBool c = satisfy (c ≢) <?> "not " ⧺ show c
{-# INLINE notBool #-}

-- | The parser @satisfy p@ succeeds for any bit for which the
-- predicate @p@ returns 'True'. Returns the bit that is actually
-- parsed.
--
-- >digit = satisfy isDigit
-- >    where isDigit w = w ≥ 48 ∧ w ≤ 57
satisfy ∷ (α ~ Bitstream d, B.Bitstream α) ⇒
    (Bool → Bool) → Parser d Bool
satisfy p = do
  h ← peekBool'
  if p h then h <$ advance 1 else fail "satisfy"
{-# INLINE satisfy #-}

-- | The parser @satisfyWith f p@ transforms a byte, and succeeds if
-- the predicate @p@ returns 'True' on the transformed value. The
-- parser returns the transformed byte that was parsed.
satisfyWith ∷ (α ~ Bitstream d, B.Bitstream α) ⇒
    (Bool → a) → (a → Bool) → Parser d a
satisfyWith f p = do
  h ← peekBool'
  let c = f h
  if p c then c <$ advance 1 else fail "satisfyWith"
{-# INLINE satisfyWith #-}

-- | The parser @skip p@ succeeds for any bit for which the predicate
-- @p@ returns 'True'.
--
-- >skipDigit = skip isDigit
-- >    where isDigit w = w ≥ 48 ∧ w ≤ 57
skip ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ (Bool → Bool) → Parser d ()
skip p = do
  h ← peekBool'
  if p h
    then advance 1
    else fail "skip"

{- }}} -}

-- ** Lookahead
{- {{{ -}

-- | Match any bit, to perform lookahead. Returns 'Nothing' if
-- end of input has been reached. Does not consume any input.
--
-- /Note/: Because this parser does not fail, do not use it with
-- combinators such as 'Control.Applicative.many', because such
-- parsers loop until a failure occurs.  Careless use will thus
-- result in an infinite loop.
peekBool ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d (Maybe Bool)
peekBool = toParser $ \ β pos more _nope yupp → case () of
    _| fromPos pos < B.length β → yupp β pos more . Just $! β B.!! fromPos pos
     | more ≡ isComplete → yupp β pos more Nothing
     | otherwise → prompt β pos more
        (\ β' pos' more' → yupp β' pos' more' Nothing)
        (\ β' pos' more' → yupp β' pos' more' . Just $! β B.!! fromPos pos)
{-# INLINE peekBool #-}

-- | Match any bit, to perform lookahead.  Does not consume any
-- input, but will fail if end of input has been reached.
peekBool' ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d Bool
peekBool' = toParser $ \ β pos more nope yupp → if lengthAtLeast pos 1 β
    then yupp β pos more (β B.!! fromPos pos)
    else ensureSuspended 1 β pos more nope
        (\ β' pos' more' α' → yupp β' pos' more' $! B.head α')
{-# INLINE peekBool' #-}

{- }}} -}

-- * Efficient bitstring handling
{- {{{ -}

-- | @pattern s@ parses a sequence of bits that match @s@, where each 'Char'
-- may be either @\'0\'@, @\'1\'@, or @\'x\'@; characters matching 'isSpace'
-- are ignored. (Alternatively―without regard for case―@[ofn]@, @[ity]@, or
-- any other character respectively.)
--
-- Returns the matched bitstream.
-- This parser consumes no input if it fails (even if a partial match).
--
-- Synonymous with @'fromString'@, for use with
-- <https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/type-class-extensions.html#overloaded-strings OverloadedStrings>:
--
-- @
-- instance (α ~ 'Bitstream' d, 'B.Bitstream' α) ⇒ 'IsString' ('Parser' d α)
-- @
pattern ∷ ∀ α d. (α ~ Bitstream d, B.Bitstream α) ⇒
    String → Parser d α
pattern expect@(filter (not . isSpace) -> expect') = takeWith
    ("pattern " ⧺ show expect) len $ if len ≤ finiteBitSize (0 ∷ Word)
        then p (0 ∷ Word) else p (0 ∷ ℤ) where
    len = length expect'

    {-# SPECIALISE p ∷ Word → α → Bool #-}
    {-# SPECIALISE p ∷ Integer → α → Bool #-}
    p ∷ (Integral w, Bits w) ⇒ w → α → Bool
    p w = \ α → B.toBits α .&. ms ≡ bs `asTypeOf` w where
        (ms, bs) = foldl maskbits (0, 0) expect'
        maskbits ((`shiftL` 1) → !m, (`shiftL` 1) → !b) c = case c of
            '0' → o; '1' → i
            _ → case toLower c of -- alternatives
                'o' → o; 'i' → i
                'f' → o; 't' → i
                'n' → o; 'y' → i
                _ → (m, b)
          where
            o = (m .|. 1, b)
            i = (m .|. 1, b .|. 1)
{-# INLINE pattern #-}

-- | @bits α@ parses a bitstream that identically match @α@.
--
-- Returns the parsed bitstream (i.e. @α@).
-- This parser consumes no input if it fails (even if a partial match).
bits ∷ ∀ α π d. (α ~ Bitstream d, B.Bitstream α, π ~ Packet d, Show π) ⇒
    α → Parser d α
bits α = takeWith ("bits " ⧺ show α) (B.length α) (α ≡)
{-# INLINE bits #-}

maskBits ∷ (α ~ Bitstream d, B.Bitstream α, Integral w, Bits w, Show w) =>
    Int → w → w → Parser d α
maskBits len ms bs = takeWith (unwords ["mask", show len, show ms, show bs])
    len (\ α → B.toBits α .&. ms ≡ bs)
{-# INLINE maskBits #-}

-- | Skip past input for as long as the predicate returns 'True'.
skipWhile ∷ (α ~ Bitstream d, B.Bitstream α) ⇒
    (Bool → Bool) → Parser d ()
skipWhile p = go where
    go = do
        α ← B.takeWhile p <$> get
        continue ← inputSpansChunks (B.length α)
        when continue go
{-# INLINE skipWhile #-}

-- | Consume exactly @n@ bits of input.
take ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Int → Parser d α
take n = takeWith ("take " ⧺ show n) n (const True)
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
takeWhile ∷ (α ~ Bitstream d, B.Bitstream α) ⇒
    (Bool → Bool) → Parser d α
takeWhile p = B.concat ∘ reverse <$> go [] where
    go acc = do
        s ← B.takeWhile p <$> get
        continue ← inputSpansChunks (B.length s)
        (if continue then go else return) (s : acc)
{-# INLINE takeWhile #-}

-- | Consume input as long as the predicate returns 'True', and return
-- the consumed input.
--
-- This parser requires the predicate to succeed on at least one byte
-- of input: it will fail if the predicate never returns 'True' or if
-- there is no input left.
takeWhile1 ∷ ∀ α d. (α ~ Bitstream d, B.Bitstream α) ⇒
    (Bool → Bool) → Parser d α
takeWhile1 p = do
    (`when` demandInput) =<< endOfChunk
    s ← B.takeWhile p <$> get
    let len = B.length s
    if len ≡ 0 then fail "takeWhile1" else do
        advance len
        eoc ← endOfChunk
        if eoc then mappend s <$> takeWhile p else return s
  where
    endOfChunk ∷ Parser d Bool
    endOfChunk = toParser $ \ β pos more _nope yupp →
        yupp β pos more (fromPos pos ≡ B.length β)
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
takeTill ∷ (α ~ Bitstream d, B.Bitstream α) ⇒
    (Bool → Bool) → Parser d α
takeTill p = takeWhile (not ∘ p)
{-# INLINE takeTill #-}

{- }}} -}

-- ** Consume all remaining input
{- {{{ -}

-- | Consume all remaining input and return it as a single stream.
takeBitstream ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d α
takeBitstream = B.concat <$> takeRest

-- | Consume all remaining input and return it as a single lazy stream.
takeLazyBitstream ∷ (α ~ Bitstream d, B.Bitstream α) ⇒
    Parser d (L.Bitstream d)
takeLazyBitstream = L.fromChunks <$> takeRest

{- }}} -}

