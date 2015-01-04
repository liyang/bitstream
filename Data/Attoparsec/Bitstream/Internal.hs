{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Attoparsec.Bitstream.Internal where

import Data.Attoparsec.Internal
import Data.Attoparsec.Internal.Types hiding (Parser, Failure, Success)
import qualified Data.Attoparsec.Internal.Types as AP

import Data.Bitstream (Bitstream)
import qualified Data.Bitstream as B hiding (Bitstream)
import qualified Data.Bitstream.Generic as B

type Parser lr = AP.Parser (Bitstream lr)
type Result lr = IResult (Bitstream lr)

type instance State (Bitstream lr) = Bitstream lr

type Failure lr r = AP.Failure (Bitstream lr) (Bitstream lr) r
type Success lr a r = AP.Success (Bitstream lr) (Bitstream lr) a r

instance B.Bitstream (Bitstream lr) => Chunk (Bitstream lr) where
    type ChunkElem (Bitstream lr) = Bool
    nullChunk = B.null
    {-# INLINE nullChunk #-}
    pappendChunk = B.append
    {-# INLINE pappendChunk #-}
    atBufferEnd _ = Pos . B.length
    {-# INLINE atBufferEnd #-}
    bufferElemAt _ (Pos i) buf
        | i < B.length buf = Just (buf B.!! i, 1)
        | otherwise = Nothing
    {-# INLINE bufferElemAt #-}
    chunkElemToChar _ b = if b then '1' else '0'
    {-# INLINE chunkElemToChar #-}

-- | Terminal failure continuation.
failK :: (bs ~ Bitstream lr, B.Bitstream bs) => Failure lr a
failK t (Pos pos) _more stack msg = Fail (B.drop pos t) stack msg
{-# INLINE failK #-}

-- | Terminal success continuation.
successK :: (bs ~ Bitstream lr, B.Bitstream bs) => Success lr a a
successK t (Pos pos) _more a = Done (B.drop pos t) a
{-# INLINE successK #-}

advance :: Int -> Parser lr ()
advance n = AP.Parser $ \ t pos more _nope yupp -> yupp t (pos + Pos n) more ()
{-# INLINE advance #-}

lengthAtLeast :: (bs ~ Bitstream lr, B.Bitstream bs) => Pos -> Int -> bs -> Bool
lengthAtLeast (Pos pos) n bs = B.length bs >= pos + n
{-# INLINE lengthAtLeast #-}

substring :: (bs ~ Bitstream lr, B.Bitstream bs) => Pos -> Pos -> bs -> bs
substring (Pos pos) (Pos n) = B.take n . B.drop pos
{-# INLINE substring #-}

ensureSuspended :: (bs ~ Bitstream lr, B.Bitstream bs) =>
    Int -> bs -> Pos -> More ->
    Failure lr r -> Success lr bs r -> Result lr r
ensureSuspended n t pos more nope yupp =
        runParser (demandInput >> go) t pos more nope yupp where
    go = AP.Parser $ \ t' pos' more' nope' yupp' -> if lengthAtLeast pos' n t'
        then yupp' t' pos' more' (substring pos (Pos n) t')
        else runParser (demandInput >> go) t' pos' more' nope' yupp'

-- | If at least @n@ elements of input are available, return the
-- current input, otherwise fail.
ensure :: (bs ~ Bitstream lr, B.Bitstream bs) => Int -> Parser lr bs
ensure n = AP.Parser $ \ t pos more nope yupp -> if lengthAtLeast pos n t
    then yupp t pos more (substring pos (Pos n) t)
    -- The uncommon case is kept out-of-line to reduce code size:
    else ensureSuspended n t pos more nope yupp
-- Non-recursive so the bounds check can be inlined:
{-# INLINE ensure #-}

inputSpansChunks :: (bs ~ Bitstream lr, B.Bitstream bs) => Int -> Parser lr Bool
inputSpansChunks i = AP.Parser $ \ t ((+ Pos i) -> pos) more _nope yupp ->
    if fromPos pos < B.length t || more == Complete
    then yupp t pos more False else prompt t pos more
        (\ t' pos' more' -> yupp t' pos' more' False)
        (\ t' pos' more' -> yupp t' pos' more' True)
{-# INLINE inputSpansChunks #-}

-- | Consume @n@ bits of input, but succeed only if the predicate
-- returns 'True'.
takeWith :: (bs ~ Bitstream lr, B.Bitstream bs) =>
    Int -> (bs -> Bool) -> Parser lr bs
takeWith n0 p = do
    let n = max n0 0
    s <- ensure n
    if p s then advance n >> return s else fail "takeWith"

get :: (bs ~ Bitstream lr, B.Bitstream bs) => Parser lr bs
get = AP.Parser $ \ t pos more _nope yupp ->
    yupp t pos more (B.drop (fromPos pos) t)
{-# INLINE get #-}

takeRest :: (bs ~ Bitstream lr, B.Bitstream bs) => Parser lr [bs]
takeRest = go [] where
    go acc = do
        input <- wantInput
        if input
        then do
            s <- get
            advance (B.length s)
            go (s:acc)
        else return (reverse acc)

-- | Return both the result of a parse and the portion of the input
-- that was consumed while it was being parsed.
match :: (bs ~ Bitstream lr, B.Bitstream bs) => Parser lr a -> Parser lr (bs, a)
match p = AP.Parser $ \ t pos more nope yupp -> runParser p t pos more nope $
    \ t' pos' more' a -> yupp t' pos' more' (substring pos (pos' - pos) t', a)

