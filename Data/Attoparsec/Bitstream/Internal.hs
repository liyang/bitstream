{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Attoparsec.Bitstream.Internal where

import Prelude
import Prelude.Unicode

import Control.Applicative

import Data.Attoparsec.Internal.Types hiding (Parser, Failure, Success)
import qualified Data.Attoparsec.Internal.Types as AP

import Data.Bitstream (Bitstream)
import qualified Data.Bitstream as B hiding (Bitstream)
import qualified Data.Bitstream.Generic as B

type Parser d = AP.Parser (Bitstream d)
type Result d = IResult (Bitstream d)

type instance State (Bitstream d) = Bitstream d

type Failure d r = AP.Failure (Bitstream d) (Bitstream d) r
type Success d a r = AP.Success (Bitstream d) (Bitstream d) a r

toParser = AP.Parser
toPos = Pos
isComplete = Complete; isIncomplete = Incomplete
toParser ∷ (∀ r. Bitstream d → Pos → More →
    Failure d r → Success d a r → Result d r) → Parser d a
toPos ∷ Int → Pos
isComplete, isIncomplete ∷ More

instance B.Bitstream (Bitstream d) ⇒ Chunk (Bitstream d) where
    type ChunkElem (Bitstream d) = Bool
    nullChunk = B.null
    {-# INLINE nullChunk #-}
    pappendChunk = B.append
    {-# INLINE pappendChunk #-}
    atBufferEnd _ = toPos ∘ B.length
    {-# INLINE atBufferEnd #-}
    bufferElemAt _ i β = if fromPos i < B.length β
        then Just (β B.!! fromPos i, 1) else Nothing
    {-# INLINE bufferElemAt #-}
    chunkElemToChar _ b = if b then '1' else '0'
    {-# INLINE chunkElemToChar #-}

-- | Terminal failure continuation.
failK ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Failure d a
failK β pos _more stack msg = Fail (B.drop (fromPos pos) β) stack msg
{-# INLINE failK #-}

-- | Terminal success continuation.
successK ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Success d a a
successK β pos _more a = Done (B.drop (fromPos pos) β) a
{-# INLINE successK #-}

advance ∷ Int → Parser d ()
advance n = toParser $ \ β pos more _nope yupp → yupp β (pos + toPos n) more ()
{-# INLINE advance #-}

lengthAtLeast ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Pos → Int → α → Bool
lengthAtLeast pos n α = B.length α ≥ fromPos pos + n
{-# INLINE lengthAtLeast #-}

substring ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Pos → Int → α → α
substring pos n = B.take n ∘ B.drop (fromPos pos)
{-# INLINE substring #-}

-- | Ask for input.  If we receive any, pass it to a success continuation,
-- otherwise to a failure continuation.
--
-- Duplicated and specialised for 'Bitstream'.
prompt ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ α → Pos → More →
    (α → Pos → More → Result d r) →
    (α → Pos → More → Result d r) → Result d r
prompt β pos _more nope yupp = Partial $ \ s → if B.null s
    then nope β pos isComplete else yupp (B.append β s) pos isIncomplete

-- | Immediately demand more input via a 'Partial' continuation result.
--
-- Duplicated and specialised for 'Bitstream'.
demandInput ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d ()
demandInput = toParser $ \ β pos more nope yupp → if more ≡ isComplete
    then nope β pos more [] "not enough input" else prompt β pos more
        (\ β' pos' more' → nope β' pos' more' [] "not enough input")
        (\ β' pos' more' → yupp β' pos' more' ())

ensureSuspended ∷ (α ~ Bitstream d, B.Bitstream α) ⇒
    Int → α → Pos → More →
    Failure d r → Success d α r → Result d r
ensureSuspended n β pos more nope yupp =
        runParser (demandInput >> go) β pos more nope yupp where
    go = toParser $ \ β' pos' more' nope' yupp' → if lengthAtLeast pos' n β'
        then yupp' β' pos' more' (substring pos n β')
        else runParser (demandInput >> go) β' pos' more' nope' yupp'

-- | If at least @n@ elements of input are available, return the
-- current input, otherwise fail.
ensure ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Int → Parser d α
ensure n = toParser $ \ β pos more nope yupp → if lengthAtLeast pos n β
    then yupp β pos more (substring pos n β)
    -- The uncommon case is kept out-of-line to reduce code size:
    else ensureSuspended n β pos more nope yupp
-- Non-recursive so the bounds check can be inlined:
{-# INLINE ensure #-}

inputSpansChunks ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Int → Parser d Bool
inputSpansChunks i = toParser $ \ β ((toPos i +) → pos) more _nope yupp →
    if fromPos pos < B.length β ∨ more ≡ isComplete
    then yupp β pos more False else prompt β pos more
        (\ β' pos' more' → yupp β' pos' more' False)
        (\ β' pos' more' → yupp β' pos' more' True)
{-# INLINE inputSpansChunks #-}

-- | Consume @n@ bits of input, but succeed only if the predicate
-- returns 'True'.
takeWith ∷ (α ~ Bitstream d, B.Bitstream α) ⇒
    String → Int → (α → Bool) → Parser d α
takeWith desc n0 p = do
    let n = max n0 0
    s ← ensure n
    if p s then s <$ advance n else fail desc

get ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d α
get = toParser $ \ β pos more _nope yupp →
    yupp β pos more (B.drop (fromPos pos) β)
{-# INLINE get #-}

-- | This parser always succeeds. It returns 'True' if any input is
-- available either immediately or on demand, and 'False' if the end
-- of all input has been reached.
--
-- Duplicated and specialised for 'Bitstream'.
wantInput ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d Bool
wantInput = toParser $ \ β pos more _nope yupp →
    if fromPos pos < B.length β then yupp β pos more True else
    if more ≡ isComplete then yupp β pos more False else prompt β pos more
        (\ β' pos' more' → yupp β' pos' more' False)
        (\ β' pos' more' → yupp β' pos' more' True)
{-# INLINE wantInput #-}

takeRest ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d [α]
takeRest = go [] where
    go acc = do
        input ← wantInput
        if input
        then do
            s ← get
            advance (B.length s)
            go (s : acc)
        else return (reverse acc)

-- | Return both the result of a parse and the portion of the input
-- that was consumed while it was being parsed.
match ∷ (α ~ Bitstream d, B.Bitstream α) ⇒ Parser d a → Parser d (α, a)
match p = toParser $ \ β pos more nope yupp →
    runParser p β pos more nope $ \ β' pos' more' a →
        yupp β' pos' more' (substring pos (fromPos $ pos' - pos) β', a)

