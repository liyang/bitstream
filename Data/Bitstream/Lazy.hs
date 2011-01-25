{-# LANGUAGE
    FlexibleContexts
  , ScopedTypeVariables
  , UndecidableInstances
  , UnicodeSyntax
  #-}
module Data.Bitstream.Lazy
    ( -- * Types
      Bitstream
    , Left
    , Right

      -- * Introducing and eliminating 'Bitstream's
    , empty
    , (∅)
    , singleton
    , pack
    , unpack
    , fromChunks
    , toChunks

      -- ** Converting from\/to lazy 'BS.ByteString's
    , fromByteString
    , toByteString

      -- ** Converting from\/to 'S.Stream's
    , stream
    , unstream

      -- * Changing bit order in octets
    , directionLToR
    , directionRToL

      -- * Basic interface
    , cons
    , cons'
    , snoc
    , snoc'
    )
    where
import qualified Data.Bitstream as Strict
import Data.Bitstream.Generic hiding (Bitstream)
import qualified Data.Bitstream.Generic as G
import Data.Bitstream.Internal
import Data.Bitstream.Packet
import qualified Data.ByteString.Lazy as LS
import qualified Data.List.Stream as L
import qualified Data.StorableVector as SV
import qualified Data.StorableVector.Lazy as LV
import qualified Data.Stream as S
import Foreign.Storable
import Prelude ( Bool(..), Eq(..), Int, Integral, Maybe(..), Monad(..), Num(..)
               , Ord(..), Ordering(..), Show(..), ($), div, error, fmap
               , fromIntegral, fst, otherwise
               )
import Prelude.Unicode

-- 32 KiB * sizeOf (Packet d) == 64 KiB
chunkSize ∷ LV.ChunkSize
chunkSize = LV.ChunkSize (32 ⋅ 1024)
{-# INLINE chunkSize #-}

newtype Bitstream d
    = Bitstream (LV.Vector (Packet d))
    deriving (Eq, Show)

instance G.Bitstream (Packet d) ⇒ G.Bitstream (Bitstream d) where
    {-# INLINE [0] pack #-}
    pack xs0 = Bitstream (LV.unfoldr chunkSize f xs0)
        where
          {-# INLINE f #-}
          f xs = case L.splitAt 8 xs of
                   (hd, tl)
                       | L.null hd → Nothing
                       | otherwise → Just (pack hd, tl)

    {-# INLINE [0] unpack #-}
    unpack (Bitstream v) = L.concatMap unpack (LV.unpack v)

    {-# INLINE [0] stream #-}
    stream (Bitstream v)
        = {-# CORE "lazy bitstream 'stream'" #-}
          S.concatMap G.stream (streamLV v)

    {-# INLINE [0] unstream #-}
    unstream
        = {-# CORE "lazy bitstream 'unstream'" #-}
          Bitstream ∘ unstreamLV chunkSize ∘ packStream

    {-# INLINE empty #-}
    empty = Bitstream LV.empty

    {-# INLINE singleton #-}
    singleton b
        = Bitstream (LV.singleton (singleton b))

    {-# INLINE cons #-}
    cons b (Bitstream v)
        = Bitstream (LV.cons (singleton b) v)

    {-# INLINE snoc #-}
    snoc (Bitstream v) b
        = Bitstream (LV.append v (LV.singleton (singleton b)))

{-# INLINE fromChunks #-}
fromChunks ∷ [Strict.Bitstream d] → Bitstream d
fromChunks = Bitstream ∘ LV.fromChunks ∘ L.map Strict.toPackets

{-# INLINE toChunks #-}
toChunks ∷ Bitstream d → [Strict.Bitstream d]
toChunks (Bitstream v) = L.map Strict.fromPackets (LV.chunks v)

{-# INLINE fromByteString #-}
fromByteString ∷ LS.ByteString → Bitstream d
fromByteString = Bitstream ∘ fromLBS

{-# INLINE toByteString #-}
toByteString ∷ G.Bitstream (Packet d) ⇒ Bitstream d → LS.ByteString
toByteString (Bitstream v) = toLBS v

{-# INLINE directionLToR #-}
directionLToR ∷ Bitstream Left → Bitstream Right
directionLToR (Bitstream v) = Bitstream (LV.map packetLToR v)

{-# INLINE directionRToL #-}
directionRToL ∷ Bitstream Right → Bitstream Left
directionRToL (Bitstream v) = Bitstream (LV.map packetRToL v)

{-# INLINEABLE cons' #-}
{-# SPECIALISE cons' ∷ Bool → Bitstream Left  → Bitstream Left  #-}
{-# SPECIALISE cons' ∷ Bool → Bitstream Right → Bitstream Right #-}
cons' ∷ G.Bitstream (Packet d) ⇒ Bool → Bitstream d → Bitstream d
cons' b (Bitstream v)
    = case LV.viewL v of
        Just (p, v')
            | length p < (8 ∷ Int)
                  → Bitstream (consLV' (cons b p) v')
            | otherwise
                  → Bitstream (consLV'' chunkSize (singleton b) v)
        Nothing   → Bitstream (LV.singleton (singleton b))

{-# INLINEABLE snoc' #-}
{-# SPECIALISE snoc' ∷ Bitstream Left  → Bool → Bitstream Left  #-}
{-# SPECIALISE snoc' ∷ Bitstream Right → Bool → Bitstream Right #-}
snoc' ∷ G.Bitstream (Packet d) ⇒ Bitstream d → Bool → Bitstream d
snoc' (Bitstream v) b
    = case LV.viewR v of
        Just (v', p)
            | length p < (8 ∷ Int)
                  → Bitstream (snocLV' v' (snoc p b))
            | otherwise
                  → Bitstream (snocLV'' chunkSize v (singleton b))
        Nothing   → Bitstream (LV.singleton (singleton b))

{-# INLINE consLV' #-}
consLV' ∷ Storable α ⇒ α → LV.Vector α → LV.Vector α
consLV' α v
    = case LV.chunks v of
        (x:xs) → LV.fromChunks (SV.cons α x : xs)
        []     → LV.singleton α

{-# INLINE consLV'' #-}
consLV'' ∷ Storable α ⇒ LV.ChunkSize → α → LV.Vector α → LV.Vector α
consLV'' (LV.ChunkSize cs) α v
    = case LV.chunks v of
        (x:xs)
            | SV.length x < cs
                  → LV.fromChunks (SV.cons α x : xs)
            | otherwise
                  → LV.fromChunks (SV.singleton α : x : xs)
        []        → LV.singleton α

{-# INLINE snocLV' #-}
snocLV' ∷ Storable α ⇒ LV.Vector α → α → LV.Vector α
snocLV' v α = LV.fromChunks (go (LV.chunks v))
    where
      {-# INLINE go #-}
      go []     = [SV.singleton α]
      go (x:[]) = [SV.snoc x α]
      go (x:xs) = x : go xs

{-# INLINE snocLV'' #-}
snocLV'' ∷ Storable α ⇒ LV.ChunkSize → LV.Vector α → α → LV.Vector α
snocLV'' (LV.ChunkSize cs) v α = LV.fromChunks (go (LV.chunks v))
    where
      {-# INLINE go #-}
      go []     = [SV.singleton α]
      go (x:[])
          | SV.length x < cs
                = [SV.snoc x α]
          | otherwise
                = [x, SV.singleton α]
      go (x:xs) = x : go xs
