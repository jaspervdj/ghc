{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE BangPatterns, CPP, MagicHash, NoImplicitPrelude, UnboxedTuples #-}

-- Copyright (c) 2014, Jasper Van der Jeugt and Simon Meier
-- All rights reserved.
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
--
--     * Redistributions of source code must retain the above
--       copyright notice, this list of conditions and the following
--       disclaimer.
--
--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials
--       provided with the distribution.
--
--     * The names of the contributors may not be used to endorse or
--       promote products derived from this software without specific
--       prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
-- FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
-- COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
-- INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
-- (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
-- HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
-- STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
-- ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
-- OF THE POSSIBILITY OF SUCH DAMAGE.

-- | A /priority search queue/ (henceforth /queue/) efficiently
-- supports the operations of both a search tree and a priority queue.
--
-- Many operatios have a worst-case complexity of O(min(n,W)). This means that
-- the operation can become linear in the number of elements with a maximum of
-- W, the number of bits in the key type (here Int64).
--
-- However, like an 'IntMap', it performs very well in practice.

-- This implementation was extracted from the 'pqueues' package by Jasper Van
-- der Jeugt, Simon Meier, and others.
-- <https://hackage.haskell.org/package/psqueues>.
module GHC.Event.IntPSQ
    ( -- * Type
      Key
    , IntPSQ

      -- * Query
    , null
    , size
    , member
    , lookup
    , findMin

      -- * Construction
    , empty
    , singleton

      -- * Insertion
    , insert

      -- * Delete/update
    , delete
    , adjust
    -- , alterMin

      -- * Lists
    , fromList
    , toList
    -- , keys
    , atMost

      -- * Views
    -- , insertView
    , deleteView
    , minView

      -- * Traversal
    , map
    , fold'
    ) where

import Data.Bits (complement, unsafeShiftR, xor, (.|.), (.&.))
import GHC.Base hiding (lookup, map, empty)
import GHC.Int (Int64)
import GHC.Num ((+), (-))
import GHC.Real (fromIntegral)
import GHC.Show (Show)
import GHC.Word (Word64)

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

-- A "Nat" is a natural machine word (an unsigned Int)
type Nat = Word64

type Key = Int64

-- | We store masks as the index of the bit that determines the branching.
type Mask = Int64

-- | A priority search queue with @Int@ keys and priorities of type @p@ and
-- values of type @v@. It is strict in keys, priorities and values.
data IntPSQ p v
    = Bin {-# UNPACK #-} !Key !p !v {-# UNPACK #-} !Mask !(IntPSQ p v) !(IntPSQ p v)
    | Tip {-# UNPACK #-} !Key !p !v
    | Nil
    deriving (Show)

instance (Ord p, Eq v) => Eq (IntPSQ p v) where
    x == y = case (minView x, minView y) of
        (Nothing              , Nothing                ) -> True
        (Just (xk, xp, xv, x'), (Just (yk, yp, yv, y'))) ->
            xk == yk && xp == yp && xv == yv && x' == y'
        (Just _               , Nothing                ) -> False
        (Nothing              , Just _                 ) -> False


-- bit twiddling
----------------

{-# INLINE natFromInt #-}
natFromInt :: Key -> Nat
natFromInt = fromIntegral

{-# INLINE intFromNat #-}
intFromNat :: Nat -> Key
intFromNat = fromIntegral

{-# INLINE zero #-}
zero :: Key -> Mask -> Bool
zero i m
  = (natFromInt i) .&. (natFromInt m) == 0

{-# INLINE nomatch #-}
nomatch :: Key -> Key -> Mask -> Bool
nomatch k1 k2 m =
    natFromInt k1 .&. m' /= natFromInt k2 .&. m'
  where
    m' = maskW (natFromInt m)

{-# INLINE maskW #-}
maskW :: Nat -> Nat
maskW m = complement (m-1) `xor` m

{-# INLINE branchMask #-}
branchMask :: Key -> Key -> Mask
branchMask k1 k2 =
    intFromNat (highestBitMask (natFromInt k1 `xor` natFromInt k2))

-- | Return a word where only the highest bit is set.
-- The implementation is based on
-- http://graphics.stanford.edu/~seander/bithacks.html#RoundUpPowerOf2
-- which has been put in the public domain.
highestBitMask :: Word64 -> Word64
highestBitMask x1 = let x2 = x1 .|. x1 `unsafeShiftR` 1
                        x3 = x2 .|. x2 `unsafeShiftR` 2
                        x4 = x3 .|. x3 `unsafeShiftR` 4
                        x5 = x4 .|. x4 `unsafeShiftR` 8
                        x6 = x5 .|. x5 `unsafeShiftR` 16
                        x7 = x6 .|. x6 `unsafeShiftR` 32
                     in x7 `xor` (x7 `unsafeShiftR` 1)
{-# INLINE highestBitMask #-}


------------------------------------------------------------------------------
-- Query
------------------------------------------------------------------------------

-- | /O(1)/ True if the queue is empty.
null :: IntPSQ p v -> Bool
null Nil = True
null _   = False

-- | /O(n)/ The number of elements stored in the PSQ.
size :: IntPSQ p v -> Int
size Nil               = 0
size (Tip _ _ _)       = 1
size (Bin _ _ _ _ l r) = 1 + size l + size r
-- TODO (SM): benchmark this against a tail-recursive variant

-- | /O(min(n,W))/ Check if a key is present in the the queue.
member :: Key -> IntPSQ p v -> Bool
member k t = case lookup k t of
    Nothing -> False
    Just _  -> True

-- | /O(min(n,W))/ The priority and value of a given key, or 'Nothing' if the
-- key is not bound.
lookup :: Key -> IntPSQ p v -> Maybe (p, v)
lookup k = go
  where
    go t = case t of
        Nil                -> Nothing

        Tip k' p' x'
          | k == k'        -> Just (p', x')
          | otherwise      -> Nothing

        Bin k' p' x' m l r
          | nomatch k k' m -> Nothing
          | k == k'        -> Just (p', x')
          | zero k m       -> go l
          | otherwise      -> go r

-- | /O(1)/ The element with the lowest priority.
findMin :: Ord p => IntPSQ p v -> Maybe (Key, p, v)
findMin t = case t of
    Nil              -> Nothing
    Tip k p x        -> Just (k, p, x)
    Bin k p x _ _ _  -> Just (k, p, x)


------------------------------------------------------------------------------
--- Construction
------------------------------------------------------------------------------

-- | /O(1)/ The empty queue.
empty :: IntPSQ p v
empty = Nil

-- | /O(1)/ Build a queue with one element.
singleton :: Ord p => Key -> p -> v -> IntPSQ p v
singleton = Tip


------------------------------------------------------------------------------
-- Insertion
------------------------------------------------------------------------------

-- | /O(min(n,W))/ Insert a new key, priority and value in the queue. If the key
-- is already present in the queue, the associated priority and value are
-- replaced with the supplied priority and value.
insert :: Ord p => Key -> p -> v -> IntPSQ p v -> IntPSQ p v
insert k p x t0 = unsafeInsertNew k p x (delete k t0)

-- | Internal function to insert a key that is *not* present in the priority
-- queue.
{-# INLINABLE unsafeInsertNew #-}
unsafeInsertNew :: Ord p => Key -> p -> v -> IntPSQ p v -> IntPSQ p v
unsafeInsertNew k p x = go
  where
    go t = case t of
      Nil       -> Tip k p x

      Tip k' p' x'
        | (p, k) < (p', k') -> link k  p  x  k' t           Nil
        | otherwise         -> link k' p' x' k  (Tip k p x) Nil

      Bin k' p' x' m l r
        | nomatch k k' m ->
            if (p, k) < (p', k')
              then link k  p  x  k' t           Nil
              else link k' p' x' k  (Tip k p x) (merge m l r)

        | otherwise ->
            if (p, k) < (p', k')
              then
                if zero k' m
                  then Bin k  p  x  m (unsafeInsertNew k' p' x' l) r
                  else Bin k  p  x  m l (unsafeInsertNew k' p' x' r)
              else
                if zero k m
                  then Bin k' p' x' m (unsafeInsertNew k  p  x  l) r
                  else Bin k' p' x' m l (unsafeInsertNew k  p  x  r)

-- | Link
link :: Key -> p -> v -> Key -> IntPSQ p v -> IntPSQ p v -> IntPSQ p v
link k p x k' k't otherTree
  | zero m k' = Bin k p x m k't       otherTree
  | otherwise = Bin k p x m otherTree k't
  where
    m = branchMask k k'


------------------------------------------------------------------------------
-- Delete/Alter
------------------------------------------------------------------------------

-- | /O(min(n,W))/ Delete a key and its priority and value from the queue. When
-- the key is not a member of the queue, the original queue is returned.
{-# INLINABLE delete #-}
delete :: Ord p => Key -> IntPSQ p v -> IntPSQ p v
delete k = go
  where
    go t = case t of
        Nil           -> Nil

        Tip k' _ _
          | k == k'   -> Nil
          | otherwise -> t

        Bin k' p' x' m l r
          | nomatch k k' m -> t
          | k == k'        -> merge m l r
          | zero k m       -> binShrinkL k' p' x' m (go l) r
          | otherwise      -> binShrinkR k' p' x' m l      (go r)

-- | /O(min(n,W))/ Update a priority at a specific key with the result
-- of the provided function. When the key is not a member of the
-- queue, the original queue is returned.
adjust :: Ord p => (p -> p) -> Key -> IntPSQ p v -> IntPSQ p v
adjust f = \k t0 -> case deleteView k t0 of
    Nothing        -> t0
    Just (p, v, t) -> unsafeInsertNew k (f p) v t

-- | /O(min(n,W))/ A variant of 'alter' which works on the element with the
-- minimum priority. Unlike 'alter', this variant also allows you to change the
-- key of the element.
{-# INLINE alterMin #-}
alterMin :: Ord p
         => (Maybe (Key, p, v) -> (b, Maybe (Key, p, v)))
         -> IntPSQ p v
         -> (b, IntPSQ p v)
alterMin f t = case t of
    Nil             -> case f Nothing of
                         (b, Nothing)           -> (b, Nil)
                         (b, Just (k', p', x')) -> (b, Tip k' p' x')

    Tip k p x       -> case f (Just (k, p, x)) of
                         (b, Nothing)           -> (b, Nil)
                         (b, Just (k', p', x')) -> (b, Tip k' p' x')

    Bin k p x m l r -> case f (Just (k, p, x)) of
                         (b, Nothing)           -> (b, merge m l r)
                         (b, Just (k', p', x'))
                           | k  /= k'  -> (b, insert k' p' x' (merge m l r))
                           | p' <= p   -> (b, Bin k p' x' m l r)
                           | otherwise -> (b, unsafeInsertNew k p' x' (merge m l r))

-- | Smart constructor for a 'Bin' node whose left subtree could have become
-- 'Nil'.
{-# INLINE binShrinkL #-}
binShrinkL :: Key -> p -> v -> Mask -> IntPSQ p v -> IntPSQ p v -> IntPSQ p v
binShrinkL k p x m Nil r = case r of Nil -> Tip k p x; _ -> Bin k p x m Nil r
binShrinkL k p x m l   r = Bin k p x m l r

-- | Smart constructor for a 'Bin' node whose right subtree could have become
-- 'Nil'.
{-# INLINE binShrinkR #-}
binShrinkR :: Key -> p -> v -> Mask -> IntPSQ p v -> IntPSQ p v -> IntPSQ p v
binShrinkR k p x m l Nil = case l of Nil -> Tip k p x; _ -> Bin k p x m l Nil
binShrinkR k p x m l r   = Bin k p x m l r


------------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------------

-- | /O(n*min(n,W))/ Build a queue from a list of (key, priority, value) tuples.
-- If the list contains more than one priority and value for the same key, the
-- last priority and value for the key is retained.
{-# INLINABLE fromList #-}
fromList :: Ord p => [(Key, p, v)] -> IntPSQ p v
fromList = go empty
  where
    go !im []               = im
    go !im ((k, p, x) : zs) = go (insert k p x im) zs

-- | /O(n)/ Convert a queue to a list of (key, priority, value) tuples. The
-- order of the list is not specified.
toList :: IntPSQ p v -> [(Key, p, v)]
toList =
    go []
  where
    go acc Nil                   = acc
    go acc (Tip k' p' x')        = (k', p', x') : acc
    go acc (Bin k' p' x' _m l r) = (k', p', x') : go (go acc r) l

-- | /O(n)/ Obtain the list of present keys in the queue.
keys :: IntPSQ p v -> [Key]
keys t = [k | (k, _, _) <- toList t]
-- TODO (jaspervdj): More efficient implementations possible

-- | /O(n)/ Return a list of elements whose priorities are at most @p@.
atMost :: Ord p => p -> IntPSQ p v -> ([(Key, p, v)], IntPSQ p v)
atMost pMost = go []
  where
    go acc t = case minView t of
        Nothing          -> (acc, t)
        Just (k, p, v, t')
            | p <= pMost -> go ((k, p, v) : acc) t'
            | otherwise  -> (acc, t)


------------------------------------------------------------------------------
-- Views
------------------------------------------------------------------------------

-- | /O(min(n,W))/ Insert a new key, priority and value in the queue. If the key
-- is already present in the queue, then the evicted priority and value can be
-- found the first element of the returned tuple.
insertView :: Ord p => Key -> p -> v -> IntPSQ p v -> (Maybe (p, v), IntPSQ p v)
insertView k p x t0 = case deleteView k t0 of
    Nothing          -> (Nothing,       unsafeInsertNew k p x t0)
    Just (p', v', t) -> (Just (p', v'), unsafeInsertNew k p x t)

-- | /O(min(n,W))/ Delete a key and its priority and value from the queue. If
-- the key was present, the associated priority and value are returned in
-- addition to the updated queue.
{-# INLINABLE deleteView #-}
deleteView :: Ord p => Key -> IntPSQ p v -> Maybe (p, v, IntPSQ p v)
deleteView k t0 =
    case delFrom t0 of
      (# _, Nothing     #) -> Nothing
      (# t, Just (p, x) #) -> Just (p, x, t)
  where
    delFrom t = case t of
      Nil -> (# Nil, Nothing #)

      Tip k' p' x'
        | k == k'   -> (# Nil, Just (p', x') #)
        | otherwise -> (# t,   Nothing       #)

      Bin k' p' x' m l r
        | nomatch k k' m -> (# t, Nothing #)
        | k == k'   -> let t' = merge m l r
                       in  t' `seq` (# t', Just (p', x') #)

        | zero k m  -> case delFrom l of
                         (# l', mbPX #) -> let t' = binShrinkL k' p' x' m l' r
                                           in  t' `seq` (# t', mbPX #)

        | otherwise -> case delFrom r of
                         (# r', mbPX #) -> let t' = binShrinkR k' p' x' m l  r'
                                           in  t' `seq` (# t', mbPX #)

-- | /O(min(n,W))/ Retrieve the binding with the least priority, and the
-- rest of the queue stripped of that binding.
{-# INLINE minView #-}
minView :: Ord p => IntPSQ p v -> Maybe (Key, p, v, IntPSQ p v)
minView t = case t of
    Nil             -> Nothing
    Tip k p x       -> Just (k, p, x, Nil)
    Bin k p x m l r -> Just (k, p, x, merge m l r)


------------------------------------------------------------------------------
-- Traversal
------------------------------------------------------------------------------

-- | /O(n)/ Modify every value in the queue.
{-# INLINABLE map #-}
map :: (Key -> p -> v -> w) -> IntPSQ p v -> IntPSQ p w
map f =
    go
  where
    go t = case t of
        Nil             -> Nil
        Tip k p x       -> Tip k p (f k p x)
        Bin k p x m l r -> Bin k p (f k p x) m (go l) (go r)

-- | /O(n)/ Strict fold over every key, priority and value in the map. The order
-- in which the fold is performed is not specified.
{-# INLINABLE fold' #-}
fold' :: (Key -> p -> v -> a -> a) -> a -> IntPSQ p v -> a
fold' f = go
  where
    go !acc Nil                   = acc
    go !acc (Tip k' p' x')        = f k' p' x' acc
    go !acc (Bin k' p' x' _m l r) =
        let !acc1 = f k' p' x' acc
            !acc2 = go acc1 l
            !acc3 = go acc2 r
        in acc3


-- | Internal function that merges two *disjoint* 'IntPSQ's that share the
-- same prefix mask.
{-# INLINABLE merge #-}
merge :: Ord p => Mask -> IntPSQ p v -> IntPSQ p v -> IntPSQ p v
merge m l r = case l of
    Nil -> r

    Tip lk lp lx ->
      case r of
        Nil                     -> l
        Tip rk rp rx
          | (lp, lk) < (rp, rk) -> Bin lk lp lx m Nil r
          | otherwise           -> Bin rk rp rx m l   Nil
        Bin rk rp rx rm rl rr
          | (lp, lk) < (rp, rk) -> Bin lk lp lx m Nil r
          | otherwise           -> Bin rk rp rx m l   (merge rm rl rr)

    Bin lk lp lx lm ll lr ->
      case r of
        Nil                     -> l
        Tip rk rp rx
          | (lp, lk) < (rp, rk) -> Bin lk lp lx m (merge lm ll lr) r
          | otherwise           -> Bin rk rp rx m l                Nil
        Bin rk rp rx rm rl rr
          | (lp, lk) < (rp, rk) -> Bin lk lp lx m (merge lm ll lr) r
          | otherwise           -> Bin rk rp rx m l                (merge rm rl rr)


------------------------------------------------------------------------------
-- Improved insert performance for special cases
------------------------------------------------------------------------------

-- TODO (SM): Make benchmarks run again, integrate this function with insert
-- and test how benchmarks times change.

-- | Internal function to insert a key with priority larger than the
-- maximal priority in the heap. This is always the case when using the PSQ
-- as the basis to implement a LRU cache, which associates a
-- access-tick-number with every element.
{-# INLINE unsafeInsertIncreasePriority #-}
unsafeInsertIncreasePriority
    :: Ord p => Key -> p -> v -> IntPSQ p v -> IntPSQ p v
unsafeInsertIncreasePriority =
    unsafeInsertWithIncreasePriority (\newP newX _ _ -> (newP, newX))

{-# INLINE unsafeInsertIncreasePriorityView #-}
unsafeInsertIncreasePriorityView
    :: Ord p => Key -> p -> v -> IntPSQ p v -> (Maybe (p, v), IntPSQ p v)
unsafeInsertIncreasePriorityView =
    unsafeInsertWithIncreasePriorityView (\newP newX _ _ -> (newP, newX))

-- | This name is not chosen well anymore. This function:
--
-- - Either inserts a value at a new key with a prio higher than the max of the
--   entire PSQ.
-- - Or, overrides the value at the key with a prio strictly higher than the
--   original prio at that key (but not necessarily the max of the entire PSQ).
{-# INLINABLE unsafeInsertWithIncreasePriority #-}
unsafeInsertWithIncreasePriority
    :: Ord p
    => (p -> v -> p -> v -> (p, v))
    -> Key -> p -> v -> IntPSQ p v -> IntPSQ p v
unsafeInsertWithIncreasePriority f k p x t0 =
    -- TODO (jaspervdj): Maybe help inliner a bit here, check core.
    go t0
  where
    go t = case t of
        Nil -> Tip k p x

        Tip k' p' x'
            | k == k'   -> case f p x p' x' of (!fp, !fx) -> Tip k fp fx
            | otherwise -> link k' p' x' k  (Tip k p x) Nil

        Bin k' p' x' m l r
            | nomatch k k' m -> link k' p' x' k (Tip k p x) (merge m l r)
            | k == k'        -> case f p x p' x' of
                (!fp, !fx)
                    | zero k m  -> merge m (unsafeInsertNew k fp fx l) r
                    | otherwise -> merge m l (unsafeInsertNew k fp fx r)
            | zero k m       -> Bin k' p' x' m (go l) r
            | otherwise      -> Bin k' p' x' m l      (go r)

{-# INLINABLE unsafeInsertWithIncreasePriorityView #-}
unsafeInsertWithIncreasePriorityView
    :: Ord p
    => (p -> v -> p -> v -> (p, v))
    -> Key -> p -> v -> IntPSQ p v -> (Maybe (p, v), IntPSQ p v)
unsafeInsertWithIncreasePriorityView f k p x t0 =
    -- TODO (jaspervdj): Maybe help inliner a bit here, check core.
    case go t0 of
        (# t, mbPX #) -> (mbPX, t)
  where
    go t = case t of
        Nil -> (# Tip k p x, Nothing #)

        Tip k' p' x'
            | k == k'   -> case f p x p' x' of
                (!fp, !fx) -> (# Tip k fp fx, Just (p', x') #)
            | otherwise -> (# link k' p' x' k  (Tip k p x) Nil, Nothing #)

        Bin k' p' x' m l r
            | nomatch k k' m ->
                let t' = merge m l r
                in t' `seq`
                    let t'' = link k' p' x' k (Tip k p x) t'
                    in t'' `seq` (# t'', Nothing #)

            | k == k' -> case f p x p' x' of
                (!fp, !fx)
                    | zero k m  ->
                        let t' = merge m (unsafeInsertNew k fp fx l) r
                        in t' `seq` (# t', Just (p', x') #)
                    | otherwise ->
                        let t' = merge m l (unsafeInsertNew k fp fx r)
                        in t' `seq` (# t', Just (p', x') #)

            | zero k m -> case go l of
                (# l', mbPX #) -> l' `seq` (# Bin k' p' x' m l' r, mbPX #)

            | otherwise -> case go r of
                (# r', mbPX #) -> r' `seq` (# Bin k' p' x' m l r', mbPX #)

-- | This can NOT be used to delete elements.
{-# INLINABLE unsafeLookupIncreasePriority #-}
unsafeLookupIncreasePriority
    :: Ord p
    => (p -> v -> (Maybe b, p, v))
    -> Key
    -> IntPSQ p v
    -> (Maybe b, IntPSQ p v)
unsafeLookupIncreasePriority f k t0 =
    -- TODO (jaspervdj): Maybe help inliner a bit here, check core.
    case go t0 of
        (# t, mbB #) -> (mbB, t)
  where
    go t = case t of
        Nil -> (# Nil, Nothing #)

        Tip k' p' x'
            | k == k'   -> case f p' x' of
                (!fb, !fp, !fx) -> (# Tip k fp fx, fb #)
            | otherwise -> (# t, Nothing #)

        Bin k' p' x' m l r
            | nomatch k k' m -> (# t, Nothing #)

            | k == k' -> case f p' x' of
                (!fb, !fp, !fx)
                    | zero k m  ->
                        let t' = merge m (unsafeInsertNew k fp fx l) r
                        in t' `seq` (# t', fb #)
                    | otherwise ->
                        let t' = merge m l (unsafeInsertNew k fp fx r)
                        in t' `seq` (# t', fb #)

            | zero k m -> case go l of
                (# l', mbB #) -> l' `seq` (# Bin k' p' x' m l' r, mbB #)

            | otherwise -> case go r of
                (# r', mbB #) -> r' `seq` (# Bin k' p' x' m l r', mbB #)
