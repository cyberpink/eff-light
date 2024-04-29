-- https://okmij.org/ftp/Haskell/extensible/OpenUnion53.hs
{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies, TypeOperators                           #-}

-- Only for MemberU below, when emulating Monad Transformers
{-# LANGUAGE FunctionalDependencies, UndecidableInstances #-}

-- Open unions (type-indexed co-products) for extensible effects
-- All operations are constant-time, and there is no Typeable constraint

-- This is a variation of OpenUion5.hs, which relies on overlapping
-- instances instead of closed type families. Closed type families
-- have their problems: overlapping instances can resolve even
-- for unground types, but closed type families are subject to a
-- strict apartness condition.

-- This implementation is very similar to OpenUnion1.hs, but without
-- the annoying Typeable constraint. We sort of emulate it:

-- Our list r of open union components is a small Universe.
-- Therefore, we can use the Typeable-like evidence in that
-- universe. We hence can define
--
-- data Union r v where
--  Union :: t v -> TRep t r -> Union r v -- t is existential
-- where
-- data TRep t r where
--  T0 :: TRep t (t ': r)
--  TS :: TRep t r -> TRep (any ': r)
-- Then Member is a type class that produces TRep
-- Taken literally it doesn't seem much better than
-- OpenUinion41.hs. However, we can cheat and use the index of the
-- type t in the list r as the TRep. (We will need UnsafeCoerce then).

-- The interface is the same as of other OpenUnion*.hs
module Type.OpenUnion (Union, inj, prj, Decomp(..),
                   Member, MemberU2, -- weaken
                  ) where

import Unsafe.Coerce (unsafeCoerce)
import Data.Kind (Type)

-- The data constructors of Union are not exported

-- Strong Sum (Existential with the evidence) is an open union
-- t is can be a GADT and hence not necessarily a Functor.
-- Int is the index of t in the list r; that is, the index of t in the
-- universe r

data family Union (r :: [ Type -> Type ]) (v :: Type)

-- data instance Union '[] _ = UnionEmpty
newtype instance Union (t ': '[]) v = UnionSingle (t v)
data instance  Union (t1 ': t2 ': t3) v where
  Union :: {-# UNPACK #-} !Int -> t v -> Union (t1 ': t2 ': t3) v

{-# INLINE prj' #-}
{-# INLINE inj' #-}
inj' :: Int -> t v -> Union (t1 ': t2 ': t3) v
inj' = Union

prj' :: Int -> Union (t1 ': t2 ': t3) v -> Maybe (t v)
prj' n (Union n' x) | n == n'   = Just (unsafeCoerce x)
                    | otherwise = Nothing

newtype P t r = P{unP :: Int}

class Member (t :: Type -> Type) r where
  inj :: t v -> Union r v
  prj :: Union r v -> Maybe (t v)

-- Optimized specialized instance
-- Explicit type-level equality condition is a dirty
-- hack to eliminate the type annotation in the trivial case,
-- such as @run (runReader get ())@.
--
-- There is no ambiguity when finding instances for
-- @Member t (a ': b ': r)@, which the second instance is selected.
--
-- The only case we have to concerned about is  @Member t '[s]@.
-- But, in this case, values of definition is the same (if present),
-- and the first one is chosen according to GHC User Manual, since
-- the latter one is incoherent. This is the optimal choice.
{-
instance {-# OVERLAPPING #-} t ~ s => Member t '[s] where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj x           = Union 0 x
  prj (Union _ x) = Just (unsafeCoerce x)
-}

instance Member t (t ': '[]) where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj = UnionSingle
  prj (UnionSingle x) = Just x

instance (FindElem t (t1 ': t2 ': t3)) => Member t (t1 ': t2 ': t3) where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj = inj' (unP $ (elemNo :: P t (t1 ': t2 ': t3)))
  prj = prj' (unP $ (elemNo :: P t (t1 ': t2 ': t3)))


class Decomp (r :: [ Type -> Type ]) where
  decomp :: Union (t ': r) v -> Either (Union r v) (t v)

instance Decomp '[] where
  {-# INLINE decomp #-}
  decomp (UnionSingle x) = Right x

instance Decomp (t1 ': '[]) where
  {-# INLINE decomp #-}
  decomp (Union 0 v) = Right $ unsafeCoerce v
  decomp (Union _ v) = Left  $ UnionSingle (unsafeCoerce v)

instance Decomp (t1 ': t2 ': t3) where
  {-# INLINE decomp #-}
  decomp (Union 0 v) = Right $ unsafeCoerce v
  decomp (Union n v) = Left  $ Union (n-1) v

-- weaken :: Union (t1 ': t2) w -> Union (any ': t1 ': t2) w
-- weaken (Union n v) = Union (n+1) v

-- Find an index of an element in a `list'
-- The element must exist
-- This is essentially a compile-time computation.
class FindElem (t :: Type -> Type) r where
  elemNo :: P t r

-- Stopped Using Obsolete -XOverlappingInstances
-- and explicitly specify to choose the topmost
-- one for multiple occurence, which is the same
-- behaviour as OpenUnion51 with GHC 7.10.
-- instance {-# OVERLAPPING #-} t ~ s => FindElem t '[s] where
--   elemNo = P 0


instance {-# INCOHERENT  #-} t ~ s => FindElem t '[s] where
  elemNo = P 0

-- Remove the {-# INCOHERENT #-} below when using the latest GHC...
instance {-# INCOHERENT #-} FindElem t (t ': r) where
  elemNo = P 0

instance {-# OVERLAPPABLE #-} FindElem t r => FindElem t (t' ': r) where
  elemNo = P $ 1 + (unP $ (elemNo :: P t r))

type family EQU (a :: k) (b :: k) :: Bool where
  EQU a a = True
  EQU a b = False

-- This class is used for emulating monad transformers
class Member t r => MemberU2 (tag :: k -> Type -> Type) (t :: Type -> Type) r | tag r -> t
instance (Member t1 (t2 ': r), MemberU' (EQU t1 t2) tag t1 (t2 ': r)) =>
   MemberU2 tag t1 (t2 ': r)

class Member t r =>
      MemberU' (f::Bool) (tag :: k -> Type -> Type) (t :: Type -> Type) r | tag r -> t
instance (Member (tag e) (tag e : r)) => MemberU' True tag (tag e) (tag e ': r)
instance (Member t (t' ': r), MemberU2 tag t r) =>
           MemberU' False tag t (t' ': r)

