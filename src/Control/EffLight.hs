-- almost direct copy from https://okmij.org/ftp/Haskell/extensible/Eff1.hs
-- minor name changes for preference
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Control.EffLight (Comp(..), send, handle_relay, done, qApp, qComp, comp, run, handle_relay_s) where
import Data.FTCQueue
import Type.OpenUnion
import GHC.Exts (inline)

type Arr r a b = a -> Comp r b
type Arrs r a b = FTCQueue (Comp r) a b

data Comp r a
  = Done !a
  | forall b. Req !(Union r b) !(Arrs r b a)

comp :: Arr r a b -> Arrs r a b
comp f = tsingleton f

-- passing a value INTO a computation
{-# INLINABLE qApp #-}
qApp :: Arrs r b w -> b -> Comp r w
qApp q x =
   case inline tviewl q of
   TOne k  -> k x
   k :| t -> case k x of
     Done y -> qApp t y
     Req u k' -> Req u (k' >< t)

-- Compose effectful arrows (and possibly change the effect!)
{-# INLINE qComp #-}
qComp :: Arrs r a b -> (Comp r b -> Comp r' c) -> Arr r' a c
qComp g h = \a -> h $ qApp g a

instance Functor (Comp e) where
  {-# INLINE fmap #-}
  fmap f (Done v) = Done $ f v
  fmap f (Req r k) = Req r $ k |> (Done . f)

instance Applicative (Comp e) where
  {-# INLINE pure #-}
  pure = Done
  Done a <*> b = fmap a b
  Req ar ak <*> b = Req ar $ ak |> (`fmap` b)

instance Monad (Comp e) where  
  {-# INLINE [2] (>>=) #-}
  Done a >>= b = b a
  Req ar ak >>= b = Req ar $ ak |> b

done :: a -> Comp e a
done = Done

-- send a request and wait for a reply
{-# INLINE [2] send #-}
send :: Member t r => t v -> Comp r v
send t = Req (inj t) (tsingleton Done)
-- This seems to be a very beneficial rule! On micro-benchmarks, cuts
-- the needed memory in half and speeds up almost twice.
{-# RULES
  "send/bind" [~3] forall t k. send t >>= k = Req (inj t) (tsingleton k)
#-}


{-# INLINE handle_relay #-}
handle_relay ::
  (Decomp r) =>
  (a -> Comp r w) ->
  (forall v. t v -> Arr r v w -> Comp r w) ->
  Comp (t ': r) a -> Comp r w
handle_relay ret h m = loop m
 where
  loop (Done x) = ret x
  loop (Req u q) = case decomp u of
    Right x -> h x k
    Left u' -> Req u' (tsingleton k)
   where k = qComp q loop


{-# INLINE handle_relay_s #-}
handle_relay_s ::
  (Decomp r) =>
  s ->
  (s -> a -> Comp r w) ->
  (forall v. s -> t v -> (s -> Arr r v w) -> Comp r w) ->
  Comp (t ': r) a -> Comp r w
handle_relay_s s0 ret h m = loop s0 m
 where
  loop s (Done x) = ret s x
  loop s (Req u q) = case decomp u of
    Right x -> h s x k
    Left u' -> Req u' (tsingleton (k s))
   where k s' x = loop s' $ qApp q x
    

-- ------------------------------------------------------------------------
-- The initial case, no effects

-- The type of run ensures that all effects must be handled:
-- only pure computations may be run.
run :: Comp '[] w -> w
run (Done x) = x
run _ = undefined
-- the other case is unreachable since Union [] a cannot be
-- constructed.
-- Therefore, run is a total function if its argument terminates.
