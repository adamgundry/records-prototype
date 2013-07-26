{-
  The following is a prototype implementation of the plan for
  overloaded record fields in GHC, described at

  http://ghc.haskell.org/trac/ghc/wiki/Records/OverloadedRecordFields/Plan

  This version does not support lens integration.
-}

{-# LANGUAGE KindSignatures, DataKinds, MultiParamTypeClasses,
             TypeFamilies, RankNTypes, FlexibleInstances, 
             UndecidableInstances, PolyKinds, FlexibleContexts,
             NoMonomorphismRestriction, TypeOperators #-}

module TrivialRecords where

import Control.Applicative
import GHC.TypeLits


-- These class and type family declarations go in base:

type family GetResult (r :: *) (f :: Symbol) :: *
class t ~ GetResult r f => Get r (f :: Symbol) t where
  getFld :: proxy f -> r -> t


-- Some example datatypes...

data R a = MkR { _foo :: a -> a }
data S   = MkS { _bar :: forall b. b -> b }
data T a = MkT { _x :: [a] }
data U a = MkU { _foo' :: R a, _bar' :: a }
data V k = MkV { _foo'' :: Int, _bar'' :: k Int }

-- ...lead to automatic generation of the following instances...

type instance GetResult (R a) "foo" = a -> a
instance t ~ (a -> a) => Get (R a) "foo" t where
  getFld _ (MkR x) = x

type instance GetResult (T a) "x" = [a]
instance (b ~ [a]) => Get (T a) "x" b where
  getFld _ (MkT x) = x

type instance GetResult (U a) "foo" = R a
instance t ~ R a => Get (U a) "foo" t where
  getFld _ (MkU x _) = x

type instance GetResult (U a) "bar" = a
instance t ~ a => Get (U a) "bar" t where
  getFld _ (MkU _ y) = y

type instance GetResult (V k) "foo" = Int
instance t ~ Int => Get (V k) "foo" t where
  getFld _ (MkV x _) = x

type instance GetResult (V k) "bar" = k Int
instance t ~ k Int => Get (V k) "bar" t where
  getFld _ (MkV _ y) = y


-- Note that there are no instances for bar from S, because it is
-- higher rank, so it cannot be overloaded.


-- These function declarations approximate how uses of the fields
-- would be handled by the typechecker:

foo :: Get r "foo" t => r -> t
foo = getFld (Proxy :: Proxy "foo")

bar :: Get r "bar" t => r -> t
bar = getFld (Proxy :: Proxy "bar")

x :: Get r "x" t => r -> t
x = getFld (Proxy :: Proxy "x")

-- We can compose polymorphic fields:

fooBar = foo . bar



-- Oh, I almost forgot, we need proxy types until explicit type
-- application is sorted:

data Proxy k = Proxy
