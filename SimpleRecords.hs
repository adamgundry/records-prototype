{-
  The following is a prototype implementation of the plan for
  overloaded record fields in GHC, described at

  http://ghc.haskell.org/trac/ghc/wiki/Records/OverloadedRecordFields/Plan

  This version integrates with lenses, but does not support
  type-changing update.
-}

{-# LANGUAGE KindSignatures, DataKinds, MultiParamTypeClasses,
             TypeFamilies, RankNTypes, FlexibleInstances, 
             UndecidableInstances, PolyKinds, FlexibleContexts,
             NoMonomorphismRestriction, TypeOperators, GADTs #-}

module SimpleRecords where

import Control.Applicative
import GHC.TypeLits


-- These class and type family declarations, the instance declaration
-- for SimpleAccessor (->) and the definition of `field` go in base:

type family GetResult (r :: *) (f :: Symbol) :: *

class t ~ GetResult r f => Has r (f :: Symbol) t where
  getField :: proxy f -> r -> t
  setField :: proxy f -> r -> t -> r

class SimpleAccessor (p :: * -> * -> *) where
  simpleAccessor :: (r -> t) -> (r -> t -> r) -> p r t

instance SimpleAccessor (->) where
  simpleAccessor getter setter = getter


field :: (Has r f t, SimpleAccessor p) => proxy f -> p r t
field z = simpleAccessor (getField z) (setField z)


-- Some example datatypes...

data R a = MkR { _foo :: a -> a }
data S   = MkS { _bar :: forall b. b -> b }
data T a = MkT { _x :: [a] }
data U a = MkU { _foo' :: R a, _bar' :: a }
data V k = MkV { _foo'' :: Int, _bar'' :: k Int }
data W a where
    MkW :: (a ~ b, Ord a) => { gaa :: a, gab :: b } -> W (a, b)

-- ...lead to automatic generation of the following instances...

type instance GetResult (R a) "foo" = a -> a
instance t ~ (a -> a) => Has (R a) "foo" t where
  getField _ (MkR x) = x
  setField _ (MkR _) x = MkR x

type instance GetResult (T a) "x" = [a]
instance (b ~ [a]) => Has (T a) "x" b where
  getField _ (MkT x) = x
  setField _ (MkT _) y = MkT y

type instance GetResult (U a) "foo" = R a
instance t ~ R a => Has (U a) "foo" t where
  getField _ (MkU x _) = x
  setField _ (MkU _ y) x = MkU x y

type instance GetResult (U a) "bar" = a
instance t ~ a => Has (U a) "bar" t where
  getField _ (MkU _ y) = y
  setField _ (MkU x _) y = MkU x y

type instance GetResult (V k) "foo" = Int
instance t ~ Int => Has (V k) "foo" t where
  getField _ (MkV x _) = x
  setField _ (MkV _ y) x = MkV x y

type instance GetResult (V k) "bar" = k Int
instance t ~ k Int => Has (V k) "bar" t where
  getField _ (MkV _ y) = y
  setField _ (MkV x _) y = MkV x y

type instance GetResult (W (a, b)) "gaa" = a
instance t ~ a => Has (W (a, b)) "gaa" t where
  getField _ (MkW gaa _)   = gaa
  setField _ (MkW _ gab) gaa = MkW gaa gab

type instance GetResult (W (a, b)) "gab" = b
instance (t ~ b, c ~ (a, b)) => Has (W c) "gab" t where
  getField _ (MkW _ gab) = gab
  setField _ (MkW gaa _) gab = MkW gaa gab


-- Note that there are no instances for bar from S, because it is
-- higher rank, so it cannot be overloaded.


-- These function declarations approximate how uses of the fields
-- would be handled by the typechecker:

foo :: (Has r "foo" t, SimpleAccessor p) => p r t
foo = field (Proxy :: Proxy "foo")

bar :: (Has r "bar" t, SimpleAccessor p) => p r t
bar = field (Proxy :: Proxy "bar")

x :: (Has r "x" t, SimpleAccessor p) => p r t
x = field (Proxy :: Proxy "x")


-- We can use fields:

t = foo (MkR not) False

-- We can compose polymorphic fields:

fooBar = foo . bar


-- Using a newtype wrapper, we can turn any field into a simple lens
-- by applying the `fieldSimpleLens` function.  Everything from here
-- onwards can go in libraries other than base.

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

newtype SimpleLens r a = MkSimpleLens (Lens r r a a)

instance SimpleAccessor SimpleLens where
  simpleAccessor getter setter =
    MkSimpleLens (\ w s -> setter s <$> w (getter s))

fieldSimpleLens :: SimpleLens r a -> Lens r r a a
fieldSimpleLens (MkSimpleLens l) = l

foo_is_a_lens :: Has r "foo" t => Lens r r t t
foo_is_a_lens = fieldSimpleLens foo



-- data-lens (ish)

data DataLens r a = DataLens
   { getDL :: r -> a
   , setDL :: r -> a -> r }

instance SimpleAccessor DataLens where
  simpleAccessor = DataLens


-- fclabels

data Point arr f i o = Point
  { _get :: f `arr` o
  , _set :: (i, f) `arr` f
  }

newtype FCLens arr f a = FCLens { unLens :: Point arr f a a }

instance SimpleAccessor (FCLens (->)) where
  simpleAccessor getter setter =
      FCLens (Point getter (uncurry $ flip setter))


-- data-accessor

newtype DataAccessor r a = Cons {decons :: r -> (a, a -> r)}

instance SimpleAccessor DataAccessor where
  simpleAccessor getter setter = Cons (\ r -> (getter r, setter r))


-- Oh, I almost forgot, we need proxy types until explicit type
-- application is sorted:

data Proxy k = Proxy
