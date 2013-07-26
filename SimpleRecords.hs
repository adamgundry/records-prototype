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
             NoMonomorphismRestriction, TypeOperators #-}

module SimpleRecords where

import Control.Applicative
import GHC.TypeLits


-- These class and type family declarations, the instance declaration
-- for SimpleAccessor (->) and the definition of `field` go in base:

type family GetResult (r :: *) (f :: Symbol) :: *
class t ~ GetResult r f => Get r (f :: Symbol) t where
  getFld :: proxy f -> r -> t
  setFld :: proxy f -> r -> t -> r

class SimpleAccessor (p :: * -> * -> *) where
  simpleAccessor :: (r -> t) -> (r -> t -> r) -> p r t

instance SimpleAccessor (->) where
  simpleAccessor getter setter = getter


field :: (Get r f t, SimpleAccessor p) => proxy f -> p r t
field z = simpleAccessor (getFld z) (setFld z)


-- Some example datatypes...

data R a = MkR { _foo :: a -> a }
data S   = MkS { _bar :: forall b. b -> b }
data T a = MkT { _x :: [a] }
data U a = MkU { _foo' :: R a, _bar' :: a }
data V   = MkV { _foo'' :: Int }

-- ...lead to automatic generation of the following instances...

type instance GetResult (R a) "foo" = a -> a
instance t ~ (a -> a) => Get (R a) "foo" t where
  getFld _ (MkR x) = x
  setFld _ (MkR _) x = MkR x

type instance GetResult (T a) "x" = [a]
instance (b ~ GetResult (T a) "x") => Get (T a) "x" b where
  getFld _ (MkT x) = x
  setFld _ (MkT _) y = MkT y

type instance GetResult (U a) "foo" = R a
instance t ~ R a => Get (U a) "foo" t where
  getFld _ (MkU x _) = x
  setFld _ (MkU _ y) x = MkU x y

type instance GetResult (U a) "bar" = a
instance t ~ a => Get (U a) "bar" t where
  getFld _ (MkU _ y) = y
  setFld _ (MkU x _) y = MkU x y

type instance GetResult V "foo" = Int
instance t ~ Int => Get V "foo" t where
  getFld _ (MkV x) = x
  setFld _ (MkV _) x = MkV x


-- Note that there are no instances for bar from S, because it is
-- higher rank, so it cannot be overloaded.


-- These function declarations approximate how uses of the fields
-- would be handled by the typechecker:

foo :: (Get r "foo" t, SimpleAccessor p) => p r t
foo = field (Proxy :: Proxy "foo")

bar :: (Get r "bar" t, SimpleAccessor p) => p r t
bar = field (Proxy :: Proxy "bar")

x :: (Get r "x" t, SimpleAccessor p) => p r t
x = field (Proxy :: Proxy "x")

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

foo_is_a_lens :: Get r "foo" t => Lens r r t t
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
