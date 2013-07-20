{-
  The following is a prototype implementation of the plan for
  overloaded record fields in GHC, described at

  http://ghc.haskell.org/trac/ghc/wiki/Records/OverloadedRecordFields/Plan
-}

{-# LANGUAGE KindSignatures, DataKinds, MultiParamTypeClasses,
             TypeFamilies, RankNTypes, FlexibleInstances, 
             UndecidableInstances, PolyKinds, FlexibleContexts,
             NoMonomorphismRestriction #-}

module RecordsPrototype where

import Control.Applicative
import GHC.TypeLits


-- These class and type family declarations, the instance declaration
-- for Accessor (->) and the definition of `field` go in base:

type family GetResult (r :: *) (f :: Symbol) :: *
class t ~ GetResult r f => Get r (f :: Symbol) t where
  getFld :: proxy f -> r -> t

type family SetResult (r :: *) (f :: Symbol) (a :: *) :: *  
class Set (r :: *) (f :: Symbol) (a :: *) where
  setFld :: proxy f -> r -> a -> SetResult r f a


class Accessor (p :: * -> * -> *) (f :: Symbol) where
  accessor :: proxy f -> (r -> GetResult r f) ->
              (forall a . Set r f a => r -> a -> SetResult r f a) ->
              p r (GetResult r f)

instance Accessor (->) f where
  accessor _ getter setter = getter


field :: (Get r f t, Accessor p f) => proxy f -> p r t
field z = accessor z (getFld z) (setFld z)


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

type instance SetResult (R a) "foo" (b -> b) = R b
instance (b' ~ (b -> b)) => Set (R a) "foo" b' where
  setFld _ (MkR _) x = MkR x

type instance GetResult (T a) "x" = [a]
instance (b ~ GetResult (T a) "x") => Get (T a) "x" b where
  getFld _ (MkT x) = x

type instance SetResult (T a) "x" [c] = T c
instance (b ~ [c]) => Set (T a) "x" b where
  setFld _ (MkT _) y = MkT y

type instance GetResult (U a) "foo" = R a
instance t ~ R a => Get (U a) "foo" t where
  getFld _ (MkU x _) = x

type instance SetResult (U a) "foo" (R c) = U c
instance b ~ R a => Set (U a) "foo" b where
  setFld _ (MkU _ y) x = MkU x y

type instance GetResult (U a) "bar" = a
instance t ~ a => Get (U a) "bar" t where
  getFld _ (MkU _ y) = y

type instance SetResult (U a) "bar" c = U c
instance t ~ a => Set (U a) "bar" t where
  setFld _ (MkU x _) y = MkU x y

type instance GetResult V "foo" = Int
instance t ~ Int => Get V "foo" t where
  getFld _ (MkV x) = x

type instance SetResult V "foo" Int = V
instance a ~ Int => Set V "foo" a where
  setFld _ (MkV _) x = MkV x


-- Note that:
--  * there are no instances for bar from S, because it is higher rank
--  * the Set instances for U do not support type-changing update


-- These function declarations approximate how uses of the fields
-- would be handled by the typechecker:

foo :: (Get r "foo" t, Accessor p "foo") => p r t
foo = field (Proxy :: Proxy "foo")

bar :: (Get r "bar" t, Accessor p "bar") => p r t
bar = field (Proxy :: Proxy "bar")

x :: (Get r "x" t, Accessor p "x") => p r t
x = field (Proxy :: Proxy "x")

-- We can compose polymorphic fields:

fooBar = foo . bar


-- Using a newtype wrapper, we can turn any field into a lens by
-- applying the `fieldLens` function.  Everything from here onwards
-- can go in libraries other than base.

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

newtype WrapLens f r a
  = MkWrapLens (forall b . Set r f b => Lens r (SetResult r f b) a b)

instance f ~ g => Accessor (WrapLens f) g where
  accessor _ getter setter = MkWrapLens (\ w s -> setter s <$> w (getter s))

fieldLens :: Set r f b => WrapLens f r a -> Lens r (SetResult r f b) a b
fieldLens (MkWrapLens l) = l


foo_is_a_lens :: (Get r "foo" t, Set r "foo" b) =>
                 Lens r (SetResult r "foo" b) t b
foo_is_a_lens = fieldLens foo


-- Just for good measure, here's another style of lens that can also
-- be an Accessor:

data DataLens f r a = DataLens
    { getDL :: r -> a
    , setDL :: forall b . Set r f b => r -> b -> SetResult r f b }

instance f ~ g => Accessor (DataLens f) g where
  accessor _ = DataLens


-- Oh, I almost forgot, we need proxy types until explicit type
-- application is sorted:

data Proxy k = Proxy
