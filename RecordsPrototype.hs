{-
  The following is a prototype implementation of the plan for
  overloaded record fields in GHC, described at

  http://ghc.haskell.org/trac/ghc/wiki/Records/OverloadedRecordFields/Plan

  This is the full version, which supports integration with
  type-changing lenses.
-}

{-# LANGUAGE KindSignatures, DataKinds, MultiParamTypeClasses,
             TypeFamilies, RankNTypes, FlexibleInstances, 
             UndecidableInstances, PolyKinds, FlexibleContexts,
             NoMonomorphismRestriction, TypeOperators, GADTs #-}

module RecordsPrototype where

import Control.Applicative
import GHC.TypeLits


-- These class and type family declarations, the instance declaration
-- for Accessor (->) and the definition of `field` go in base:

type family GetResult (r :: *) (f :: Symbol) :: *
class (t ~ GetResult r f, r ~ SetResult r f t) =>
          Get r (f :: Symbol) t where
  getFld :: proxy f -> r -> t

type family SetResult (r :: *) (f :: Symbol) (a :: *) :: *  
class Get r f (GetResult r f) => Set (r :: *) (f :: Symbol) (a :: *) where
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
data V k = MkV { _foo'' :: Int, _bar'' :: k Int }
data W a where
    MkW :: (a ~ b, Ord a) => { gaa :: a, gab :: b } -> W (a, b)


-- ...lead to automatic generation of the following instances...

type instance GetResult (R a) "foo" = a -> a
instance t ~ (a -> a) => Get (R a) "foo" t where
  getFld _ (MkR x) = x

type instance SetResult (R a) "foo" (b -> b) = R b
instance (t ~ (b -> b)) => Set (R a) "foo" t where
  setFld _ (MkR _) x = MkR x

type instance GetResult (T a) "x" = [a]
instance (t ~ [a]) => Get (T a) "x" t where
  getFld _ (MkT x) = x

type instance SetResult (T a) "x" [c] = T c
instance (t ~ [c]) => Set (T a) "x" t where
  setFld _ (MkT _) y = MkT y

type instance GetResult (U a) "foo" = R a
instance t ~ R a => Get (U a) "foo" t where
  getFld _ (MkU x _) = x

type instance SetResult (U a) "foo" (R c) = U c
instance t ~ R a => Set (U a) "foo" t where
  setFld _ (MkU _ y) x = MkU x y

type instance GetResult (U a) "bar" = a
instance t ~ a => Get (U a) "bar" t where
  getFld _ (MkU _ y) = y

type instance SetResult (U a) "bar" c = U c
instance t ~ a => Set (U a) "bar" t where
  setFld _ (MkU x _) y = MkU x y

type instance GetResult (V k) "foo" = Int
instance t ~ Int => Get (V k) "foo" t where
  getFld _ (MkV x _) = x

type instance SetResult (V k) "foo" Int = V k
instance t ~ Int => Set (V k) "foo" t where
  setFld _ (MkV _ y) x = MkV x y

type instance GetResult (V k) "bar" = k Int
instance t ~ k Int => Get (V k) "bar" t where
  getFld _ (MkV _ y) = y

type instance SetResult (V k) "bar" (l Int) = V l
instance t ~ l Int => Set (V k) "bar" t where
  setFld _ (MkV x _) y = MkV x y

type instance GetResult (W (a, b)) "gaa" = a
instance (t ~ a, c ~ (a, b)) => Get (W c) "gaa" t where
  getFld _ (MkW gaa _)   = gaa

type instance SetResult (W (a, b)) "gaa" c = W (c, b)
instance (t ~ a, c ~ (a, b)) => Set (W c) "gaa" t where
  setFld _ (MkW _ gab) gaa = MkW gaa gab

type instance GetResult (W (a, b)) "gab" = b
instance (t ~ b, c ~ (a, b)) => Get (W c) "gab" t where
  getFld _ (MkW _ gab) = gab

type instance SetResult (W (a, b)) "gab" c = W (a, c)
instance (t ~ a, c ~ (a, b)) => Set (W c) "gab" t where
  setFld _ (MkW gaa _) gab = MkW gaa gab


-- Note that:
--  * there are no instances for bar from S, because it is higher rank;
--  * the Set instances for U do not support type-changing update,
--      because its fields cannot be updated individually.


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


foo_is_a_lens :: Set r "foo" b =>
                 Lens r (SetResult r "foo" b) (GetResult r "foo") b
foo_is_a_lens = fieldLens foo


-- What if our lenses don't support type-changing update?  No problem!
-- Here is the relevant class (the dependency on the field name has
-- gone, of course).  This could replace `Accessor` entirely if we
-- wanted to drop support for type-changing update.

class SimpleAccessor h where
  simpleAccessor :: (r -> a) -> (r -> a -> r) -> h r a

instance SimpleAccessor (->) where
  simpleAccessor getter setter = getter


-- If `h` is a simple lens type, then `Wrap h f` is a normal `Accessor`,
-- wrapping up a proof that the record type doesn't change.

newtype Wrap h f r a = MkWrap
    { simpleField :: (Set r f a, SetResult r f a ~ r) => h r a }

instance (f ~ g, SimpleAccessor h) => Accessor (Wrap h f) g where
  accessor _ getter setter = MkWrap (simpleAccessor getter setter)


-- Now simple lenses are accessors:

newtype SimpleLens r a = MkSimpleLens (Lens r r a a)

instance SimpleAccessor SimpleLens where
  simpleAccessor getter setter =
    MkSimpleLens (\ w s -> setter s <$> w (getter s))

-- And `simpleField` turns a field into a simple lens:

type Field h = (Set r f a, r ~ SetResult r f a) => Wrap h f r a -> h r a

fieldSimpleLens :: Field SimpleLens
fieldSimpleLens = simpleField


-- data-lens (ish)

data DataLens r a = DataLens
   { getDL :: r -> a
   , setDL :: r -> a -> r }

instance SimpleAccessor DataLens where
  simpleAccessor = DataLens

fieldDataLens :: Field DataLens
fieldDataLens = simpleField


-- fclabels

data Point arr f i o = Point
  { _get :: f `arr` o
  , _set :: (i, f) `arr` f
  }

newtype FCLens arr f a = FCLens { unLens :: Point arr f a a }

instance SimpleAccessor (FCLens (->)) where
  simpleAccessor getter setter =
      FCLens (Point getter (uncurry $ flip setter))

fieldFCLens :: Field (FCLens (->))
fieldFCLens = simpleField


-- data-accessor

newtype DataAccessor r a = Cons {decons :: r -> (a, a -> r)}

instance SimpleAccessor DataAccessor where
  simpleAccessor getter setter = Cons (\ r -> (getter r, setter r))

fieldDataAccessor :: Field DataAccessor
fieldDataAccessor = simpleField


-- Oh, I almost forgot, we need proxy types until explicit type
-- application is sorted:

data Proxy k = Proxy
