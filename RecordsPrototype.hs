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

class t ~ GetResult r f => Has r (f :: Symbol) t where
  getField :: proxy f -> r -> t

type family SetResult (r :: *) (f :: Symbol) (a :: *) :: *  

class (Has r f (GetResult r f), r ~ SetResult r f (GetResult r f)) =>
          Upd (r :: *) (f :: Symbol) (a :: *) where
  setField :: proxy f -> r -> a -> SetResult r f a

class Accessor (p :: * -> * -> *) (f :: Symbol) where
  accessor :: proxy f -> (r -> GetResult r f) ->
              (forall a . Upd r f a => r -> a -> SetResult r f a) ->
              p r (GetResult r f)

instance Accessor (->) f where
  accessor _ getter setter = getter


field :: (Has r f t, Accessor p f) => proxy f -> p r t
field z = accessor z (getField z) (setField z)


-- Some example datatypes...

data R a = MkR { _foo :: a -> a }
data S   = MkS { _bar :: forall b. b -> b }
data T a = MkT { _x :: [a] }
data U a = MkU { _foo' :: R a, _bar' :: a }
data V k = MkV { _foo'' :: Int, _bar'' :: k Int }
data W a where
    MkW :: (a ~ b, Ord a) => { gaa :: a, gab :: b } -> W (a, b)
data X a = MkX { _foo''' :: Bool }

data family F (a :: *)
data instance F Int = MkF { _foo'''' :: Int }

-- ...lead to automatic generation of the following instances...

type instance GetResult (R a) "foo" = a -> a
instance t ~ (a -> a) => Has (R a) "foo" t where
  getField _ (MkR x) = x

type instance SetResult (R a) "foo" (b -> b) = R b
instance (t ~ (b -> b)) => Upd (R a) "foo" t where
  setField _ (MkR _) x = MkR x

type instance GetResult (T a) "x" = [a]
instance (t ~ [a]) => Has (T a) "x" t where
  getField _ (MkT x) = x

type instance SetResult (T a) "x" [c] = T c
instance (t ~ [c]) => Upd (T a) "x" t where
  setField _ (MkT _) y = MkT y

type instance GetResult (U a) "foo" = R a
instance t ~ R a => Has (U a) "foo" t where
  getField _ (MkU x _) = x

type instance SetResult (U a) "foo" (R c) = U c
instance t ~ R a => Upd (U a) "foo" t where
  setField _ (MkU _ y) x = MkU x y

type instance GetResult (U a) "bar" = a
instance t ~ a => Has (U a) "bar" t where
  getField _ (MkU _ y) = y

type instance SetResult (U a) "bar" c = U c
instance t ~ a => Upd (U a) "bar" t where
  setField _ (MkU x _) y = MkU x y

type instance GetResult (V k) "foo" = Int
instance t ~ Int => Has (V k) "foo" t where
  getField _ (MkV x _) = x

type instance SetResult (V k) "foo" Int = V k
instance t ~ Int => Upd (V k) "foo" t where
  setField _ (MkV _ y) x = MkV x y

type instance GetResult (V k) "bar" = k Int
instance t ~ k Int => Has (V k) "bar" t where
  getField _ (MkV _ y) = y

type instance SetResult (V k) "bar" (l Int) = V l
instance t ~ l Int => Upd (V k) "bar" t where
  setField _ (MkV x _) y = MkV x y

type instance GetResult (W (a, b)) "gaa" = a
instance (t ~ a, c ~ (a, b)) => Has (W c) "gaa" t where
  getField _ (MkW gaa _)   = gaa

type instance SetResult (W (a, b)) "gaa" c = W (c, b)
instance (t ~ a, c ~ (a, b)) => Upd (W c) "gaa" t where
  setField _ (MkW _ gab) gaa = MkW gaa gab

type instance GetResult (W (a, b)) "gab" = b
instance (t ~ b, c ~ (a, b)) => Has (W c) "gab" t where
  getField _ (MkW _ gab) = gab

type instance SetResult (W (a, b)) "gab" c = W (a, c)
instance (t ~ a, c ~ (a, b)) => Upd (W c) "gab" t where
  setField _ (MkW gaa _) gab = MkW gaa gab

type instance GetResult (X a) "foo" = Bool
instance t ~ Bool => Has (X a) "foo" t where
  getField _ (MkX x) = x

type instance SetResult (X a) "foo" Bool = X a
instance t ~ Bool => Upd (X a) "foo" t where
  setField _ (MkX _ ) x = MkX x

type instance GetResult (F Int) "foo" = Int
instance t ~ Int => Has (F Int) "foo" t where
  getField _ (MkF x) = x

type instance SetResult (F Int) "foo" Int = F Int
instance t ~ Int => Upd (F Int) "foo" t where
  setField _ (MkF _) x = MkF x

-- Note that:
--  * there are no instances for bar from S, because it is higher rank;
--  * the Upd instances for U do not support type-changing update,
--      because its fields cannot be updated individually.
--  * similarly X does not support type-changing update, because it
--      has a phantom type variable.


data FC (f :: y -> *)(g :: x -> y)(a :: x) :: * where
   FC :: { runFC :: f (g a) } -> FC f g a

type instance GetResult (FC f g a) "runFC" = f (g a)
type instance SetResult (FC f (g :: x -> y) a) "runFC" (f' ((g' :: x -> y) a')) = FC f' g' a'

instance t ~ f (g a) => Has (FC f g a) "runFC" t where
  getField _ (FC x) = x

instance forall (f :: y -> *)(f' :: y -> *)(g :: x -> y)(g' :: x -> y)(a :: x)(a' :: x)(b :: *) .
            b ~ f' (g' a') => Upd (FC f g a) "runFC" b where
  setField _ (FC _) x = FC x


-- These function declarations approximate how uses of the fields
-- would be handled by the typechecker:

foo :: (Has r "foo" t, Accessor p "foo") => p r t
foo = field (Proxy :: Proxy "foo")

bar :: (Has r "bar" t, Accessor p "bar") => p r t
bar = field (Proxy :: Proxy "bar")

x :: (Has r "x" t, Accessor p "x") => p r t
x = field (Proxy :: Proxy "x")


-- We can use fields:

t = foo (MkR not) False

-- We can compose polymorphic fields:

fooBar = foo . bar


-- Using a newtype wrapper, we can turn any field into a lens by
-- applying the `fieldLens` function.  Everything from here onwards
-- can go in libraries other than base.

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

newtype WrapLens f r a
  = MkWrapLens (forall b . Upd r f b => Lens r (SetResult r f b) a b)

instance f ~ g => Accessor (WrapLens f) g where
  accessor _ getter setter = MkWrapLens (\ w s -> setter s <$> w (getter s))

fieldLens :: Upd r f b => WrapLens f r a -> Lens r (SetResult r f b) a b
fieldLens (MkWrapLens l) = l


foo_is_a_lens :: Upd r "foo" b =>
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
    { simpleField :: (Upd r f a, SetResult r f a ~ r) => h r a }

instance (f ~ g, SimpleAccessor h) => Accessor (Wrap h f) g where
  accessor _ getter setter = MkWrap (simpleAccessor getter setter)


-- Now simple lenses are accessors:

newtype SimpleLens r a = MkSimpleLens (Lens r r a a)

instance SimpleAccessor SimpleLens where
  simpleAccessor getter setter =
    MkSimpleLens (\ w s -> setter s <$> w (getter s))

-- And `simpleField` turns a field into a simple lens:

type Field h = (Upd r f a, r ~ SetResult r f a) => Wrap h f r a -> h r a

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
