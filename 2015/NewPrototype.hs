{-
  This is a newly revised (as of January 2015) plan for overloaded
  record fields in GHC, along the lines of the previous descriptions
  but with some significant simplications.
-}

{-# LANGUAGE KindSignatures, DataKinds, MultiParamTypeClasses,
             TypeFamilies, RankNTypes, FlexibleInstances,
             UndecidableInstances, PolyKinds, FlexibleContexts,
             NoMonomorphismRestriction, TypeOperators, GADTs,
             IncoherentInstances #-}

module NewPrototype where

import Control.Applicative
import GHC.TypeLits


------------------------------------------------------------------------------
-- Translation of record fields in expressions
------------------------------------------------------------------------------

-- The 'IsRecordField' class will be used in the translation of record
-- fields appearing in expressions, when OverloadedRecordFields is
-- enabled.  Instances of this class give ways to interpret fields.
--
-- This is not a profunctor! Does that matter?
class IsRecordField (n :: Symbol) p where
  field :: proxy n -> p

-- These function declarations approximate how uses of the fields
-- would be handled by the typechecker:

foo :: IsRecordField "foo" p => p
foo = field (Proxy :: Proxy "foo")

bar :: IsRecordField "bar" p => p
bar = field (Proxy :: Proxy "bar")

x :: IsRecordField "x" p => p
x = field (Proxy :: Proxy "x")


------------------------------------------------------------------------------
-- Constraint solver extensions
------------------------------------------------------------------------------

-- The 'Has' and 'Upd' typeclasses and 'FldTy' and 'UpdTy' type
-- families (better names required) have special-purpose constraint
-- solving behaviour, which could be built-in to GHC or implemented in
-- a plugin.  We need not actually generate instances, although this
-- may be a useful intuition for how the constraint solver works.
--
-- These classes are used to give 'IsRecordField' instances for
-- functions and lenses (only 'Has'/'FldTy' are required for
-- functions, so we could separate them out).

type family FldTy (r :: *) (n :: Symbol) :: *
type family UpdTy (r :: *) (n :: Symbol) (a :: *) :: *

class Has r n where
  getField :: proxy n -> r -> FldTy r n

class
  ( Has r n
  , r ~ UpdTy r n (FldTy r n)
  ) => Upd r n a where
  setField :: proxy n -> r -> a -> UpdTy r n a

instance (Has r n, FldTy r n ~ t) => IsRecordField n (r -> t) where
  field = getField


-- Some example datatypes, and the instances they "generate":

data R a = MkR { _foo :: a -> a }

type instance FldTy (R a) "foo" = a -> a
type instance UpdTy (R a) "foo" (b -> b) = R b

instance Has (R a) "foo" where
  getField _ (MkR x) = x

instance (t ~ (b -> b)) => Upd (R a) "foo" t where
  setField _ (MkR _) x = MkR x


-----
-- No instances generated for S, because bar is higher-rank
data S = MkS { _bar :: forall b. b -> b }


-----
-- Standard example
data T a = MkT { _x :: [a] }

type instance FldTy (T a) "x" = [a]
type instance UpdTy (T a) "x" [c] = T c

instance Has (T a) "x" where
  getField _ (MkT x) = x

instance (t ~ [c]) => Upd (T a) "x" t where
  setField _ (MkT _) y = MkT y


-----
-- Type-changing update not available
-- (parameter used in multiple fields)
data U a = MkU { _foo' :: R a, _bar' :: a }

type instance FldTy (U a) "foo" = R a
type instance UpdTy (U a) "foo" (R c) = U c

instance Has (U a) "foo" where
  getField _ (MkU x _) = x

instance t ~ R a => Upd (U a) "foo" t where
  setField _ (MkU _ y) x = MkU x y


type instance FldTy (U a) "bar" = a
type instance UpdTy (U a) "bar" c = U c

instance Has (U a) "bar" where
  getField _ (MkU _ y) = y

instance t ~ a => Upd (U a) "bar" t where
  setField _ (MkU x _) y = MkU x y


-----
-- Example with a higher-kinded parameter
data V k = MkV { _foo'' :: Int, _bar'' :: k Int }

type instance FldTy (V k) "foo" = Int
type instance UpdTy (V k) "foo" Int = V k

instance Has (V k) "foo" where
  getField _ (MkV x _) = x

instance t ~ Int => Upd (V k) "foo" t where
  setField _ (MkV _ y) x = MkV x y


type instance FldTy (V k) "bar" = k Int
type instance UpdTy (V k) "bar" (l Int) = V l

instance Has (V k) "bar" where
  getField _ (MkV _ y) = y

instance t ~ l Int => Upd (V k) "bar" t where
  setField _ (MkV x _) y = MkV x y


-----
-- GADT example
data W a where
    MkW :: (a ~ b, Ord a) => { gaa :: a, gab :: b } -> W (a, b)

type instance FldTy (W (a, b)) "gaa" = a
type instance UpdTy (W (a, b)) "gaa" c = W (c, b)

instance (c ~ (a, b)) => Has (W c) "gaa" where
  getField _ (MkW gaa _)   = gaa

instance (t ~ a, c ~ (a, b)) => Upd (W c) "gaa" t where
  setField _ (MkW _ gab) gaa = MkW gaa gab


type instance FldTy (W (a, b)) "gab" = b
type instance UpdTy (W (a, b)) "gab" c = W (a, c)

instance (c ~ (a, b)) => Has (W c) "gab" where
  getField _ (MkW _ gab) = gab

instance (t ~ a, c ~ (a, b)) => Upd (W c) "gab" t where
  setField _ (MkW gaa _) gab = MkW gaa gab


-----
-- Type-changing update not available (phantom type parameter)
data X a = MkX { _foo''' :: Bool }

type instance FldTy (X a) "foo" = Bool
type instance UpdTy (X a) "foo" Bool = X a

instance Has (X a) "foo" where
  getField _ (MkX x) = x

instance t ~ Bool => Upd (X a) "foo" t where
  setField _ (MkX _ ) x = MkX x


-----
-- Type-changing update not available (parameter under a type family)
data Y a = MkY { _x' :: Wobbly a }

type family Wobbly a

type instance FldTy (Y a) "x" = Wobbly a
type instance UpdTy (Y a) "x" z = Y a

instance Has (Y a) "x" where
  getField _ (MkY x) = x

instance t ~ Wobbly a => Upd (Y a) "x" t where
  setField _ (MkY _) x = MkY x



-----
-- Example of a field in a data family
data family F (a :: *)
data instance F Int = MkF { _foo'''' :: Int }

type instance FldTy (F Int) "foo" = Int
type instance UpdTy (F Int) "foo" Int = F Int

instance Has (F Int) "foo" where
  getField _ (MkF x) = x

instance t ~ Int => Upd (F Int) "foo" t where
  setField _ (MkF _) x = MkF x


-----
-- Poly-kinded example
data FC (f :: y -> *)(g :: x -> y)(a :: x) :: * where
   FC :: { runFC :: f (g a) } -> FC f g a

type instance FldTy (FC f g a) "runFC" = f (g a)
type instance UpdTy (FC f (g :: x -> y) a) "runFC" (f' ((g' :: x -> y) a')) = FC f' g' a'

instance Has (FC f g a) "runFC" where
  getField _ (FC x) = x

instance forall (f :: y -> *)(f' :: y -> *)(g :: x -> y)(g' :: x -> y)(a :: x)(a' :: x)(t :: *) .
            t ~ f' (g' a') => Upd (FC f g a) "runFC" t where
  setField _ (FC _) x = FC x


------------------------------------------------------------------------------
-- Using overloaded fields
------------------------------------------------------------------------------

-- We can use fields as selectors:

t = foo (MkR not) False

-- We can compose polymorphic fields:

fooBar = foo . bar



------------------------------------------------------------------------------
-- Interpreting fields as lenses
------------------------------------------------------------------------------

-- Using a newtype wrapper, we can turn any field into a van Laarhoven
-- lens by applying the `fieldLens` function.  Everything from here
-- onwards can go in libraries other than base.

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

newtype WrapLens n r a
  = MkWrapLens { le :: forall b . Upd r n b => Lens r (UpdTy r n b) a b }

instance (m ~ n, a ~ FldTy r n) => IsRecordField n (WrapLens m r a) where
  field p = MkWrapLens (\ w s -> setField p s <$> w (getField p s))

-- We could even make fields directly into van Laarhoven lenses, but
-- this overlaps incoherently with the normal instance for (->), so we
-- might not want both... can we let the user choose?

instance (Functor f, Has r n, Upd r n b, a ~ FldTy r n, r' ~ UpdTy r n b)
           => IsRecordField n ((a -> f b) -> r -> f r') where
  field p w s = setField p s <$> w (getField p s)


fieldLens :: Upd r n b => WrapLens n r a -> Lens r (UpdTy r n b) a b
fieldLens (MkWrapLens l) = l

field_is_a_lens :: Upd r n b => proxy n -> Lens r (UpdTy r n b) (FldTy r n) b
field_is_a_lens = field


foo_is_a_lens :: Upd r "foo" b =>
                 Lens r (UpdTy r "foo" b) (FldTy r "foo") b
foo_is_a_lens = fieldLens foo

foo_is_a_lens' :: Upd r "foo" b =>
                 Lens r (UpdTy r "foo" b) (FldTy r "foo") b
foo_is_a_lens' = foo


-- What if our lenses don't support type-changing update?  No problem!

-- data-lens (ish)

data DataLens r a = DataLens
   { getDL :: r -> a
   , setDL :: r -> a -> r }

instance (Upd r n a, a ~ FldTy r n) => IsRecordField n (DataLens r a) where
  field p = DataLens (getField p) (setField p)


-- fclabels

data Point arr f i o = Point
  { _get :: f `arr` o
  , _set :: (i, f) `arr` f
  }

newtype FCLens arr f a = FCLens { unLens :: Point arr f a a }

instance (Upd r n a, a ~ FldTy r n) => IsRecordField n (FCLens (->) r a) where
  field p = FCLens (Point (getField p) (uncurry $ flip $ setField p))


-- data-accessor

newtype DataAccessor r a = Cons {decons :: r -> (a, a -> r)}

instance (Upd r n a, a ~ FldTy r n) => IsRecordField n (DataAccessor r a) where
  field p = Cons (\ r -> (getField p r, setField p r))


-- Oh, I almost forgot, we need proxy types until explicit type
-- application is sorted:

data Proxy k = Proxy
-- In HEAD we will use the new unboxed Proxy# type
