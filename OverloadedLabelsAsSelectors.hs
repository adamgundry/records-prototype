{-# LANGUAGE AllowAmbiguousTypes
           , ConstraintKinds
           , DataKinds
           , DuplicateRecordFields
           , FlexibleContexts
           , FlexibleInstances
           , FunctionalDependencies
           , GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , NoMonomorphismRestriction
           , OverloadedLabels
           , PolyKinds
           , RankNTypes
           , ScopedTypeVariables
           , TypeApplications
           , TypeFamilies
           , TypeOperators
           , UndecidableInstances
           #-}

module OverloadedLabelsAsSelectors where

import Control.Applicative
import GHC.TypeLits
import GHC.OverloadedLabels


------------------------------------------------------------------------------
-- Interpreting overloaded labels as selectors
------------------------------------------------------------------------------

-- | The 'HasField' typeclass represents the constraint that the type
-- @s@ has a field @x@ of type @a@.
--
-- It will be solved automatically by the constraint solver, rather
-- than actually having instances, because instances have uncontrolled
-- scope but we want 'HasField' to check that the datatype's field is
-- in scope. In this prototype, however, we write out the instances by
-- hand and ignore cross-module scope issues.
class HasField (x :: Symbol) s a | x s -> a where
  getField :: s -> a

-- | Using 'HasField', we can give an 'IsLabel' instance to interpret
-- overloaded labels as selector functions.
--
-- (Probably we should get rid of the proxy argument to 'fromLabel',
-- since it is no longer needed now that we have @TypeApplications@.)
instance HasField x s a => IsLabel x (s -> a) where
  fromLabel _ = getField @x


-- | Here's an example datatype...
data T a = MkT { foo :: [a] }

-- | ... along with the instance (note that the dictionary for the
-- instance contains precisely the selector function):
instance HasField "foo" (T a) [a] where
  getField = foo


-- | We can use overloaded labels as selectors:
xs = #foo (MkT [1,2,3])

-- | We can compose field selectors, retaining type inference, but
-- restricting the labels to being selectors:
fooBar = #foo . #bar

-- | The type of a composition is simple enough (but requires
-- @FlexibleContexts@):
fooBaz :: (HasField "foo" b c, HasField "baz" a b) => a -> c
fooBaz = #foo . #baz



------------------------------------------------------------------------------
-- Interpreting overloaded labels as lenses
------------------------------------------------------------------------------

-- | If we want to be able to turn overloaded labels into lenses, we
-- need the ability to set fields as well as get them.  This is
-- provided by the 'ModifyField' class:
class ModifyField x s t b | x s b -> t where
  setField :: s -> b -> t

-- | This class could be solved rather like 'HasField', except that we
-- would need to generate code for the setter functions somewhere.
instance ModifyField "x" (T a) (T b) [b] where
  setField (MkT _) foo = MkT foo


-- | Using a newtype wrapper, we can turn any field into a van
-- Laarhoven lens by applying the 'runLens' function.
--
-- Everything from here onwards can go in libraries other than base.
newtype ReifiedLens s t a b = Lens { runLens :: Lens s t a b }

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

type FieldLens x s t a b = (HasField x s a, ModifyField x s t b)

instance FieldLens x s t a b => IsLabel x (ReifiedLens s t a b) where
  fromLabel _ = Lens (\ w s -> setField @x s <$> w (getField @x s))


foo_is_a_lens :: FieldLens "foo" s t a b => Lens s t a b
foo_is_a_lens = runLens #foo

fooBar_is_a_lens = runLens #foo . runLens #bar

fooBaz_is_a_lens :: (FieldLens "foo" s t u v, FieldLens "baz" u v a b) => Lens s t a b
fooBaz_is_a_lens = runLens #foo . runLens #baz



-- We could even make fields directly into van Laarhoven lenses, but
-- this overlaps incoherently with the normal instance for (->), and
-- hence breaks type inference for the composition of fields.

-- instance (Functor f, HasField x s a, ModifyField x s t b)
--            => IsLabel x ((a -> f b) -> s -> f t) where
--   fromLabel _ w s = setField @x s <$> w (getField @x s)



-- | What if we use another representation of lenses, that doesn't
-- support type-changing update?  No problem!
data DataLens r a = DataLens
   { getDL :: r -> a
   , setDL :: r -> a -> r }

instance (HasField x s a, ModifyField x s s a) => IsLabel x (DataLens s a) where
  fromLabel _ = DataLens (getField @x) (setField @x)



------------------------------------------------------------------------------
-- Further examples
------------------------------------------------------------------------------

-- Here are some more example datatypes, and the instances they "generate".


data R a = MkR { foo :: a -> a }

instance HasField "foo" (R a) (a -> a) where
  getField = foo

instance ModifyField "foo" (R a) (R b) (b -> b) where
  setField (MkR _) x = MkR x


-----
-- No instances generated for S, because bar is higher-rank
data S = MkS { bar :: forall b. b -> b }


-----
-- Type-changing update not available
-- (parameter used in multiple fields)
data U a = MkU { foo :: R a, bar :: a }

instance HasField "foo" (U a) (R a) where
  getField = foo

instance HasField "bar" (U a) a where
  getField = bar

instance ModifyField "foo" (U a) (U a) (R a) where
  setField (MkU _ y) x = MkU x y

instance ModifyField "bar" (U a) (U a) a where
  setField (MkU x _) y = MkU x y


-----
-- Example with a higher-kinded parameter
data V k = MkV { foo :: Int, bar :: k Int }

instance HasField "foo" (V k) Int where
  getField = foo

instance HasField "bar" (V k) (k Int) where
  getField = bar

instance ModifyField "foo" (V k) (V k) Int where
  setField (MkV _ y) x = MkV x y

instance ModifyField "bar" (V k) (V l) (l Int) where
  setField (MkV x _) y = MkV x y


-----
-- GADT example
data W a where
    MkW :: (a ~ b, Ord a) => { gaa :: a, gab :: b } -> W (a, b)

instance HasField "gaa" (W (a,b)) a where
  getField = gaa

instance HasField "gab" (W (a,b)) b where
  getField = gab

instance c ~ b => ModifyField "gaa" (W (a,b)) (W (c,b)) c where
  setField (MkW _ gab) gaa = MkW gaa gab

instance a ~ c => ModifyField "gab" (W (a,b)) (W (a,c)) c where
  setField (MkW gaa _) gab = MkW gaa gab


-----
-- Type-changing update not available (phantom type parameter)
data X a = MkX { foo :: Bool }

instance HasField "foo" (X a) Bool where
  getField = foo

instance ModifyField "foo" (X a) (X a) Bool where
  setField (MkX _) x = MkX x


-----
-- Type-changing update not available (parameter under a type family)
data Y a = MkY { x :: Wobbly a }

type family Wobbly a

instance b ~ Wobbly a => HasField "x" (Y a) b where
  getField = x

instance b ~ Wobbly a => ModifyField "x" (Y a) (Y a) b where
  setField (MkY _) x = MkY x


-----
-- Example of a field in a data family
data family F (a :: *)
data instance F Int = MkF { foo :: Int }

instance HasField "foo" (F Int) Int where
  getField = foo

instance ModifyField "foo" (F Int) (F Int) Int where
  setField (MkF _) x = MkF x


-----
-- Poly-kinded example
data FC (f :: y -> *)(g :: x -> y)(a :: x) :: * where
   FC :: { runFC :: f (g a) } -> FC f g a

instance HasField "runFC" (FC f g a) (f (g a)) where
  getField = runFC

instance ModifyField "runFC" (FC f g a) (FC f' g' a') (f' (g' a')) where
  setField (FC _) x = FC x
