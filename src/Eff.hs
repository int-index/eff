{-# OPTIONS -Wall #-}

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ApplicativeDo #-}

module Eff where

import Data.Kind (Type)
import GHC.Exts (Constraint)

data family Dict (eff :: k) (m :: Type -> Type) :: Type

type family Super (eff :: k) (m :: km) :: Constraint

class Super eff m => eff <: (m :: Type -> Type) where
  dict :: Dict eff m

instance {-# OVERLAPPABLE #-}
  ( eff <: m,
    Lift eff t,
    Super eff (t m) ) =>
      (eff :: Type) <: t m
  where
    dict = lift dict

class Handle baseEff eff t | eff t -> baseEff where
  handle :: baseEff <: m => Dict eff (t m)

class Lift eff t where
  lift :: Dict eff m -> Dict eff (t m)

-- CONSTRAINT

type MConstraint = (Type -> Type) -> Constraint

data instance Dict (c :: MConstraint) m where
  MDict :: c m => Dict c m

type instance Super (c :: km -> Constraint) (m :: km) = c m

instance
  (Super c m, km ~ (Type -> Type)) =>
    (c :: km -> Constraint) <: m
  where
    dict = MDict

-- UNIT

data instance Dict '() m = UDict

type instance Super '() m = ()

instance '() <: m where
  dict = UDict

-- PRODUCT

-- 2

data instance Dict '(f, g) m = P2Dict (Dict f m) (Dict g m)

type instance Super '(f, g) m = (f <: m, g <: m)

instance Super '(f, g) m => '(f, g) <: m where
  dict = P2Dict dict dict

-- 3

data instance Dict '(f, g, h) m = P3Dict (Dict f m) (Dict g m) (Dict h m)

type instance Super '(f, g, h) m = (f <: m, g <: m, h <: m)

instance Super '(f, g, h) m => '(f, g, h) <: m where
  dict = P3Dict dict dict dict

-- LIST

data instance Dict '[] m = LNDict

type instance Super '[] m = ()

instance '[] <: m where
  dict = LNDict

data instance Dict (f ': fs) m = LCDict (Dict f m) (Dict fs m)

type instance Super (f ': fs) m = (f <: m, fs <: m)

instance Super (f ': fs) m => (f ': fs) <: m where
  dict = LCDict dict dict

-- READER

data R (r :: Type)

data instance Dict (R r) m = RDict
  { _ask    :: m r,
    _local  :: forall a . (r -> r) -> m a -> m a,
    _reader :: forall a . (r -> a) -> m a }

type instance Super (R r) m = ()

ask :: (R r <: m) => m r
ask = _ask dict

local :: (R r <: m) => (r -> r) -> m a -> m a
local = _local dict

reader :: (R r <: m) => (r -> a) -> m a
reader = _reader dict

-- READER IMPL

newtype ReaderT r m a = ReaderT (r -> m a)

runReaderT :: ReaderT r m a -> r -> m a
runReaderT (ReaderT k) = k

mapReaderT :: (m a -> n b) -> ReaderT r m a -> ReaderT r n b
mapReaderT f m = ReaderT (f . runReaderT m)

withReaderT :: (r' -> r) -> ReaderT r m a -> ReaderT r' m a
withReaderT f m = ReaderT (runReaderT m . f)

instance Functor m => Functor (ReaderT r m) where
  fmap f m =
    ReaderT (\r -> fmap f (runReaderT m r))

instance Applicative m => Applicative (ReaderT r m) where
  pure a =
    ReaderT (\_ -> pure a)
  (<*>) mf ma =
    ReaderT (\r -> runReaderT mf r <*> runReaderT ma r)

instance Monad m => Monad (ReaderT r m) where
  (>>=) ma f =
    ReaderT (\r -> runReaderT ma r >>= \a -> runReaderT (f a) r)

instance Lift Applicative (ReaderT r) where
  lift MDict = MDict

instance Lift Functor (ReaderT r) where
  lift MDict = MDict

instance Lift Monad (ReaderT r) where
  lift MDict = MDict

instance Lift (R r') (ReaderT r) where
  lift r = RDict
    { _ask    = ReaderT (\_ -> _ask r),
      _local  = \f -> mapReaderT (_local r f),
      _reader = \f -> ReaderT (\_ -> _reader r f) }

-- TODO: HasLens instead of equivalence
instance r ~ r' => Handle Applicative (R r') (ReaderT r) where
  handle = RDict
    { _ask    = ReaderT pure,
      _local  = withReaderT,
      _reader = \f -> ReaderT (pure . f) }

instance Applicative <: m => R r <: ReaderT r m where
  dict = handle

-- EXAMPLES

ex1 :: '(Applicative, R Int, R String) <: m => m Int
ex1 = do
  local @Int (*2) $ do
    a <- ask @Int
    b <- ask @String
    return (a + length b)

ex1' :: Int -> IO Int
ex1' i = runReaderT (runReaderT ex1 i) (show i)
