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

module Eff where

import Data.Kind (Type)
import GHC.Exts (Constraint)

data family Dict (eff :: k) (m :: Type -> Type) :: Type

type family Super (eff :: k) (m :: Type -> Type) :: Constraint

class Super eff m => eff <: (m :: Type -> Type) where
  dict :: Dict eff m

instance {-# OVERLAPPABLE #-}
  ( baseEff <: m,
    eff <: m,
    Lift baseEff eff t,
    Super eff (t m) ) =>
      (eff :: Type) <: t m
  where
    dict = lift dict

class Lift baseEff eff t | eff t -> baseEff where
  lift :: baseEff <: m => Dict eff m -> Dict eff (t m)

-- CONSTRAINT

type MConstraint = (Type -> Type) -> Constraint

data instance Dict (c :: MConstraint) m where
  MDict :: c m => Dict c m

type instance Super (c :: MConstraint) m = c m

instance Super c m => (c :: MConstraint) <: m where
  dict = MDict

-- UNIT

data instance Dict '() m = UDict

type instance Super '() m = ()

instance '() <: m where
  dict = UDict

-- PRODUCT

-- 2

data instance Dict '(f, g) m = PDict2 (Dict f m) (Dict g m)

type instance Super '(f, g) m = (f <: m, g <: m)

instance Super '(f, g) m => '(f, g) <: m where
  dict = PDict2 dict dict

-- 3

data instance Dict '(f, g, h) m = PDict3 (Dict f m) (Dict g m) (Dict h m)

type instance Super '(f, g, h) m = (f <: m, g <: m, h <: m)

instance Super '(f, g, h) m => '(f, g, h) <: m where
  dict = PDict3 dict dict dict

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
    _local  :: (r -> r) -> m r -> m r,
    _reader :: forall a . (r -> a) -> m a }

type instance Super (R r) m = ()

ask :: (R r <: m) => m r
ask = _ask dict

local :: (R r <: m) => (r -> r) -> m r -> m r
local = _local dict

reader :: (R r <: m) => (r -> a) -> m a
reader = _reader dict

-- READER IMPL

newtype ReaderT r m a = ReaderT (r -> m a)

instance Lift Applicative Applicative (ReaderT r) where
  lift MDict = MDict

instance Lift Functor Functor (ReaderT r) where
  lift MDict = MDict

instance Lift Monad Monad (ReaderT r) where
  lift MDict = MDict

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

instance Lift '() (R r) (ReaderT r') where
  lift r = RDict
    { _ask    = ReaderT (\_ -> _ask r),
      _local  = \f -> mapReaderT (_local r f),
      _reader = \f -> ReaderT (\_ -> _reader r f) }

instance Monad <: m => R r <: ReaderT r m where
  dict = RDict
    { _ask    = ReaderT pure,
      _local  = withReaderT,
      _reader = \f -> ReaderT (pure . f) }

ex1 :: '(Monad, '[R Int, R String]) <: m => m Int
ex1 = do
  local (*2) $ do
    a <- ask @Int
    b <- ask @String
    return (a + length b)

ex1' :: Int -> IO Int
ex1' i = runReaderT (runReaderT ex1 i) (show i)
