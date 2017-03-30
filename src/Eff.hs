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
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ApplicativeDo #-}

module Eff where

import Data.Kind (Type)
import GHC.Exts (Constraint)
import Control.Applicative
import Data.Functor.Identity

data family Dict (eff :: k) (m :: Type -> Type) :: Type

type family Super (eff :: k) (m :: km) :: Constraint

class Super eff m => eff <: (m :: Type -> Type) where
  dict :: Dict eff m

instance {-# OVERLAPPABLE #-}
  ( eff <: m,
    baseEff <: m,
    Lift baseEff eff t,
    Super eff (t m) ) =>
      (eff :: Type) <: t m
  where
    dict = lift dict

class Handle baseEff eff t | eff t -> baseEff where
  handle :: baseEff <: m => Dict eff (t m)

class Lift baseEff eff t | eff t -> baseEff where
  lift :: baseEff <: m => Dict eff m -> Dict eff (t m)

-- CONSTRAINT

data instance Dict (c :: km -> Constraint) m where
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

-- OPTICS

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

type Lens' s a = Lens s s a a

view :: Lens s t a b -> s -> a
view l = getConst . l Const

over :: Lens s t a b -> (a -> b) -> s -> t
over l f = runIdentity . l (Identity . f)

set :: Lens s t a b -> b -> s -> t
set l b = over l (const b)

class HasLens outer inner where
  lens :: Lens' outer inner

instance HasLens a a where
  lens = id

instance HasLens (a, b) a where
  lens f (a, b) = (,b) <$> f a

instance HasLens (a, b) b where
  lens f (a, b) = (a,) <$> f b

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

instance Lift '() Applicative (ReaderT r) where
  lift MDict = MDict

instance Lift '() Functor (ReaderT r) where
  lift MDict = MDict

instance Lift '() Monad (ReaderT r) where
  lift MDict = MDict

instance Lift '() (R r') (ReaderT r) where
  lift d = RDict
    { _ask    = lift' (_ask d),
      _local  = \f -> mapReaderT (_local d f),
      _reader = \f -> lift' (_reader d f) }
    where
      lift' m = ReaderT (\_ -> m)

rFocus ::
  forall r r' m .
  Functor m =>
  Lens' r r' ->
  Dict (R r) m ->
  Dict (R r') m
rFocus l d = RDict
  { _ask    = view l <$> _ask d,
    _local  = \f -> _local d (over l f),
    _reader = \f -> _reader d (f . view l) }

instance r' ~ r => Handle Applicative (R r') (ReaderT r) where
  handle = RDict
    { _ask    = ReaderT pure,
      _local  = withReaderT,
      _reader = \f -> ReaderT (pure . f) }

instance (HasLens r r', Applicative m) => R r' <: ReaderT r m where
  dict = rFocus lens handle

-- STATE

data S (s :: Type)

data instance Dict (S s) m = SDict
  { _get   :: m s,
    _put   :: s -> m (),
    _state :: forall a . (s -> (a, s)) -> m a }

type instance Super (S s) m = ()

get :: (S s <: m) => m s
get = _get dict

put :: (S s <: m) => s -> m ()
put = _put dict

state :: (S s <: m) => (s -> (a, s)) -> m a
state = _state dict

-- STATE IMPL

newtype StateT s m a = StateT (s -> m (a, s))

runStateT :: StateT s m a -> s -> m (a, s)
runStateT (StateT k) = k

instance Functor m => Functor (StateT s m) where
  fmap f m =
    StateT (\s -> fmap (\(~(a, s')) -> (f a, s')) (runStateT m s))

instance Monad m => Applicative (StateT s m) where
  pure a =
    StateT (\s -> pure (a, s))
  (<*>) mf ma =
    StateT (\s -> do
      ~(f, s') <- runStateT mf s
      ~(a, s'') <- runStateT ma s'
      pure (f a, s''))

instance Monad m => Monad (StateT s m) where
  (>>=) ma f =
    StateT (\s -> runStateT ma s >>= \(~(a, s')) -> runStateT (f a) s')

instance Lift Functor (S s') (StateT s) where
  lift d = SDict
    { _get   = lift' (_get d),
      _put   = \s -> lift' (_put d s),
      _state = \f -> lift' (_state d f) }
    where
      lift' m = StateT (\s -> (,s) <$> m)

sFocus ::
  forall s s' m .
  Functor m =>
  Lens' s s' ->
  Dict (S s) m ->
  Dict (S s') m
sFocus l d = SDict
  { _get   = view l <$> _get d,
    _put   = \s' -> _state d (\s -> ((), set l s' s)),
    _state = \f -> _state d (l f) }

instance s' ~ s => Handle Applicative (S s') (StateT s) where
  handle = SDict
    { _get   = StateT (\s -> pure (s, s)),
      _put   = \s -> StateT (\_ -> pure ((), s)),
      _state = \f -> StateT (\s -> pure (f s)) }

instance (HasLens s s', Applicative m) => S s' <: StateT s m where
  dict = sFocus lens handle

-- EXAMPLES

ex1_0 :: '(R String, Applicative, R Int) <: m => m Int
ex1_0 = do
  a <- ask
  b <- ask
  return ((a :: Int) + length (b :: String))

ex1 :: '(Applicative, R Int, R String) <: m => m Int
ex1 = local @Int (*2) ex1_0

ex1' :: Int -> IO Int
ex1' i = runReaderT ex1 (i, show i)
