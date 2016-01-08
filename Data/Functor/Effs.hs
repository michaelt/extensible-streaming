{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-|
Module      : Data.Functor.Effs
Description : Open unions (type-indexed co-products) for extensible effects.
Copyright   : Alej Cabrera 2015, Michael Thompson 2016
License     : BSD-3
Maintainer  : cpp.cabrera@gmail.com
Stability   : experimental
Portability : POSIX

This implementation relies on _closed_ type families added to GHC
7.8. It has NO overlapping instances and NO Typeable. Alas, the
absence of Typeable means the projections and injections generally
take linear time.  The code illustrate how to use closed type families
to disambiguate otherwise overlapping instances.

The data constructors of Union are not exported. Essentially, the
nested Either data type.

Using <http://okmij.org/ftp/Haskell/extensible/OpenUnion41.hs> as a
starting point.

-}

module Data.Functor.Effs where

import Data.Functor.Sum
--------------------------------------------------------------------------------
                         -- Implementation --
--------------------------------------------------------------------------------
data Nat = S Nat | Z
data Index (n :: Nat) = Index
data Token (f :: * -> *) = Token

type family Position (f :: * -> *) fs :: Nat where
  Position f (f ': fs)  = 'Z
  Position f (x ': fs)  = 'S (Position f fs)

--------------------------------------------------------------------------------

data Effs (fss :: [ * -> * ]) v where
  Here  :: forall f fs x v . f x -> (x -> v) -> Effs (f ': fs) v
  There :: Effs fs v    -> Effs (f ': fs) v

instance Functor (Effs fs) where
  fmap f (Here fa out)  = Here fa (f . out)
  fmap f (There fs) = There (fmap f fs)

data Lan f r = forall x . Lan (f x) (x -> r)
instance Functor (Lan f) where fmap f (Lan fx out) = Lan fx (f . out)
--------------------------------------------------------------------------------

class IsAt (n :: Nat) f fs where
  injectAt  :: Index n -> Lan f r -> Effs fs r
  projectAt :: Index n -> Effs fs r -> Maybe (Lan f r)

instance (fs ~ (f ': fs')) => IsAt 'Z f fs  where
  injectAt _  (Lan f out)  = Here f out
  projectAt _ (Here x out) = Just (Lan x out)
  projectAt _ _            = Nothing

instance (fs ~ (f' ': fs'), IsAt n f fs') => IsAt ('S n) f fs  where
  injectAt _  f          = There (injectAt (Index :: Index n) f)
  projectAt _ (There x)  = projectAt (Index :: Index n) x
  projectAt _ (Here _ _) = Nothing

--------------------------------------------------------------------------------

class (IsAt (Position f fs) f fs) => Elem f fs where
  inject  :: Lan f r -> Effs fs r
  project :: Effs fs r -> Maybe (Lan f r)

instance (IsAt (Position f fs) f fs) => Elem f fs where
  inject  = injectAt (Index :: Index (Position f fs))
  project = projectAt (Index :: Index (Position f fs))

--------------------------------------------------------------------------------

scrutinize :: Effs (f ': fs) v -> Sum (Lan f) (Effs fs) v
scrutinize (Here fx out)  = InL (Lan fx out)
scrutinize (There v) = InR v



