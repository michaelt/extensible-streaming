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

This implementation of a sum of functors - or rather precisely of possible /non-functors/ ,
i.e. things of kind @* -> *@ -
closely follows that in the 
<http://hackage.haskell.org/package/freer-0.2.2.2/docs/Data-Open-Union.html freer> 
package. The basic sum type is here called @Eff fs@, for a type-level list fs. 
It has been altered so that it can have 
a functor instance, and used directly with @Stream@, @Free@, @FreeT@ and the like.
It is properly a separate package. Similar devices could be used to define
a union of indefinitely many genuine @Functors@ parallel to @Data.Functor.Sum@.

In @freer@, the similar type, @Union@, has no functor instance; 
this is rather supplied by the @Eff@ monad which is then defined in terms of it.  
@freer@ then uses type aligned sequences of Kleisli arrows to represent the free monad
we are looking for. The union type and the free monad implementation are thus
glued together, both taking particular forms. It is the experience of this 
library-writer that type-aligned device is /incredibly/ expensive. Where programs are 
written in properly streaming style, nothing whatever is to be gained by it.


Nevertheless, the union of functors approach has its own costs. 
The author of @freer@, Alej Cabrera, comments on the use of 
advanced type features as follows:

*   This implementation relies on _closed_ type families added to GHC
    7.8. It has NO overlapping instances and NO Typeable. Alas, the
    absence of Typeable means the projections and injections generally
    take linear time.  The code illustrates how to use closed type families
    to disambiguate otherwise overlapping instances.

*   The data constructors of Union are not exported. Essentially, the
    nested Either data type.

*   Using <http://okmij.org/ftp/Haskell/extensible/OpenUnion41.hs> as a
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
  {-#INLINE fmap #-}
  
{- | @Effs@ is a functor, because it internal performs this evasion.
     In order to inspect a list of non-functors, we frequently need
     a functorized representation, which Lan provides. Thus see the
     type of 'scrutinize' which is needed to write recursive loops
     over a stream with many non-functor breaks \'suspended\' in it.
  
  -}
data Lan f r = forall x . Lan (f x) (x -> r)
instance Functor (Lan f) where 
  fmap f (Lan fx out) = Lan fx (f . out)
  {-#INLINE fmap #-}
  
--------------------------------------------------------------------------------

class IsAt (n :: Nat) f fs where
  injectAt  :: Index n -> Lan f r -> Effs fs r
  projectAt :: Index n -> Effs fs r -> Maybe (Lan f r)

instance (fs ~ (f ': fs')) => IsAt 'Z f fs  where
  injectAt _  (Lan f out)  = Here f out
  {-#INLINE injectAt #-}
  projectAt _ (Here x out) = Just (Lan x out)
  projectAt _ _            = Nothing
  {-#INLINE projectAt #-}
  
instance (fs ~ (f' ': fs'), IsAt n f fs') => IsAt ('S n) f fs  where
  injectAt _  f          = There (injectAt (Index :: Index n) f)
  {-#INLINE injectAt #-}
  projectAt _ (There x)  = projectAt (Index :: Index n) x
  projectAt _ (Here _ _) = Nothing
  {-#INLINE projectAt #-}

--------------------------------------------------------------------------------

class (IsAt (Position f fs) f fs) => Elem f fs where
  inject  :: Lan f r -> Effs fs r
  project :: Effs fs r -> Maybe (Lan f r)

instance (IsAt (Position f fs) f fs) => Elem f fs where
  inject  = injectAt (Index :: Index (Position f fs))
  {-#INLINE inject  #-}
  project = projectAt (Index :: Index (Position f fs))
  {-#INLINE project #-}

--------------------------------------------------------------------------------

scrutinize :: Effs (f ': fs) v -> Sum (Lan f) (Effs fs) v
scrutinize (Here fx out)  = InL (Lan fx out)
scrutinize (There v) = InR v
{-#INLINABLE scrutinize #-}



