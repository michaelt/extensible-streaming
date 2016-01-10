{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
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
glued together, both taking particular forms. 

It is the experience of this library-writer that type-aligned device is 
very expensive. Where programs are written in properly streaming style, 
nothing whatever is to be gained by it.


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
data Tag (fs ::[* -> *]) = Tag

type family Position (f :: * -> *) fs :: Nat where
  Position f (f ': fs)  = 'Z
  Position f (x ': fs)  = 'S (Position f fs)

--------------------------------------------------------------------------------

data Effs (fss :: [ * -> * ]) v where
  Here  :: forall f fs x v . !(f x) -> (x -> v) -> Effs (f ': fs) v
  There :: !(Effs fs v)    -> Effs (f ': fs) v

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
data Lan f r = forall x . Lan !(f x) (x -> r)
instance Functor (Lan f) where 
  fmap f (Lan fx out) = Lan fx (f . out)
  {-#INLINE fmap #-}

--------------------------------------------------------------------------------

class At f (n :: Nat) fs where
  injectAt  :: Index n -> Lan f r -> Effs fs r
  projectAt :: Index n -> Effs fs r -> Maybe (Lan f r)

instance (fs ~ (f ': fs')) => At f 'Z fs  where
  injectAt Index  (Lan f out)  = Here f out
  {-#INLINE injectAt #-}
  projectAt Index (Here x out) = Just (Lan x out)
  projectAt _ _                = Nothing
  {-#INLINE projectAt #-}

instance (fs ~ (f' ': fs'), At f n fs') => At f ('S n) fs  where
  injectAt Index  f          = There (injectAt (Index :: Index n) f)
  {-#INLINE injectAt #-}
  projectAt Index (There x)  = projectAt (Index :: Index n) x
  projectAt Index (Here _ _) = Nothing
  {-#INLINE projectAt #-}

--------------------------------------------------------------------------------

class (At f (Position f fs) fs) => Elem f fs where
  inject  :: Lan f r -> Effs fs r
  project :: Effs fs r -> Maybe (Lan f r)

instance (At f (Position f fs) fs) => Elem f fs where
  inject = injectAt (Index :: Index (Position f fs))
  {-#INLINE inject  #-}
  project = projectAt (Index :: Index (Position f fs))
  {-#INLINE project #-}

--------------------------------------------------------------------------------

scrutinize :: Effs (f ': fs) v -> Sum (Lan f) (Effs fs) v
scrutinize (Here fx out)  = InL (Lan fx out)
scrutinize (There v) = InR v
{-#INLINABLE scrutinize #-}

-- -----------------------------------------------------------------------------
-- Various utilities for mapping over particular Effs
-- -----------------------------------------------------------------------------


eitherEff :: (forall x . f x -> g x) 
          -> (forall x . Effs fs x -> Effs gs x)
          -> Effs (f ': fs) r 
          -> Effs (g ': gs) r
eitherEff phi psi (Here f out) = Here (phi f) out
eitherEff phi psi (There rest) = There (psi rest)

mapHere :: (forall x . f x -> g x) -> Effs (f ': fs) r -> Effs (g ': fs) r
mapHere phi = eitherEff phi id 

mapThere :: (forall x . Effs fs x -> Effs gs x) -> Effs (f ': fs) r -> Effs (f ': gs) r
mapThere phi = eitherEff id phi

forEff :: Effs (f ': fs) r -> (forall x . f x -> Effs fs x) ->  Effs fs r
forEff e phi = loop e where
  loop effs = case effs of
    Here f out -> fmap out (phi f)
    There e    -> e

effMap :: Elem g fs => (forall x . f x -> g x) -> Effs (f ': fs) r -> Effs fs r
effMap phi = loop where
  loop effs = case effs of 
    Here f out -> inject (Lan (phi f) out)
    There e    -> e




