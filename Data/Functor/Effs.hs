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
nothing whatever is to be gained by it. But who knows?

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

module Data.Functor.Effs (
   Effs (..)
   , Lan (..)
   , At (..)
   , Place (..)
   , Elem (..)
   , scrutinize
   , mapHere
   , mapThere
   , eitherEff
   , forEff
   , effMap
   ) where

import Data.Functor.Sum
--------------------------------------------------------------------------------
                         -- Implementation --
--------------------------------------------------------------------------------

data Nat = S Nat | Z
data Index (n :: Nat) = Index
data Token (f :: * -> *) = Token
data Tag (fs ::[* -> *]) = Tag

type family Place (f :: * -> *) fs :: Nat where
  Place f (f ': fs)  = 'Z
  Place f (x ': fs)  = 'S (Place f fs)

--------------------------------------------------------------------------------

data Effs (fss :: [ * -> * ]) v where
  Here  :: forall f fs x v . !(f x) -> (x -> v) -> Effs (f ': fs) v
  There :: !(Effs fs v)    -> Effs (f ': fs) v

instance Functor (Effs fs) where
  fmap f (Here fa out)  = Here fa (f . out)
  fmap f (There fs) = There (fmap f fs)
  {-#INLINE fmap #-}

{- | Lan generalizes the device by which @Effs@ is a functor,
     wrapping anything of kind @*->*@ in the form of a functor,
     by so to speak accumulating fmaps. (It is @Lan Identity@ in the sense
     of the 
     <https://hackage.haskell.org/package/kan-extensions-4.2.3/docs/Data-Functor-Kan-Lan.html#t:Lan kan-extensions>
     library; we are following the remarks of Oleg in the paper on
     <http://okmij.org/ftp/Haskell/extensible/more.pdf \"freer\" monads>.) 
     Thus see the type of 'scrutinize' and 'project'

> scrutinize :: Effs (f ': fs) v -> Sum (Lan f) (Effs fs) v
> project :: Effs fs r -> Maybe (Lan f r)
  
     which are used in place of a direct pattern match when 
     writing recursive loops  over a stream with many 
     non-functor effect steps \'suspended\' in it.
  -}
  
data Lan f r = forall x . Lan !(f x) (x -> r)

instance Functor (Lan f) where 
  fmap f (Lan fx out) = Lan fx (f . out)
  {-#INLINE fmap #-}

--------------------------------------------------------------------------------
{- | The @At f n fs@ constraint is satified when f is the n\'th type
     in a type-level list of types. Saying that

> At f n fs
 
     is a bit like saying

> fs !! f == n


     When f is permitted by having that position, we can @inject@
     an item of that type into the sum. That is, 

> injectAt n (Lan fx id) 

    is a bit like @Left@ or @Either@ (or rather @InL@ or @InR@). 

-}
class At (n :: Nat) f fs where
  injectAt  :: Index n -> Lan f r -> Effs fs r
  projectAt :: Index n -> Effs fs r -> Maybe (Lan f r)

instance (fs ~ (f ': fs')) => At 'Z f fs  where
  injectAt Index (Lan f out)   = Here f out
  {-#INLINE injectAt #-}
  projectAt Index (Here x out) = Just (Lan x out)
  projectAt _ _                = Nothing
  {-#INLINE projectAt #-}

instance (fs ~ (f' ': fs'), At n f fs') => At ('S n) f fs  where
  injectAt Index  f          = There (injectAt (Index :: Index n) f)
  {-#INLINE injectAt #-}
  projectAt Index (There x)  = projectAt (Index :: Index n) x
  projectAt Index (Here _ _) = Nothing
  {-#INLINE projectAt #-}

--------------------------------------------------------------------------------
{- | @Elem f fs@ says that f is one of the functors in the sum @fs@
     In addition to using its methods the class will frequently 
     appear in user-written constraints. In error messages and type queries,
     however, its constraint is more commonly seen:

>    At f (Place f fs) fs

     This means something like

>    fs !! Place f fs == f

     or \"f is at (the place of f in the fs) in the fs\" which is 
     how we say that it is one of the possibilities, i.e. that @Elem f fs@

-}
class (At (Place f fs) f fs) => Elem f fs where
  inject  :: Lan f r -> Effs fs r
  project :: Effs fs r -> Maybe (Lan f r)

instance (At (Place f fs) f fs) => Elem f fs where
  inject = injectAt (Index :: Index (Place f fs))
  {-#INLINE inject  #-}
  project = projectAt (Index :: Index (Place f fs))
  {-#INLINE project #-}

--------------------------------------------------------------------------------

{- | @scrutinize@, called @decomp@ in @freer@ ,
     gives more help to the type checker than directly 
     pattern matching on 'Here' and 'There'. So we shall

>  loop stream = do 
>     e <- inspect stream                    -- run the underlying effect until
>     case e of
>        Left r -> return r                  -- we either come to the end
>        Right eff -> case scrutinize eff of -- or meet a break; 
>           InL (Lan fx out) -> ...          -- if it is the leftmost 'functor', ...
>           InR other        -> ...          -- else ...
-}
scrutinize :: Effs (f ': fs) v -> Sum (Lan f) (Effs fs) v
scrutinize (Here fx out)  = InL (Lan fx out)
scrutinize (There v) = InR v
{-#INLINE scrutinize #-}

-- -----------------------------------------------------------------------------
-- Various utilities for mapping over particular Effs
-- -----------------------------------------------------------------------------
{- | @eitherEff@ is a remote analogue of Prelude.either 

-}
eitherEff :: (forall x . f x -> g x) 
          -> (forall x . Effs fs x -> Effs gs x)
          -> Effs (f ': fs) r 
          -> Effs (g ': gs) r
eitherEff phi psi (Here f out) = Here (phi f) out
eitherEff phi psi (There rest) = There (psi rest)


-- | Map over the first functor-like possibility
mapHere :: (forall x . f x -> g x) -> Effs (f ': fs) r -> Effs (g ': fs) r
mapHere phi = eitherEff phi id 

-- | Map over the rest of the possibilities, en masse.
mapThere :: (forall x . Effs fs x -> Effs gs x) -> Effs (f ': fs) r -> Effs (f ': gs) r
mapThere phi = eitherEff id phi


-- | Eliminate the first possibility by assimilating it to the others.
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




