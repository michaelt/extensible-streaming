{-#LANGUAGE RankNTypes, TypeOperators, DataKinds, FlexibleContexts #-}
module Streaming.Extensible 
 ( Effects
 , liftEff
 , runEffects
 , handle
 , effectFold
 , expose
 , unexpose
 , exposeFunctor
 , iterF
 , yield_
 , module Streaming
 , module Data.Functor.Effs
  ) where 
import Streaming
import qualified Streaming.Internal as S
import qualified Streaming.Prelude as S
import Data.Functor.Effs

{- | An item of type @Effects fs m r@ is basically a free monad over @fs@, 
     a list or sum of effects: 
     @fs :: [* -> *]@ . Using familiar expedients, we arranged that though 
     the individual types listed need not be functors, the sum of them 
     @Eff fs@ must be. So @Stream (Eff fs) m@ is also a monad if @m@ is. 

     Thus it might be that by accumulating effects in a do-block 
     you end up with something that might be rendered concrete as

> type MyEffects = [State Int, Twitter, Of String, Reader Config, State String]

     In fact one would rarely use such a signature, but use a system of classes
     which record that these effects are present in the sum, without committing 
     oneself to order, and permitting it to be fused with programs with 
     different effects. Concretization arises as we approach the moment of 
     \"interpretation\". 

     Such an item (like anything of type @Stream f m r@) can be viewed as 
     a coroutine with 'm' as the ambient monad. Here the 
     the progress of events in the underlying succession is broken up or \'suspended\'
     by different \'effects\' in @fs@. These are \"handled\"  by being somehow
     mapped down into the ambient flow of events (which may of course be 'Identity').

     @Effects@  is a type synonym. One should know better, but the expansion is fairly
     intelligible in error messages. Everything we say maps immediately to 
     @FreeT (Effs fs) m r@ from the 
     <http://hackage.haskell.org/package/free-4.12.1/docs/Control-Monad-Trans-Free.html free> library and 
     @Coroutine (Effs fs) m r@ from the 
     <http://hackage.haskell.org/package/monad-coroutine-0.9.0.1/docs/Control-Monad-Coroutine.html monad-coroutine>
     library, or one of the other equivalents. 
     So modules like @Data.Functors.Effs@ should properly 
     be independent of any particular implementation of effectful free monads or
     coroutines. 
     
-}
type Effects fs m = Stream (Effs fs) m


{- | The effects stored in an @Effs@ sum needn't be functors,
     but are effectively \'functorized\' by an equivalent of

> data Lan f r = forall x . Lan (f x) (x -> r) 

     i.e.

> data UnGADT f r = forall x . UnGADT (f x) (x -> r)


     which always has a functor instance no matter how trashy f is.

     So our standard way of lifting an effect into a stream of many effects
     has that stereotyped form of @liftEff@  So, for example, taking a right-strict pair
     @Of a r@ to represent the @yield@ statement, whe might write:

> yield x = liftEff (x :> ()) id

     rather than, say

> yield x = liftF (x :> ())

     as we would with e.g. @Control.Monad.Free@  Similarly, given

> data State s r where
>   Get :: State s s
>   Put :: a -> State s ()

    which is /way/ not a functor, we would write

> get = liftEff Get id 
> put s = liftEff (Put s) (\() -> ())

     Now we are ready to use sensible looking combinators in an extensible do-block.

> incr_both = do
>  n <- get
>  put (succ n :: Int)
>  m <- get
>  put (succ m :: Integer)

     Here we are collecting state under two headings, @Int@ and @Integer@. Note
     the necessity of forcing line-by-line monomorphism, which is characteristic
     of all \"extensible effects\" approaches.
     
     Each interpreter, in collapsing such a stream, must also reckon with the fact 
     that the individual effects need not have functor instances. 
-}

liftEff :: (Monad m, At f (Position f fs) fs) 
         => f x 
         -> (x -> r) 
         -> Effects fs m r
liftEff fx out = yields (inject (Lan fx out))
{-#INLINE liftEff #-}


{- | When we have \'handled\' the various effects in a complex
     stream of effects, e.g. @[State Int, Twitter, Of String, Reader Int]@ we
     are still left with the window-dressing. The type @Effects [] m r@ ensures that
     no \'effects\' remain \'suspended\' in the ambient monad. 
     With @runEffects@ we dissolve back into the primordial flux 
     from which we emerged, whatever that flux may be.

-}
runEffects :: Monad m => Effects '[] m r -> m r
runEffects str = do
  e <- inspect str
  case e of
    Left r -> return r
    Right _ -> error "empty union has elements?"
{-#INLINE runEffects #-}
    
-- for example:
yield_ :: (Monad m, Elem (Of a) fs) =>  a -> Effects fs m ()
yield_ x = liftEff (x:> ()) id
{-#INLINE yield_ #-}


{-|  @handle@ is an omnibus right fold over a particular effect in a stream of effects,
     eliminating the particular effect from the progress of effects;
     The crucial third \"algebra\" argument has a rank 2 type.
-}
handle
   :: Monad m
   => (r -> Effects fs m s)
   -> (forall x . f x -> (x -> Effects fs m s) -> Effects fs m s)
   -> Effects (f ': fs) m r
   -> Effects fs m s
handle a b c = effectFold a effect (\(Lan fx o) -> b fx o) c
{-#INLINE handle #-}

{-|  @effectFold@ is an omnibus right fold over a particular effect in a stream of effects;
     compare 'Streaming.streamFold' . The crucial third \"algebra\" argument is here
     protected by a 'Lan' constructor, which is sometimes a bit easier to get past
     the type checker.
-}
effectFold
  :: (Monad m)
   => (r -> Effects fs m s)
   -> (m (Effects fs m s) -> Effects fs m s)
   -> (Lan f (Effects fs m s) -> Effects fs m s)
   -> Effects (f ': fs) m r
   -> Effects fs m s
effectFold done_ effect_ construct_ = loop where
  loop stream = case stream of
    S.Return r  -> done_ r
    S.Effect m  -> effect_ (liftM loop m)
    S.Step u   -> case scrutinize u of
      InL f  -> construct_ (fmap loop f)
      InR fs -> S.Step (fmap loop fs)
{-#INLINABLE effectFold #-}
      
{- | @expose@ removes an effect from the flood of events making it possible
     to operate on the stream of steps of that effect 

-}

expose :: (Monad m)
       => Effects (f ': fs) m r
       -> Stream (Lan f) (Effects fs m) r
expose = loop where
  loop str = do
    e <- lift $ lift $ inspect str
    case e of
      Left r -> return r
      Right u -> case scrutinize u of
        InL f -> do
          rest <- yields f
          loop rest
        InR fs' -> effect $ yields (fmap loop fs')
{-#INLINABLE expose #-}
{- | If an effect in your sum of effects happens to have a @Functor@ instance,
     draw it to the surface, treating the narrower stream of effects as
     the ambient monad, with steps of the form 'f' suspended in it.  
     
     
     Given an item of type 
     
> Effects (f ': fs) m r
     
     all monad-general functions of a type like 

> c m => Stream f m r -> m (Of String r)
        
     can then be applied, giving a result of type 

> c m => Effects fs m (Of String r) 

     This holds where @c = Monad@ in which case the function is pure, but
     also where @c@ is a property that 'Stream f m' inherits from 'm', e.g. 
     @MonadIO@, @MonadState@, @MonadResource@ and on and on. 
 -}
exposeFunctor  :: (Monad m, Functor f)
  => Effects (f ': fs) m r
  -> Stream f (Effects fs m) r
exposeFunctor = loop where
  loop str = do
    e <- lift $ lift $ inspect str
    case e of
      Left r -> return r
      Right u -> case scrutinize u of
        InL (Lan fx out) -> do
          rest <- yields (fmap out fx)
          loop rest
        InR fs' -> effect $ yields (fmap loop fs')
{-#INLINABLE exposeFunctor #-}
{- | Given a stream of effects broken up by steps that actually have a @Functor@ instance, 
     sink these steps into the general stream of effects
-}
unexpose
  :: (Monad m, Functor f, At f (Position f fs) fs) =>
     Stream f (Effects fs m) r -> Effects fs m r
unexpose = run . maps (\f -> liftEff f id)
{-#INLINE unexpose #-}


iterF :: (Monad m, Functor f)
      => (f (Effects fs m r) -> Effects fs m r)
      -> Effects (f ': fs) m r -> Effects fs m r
iterF op = handle return (\fx o -> op (fmap o fx))
{-#INLINE iterF #-}

