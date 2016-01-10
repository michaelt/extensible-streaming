# extensible-streaming

It is an apriori of the extensible effects campaign that we are trying to avoid monad transformers. 

But why would I want to resist monad transformers? 

On the other hand, though, what could be more pleasing than to work with an extensible sum of functors? The `Effs fs` defined here is such a sum, implemented more or less following the `freer` package. 

Actually, the items in `Effs fs` needn't be functors, nevertheless, by familiar tricks, `Eff fs` always is, and so we can stream such a bouquet of effects as we please. 

There isn't any need for a special extensible effects library, in particular for a special monad. We just need a sum-of-functors (or rather -non-functors) functor containing `scrutinize` and `inject` to put things into the sum and extract them.  And then we need a few combinators, like `liftEff` and `runEffects` and `foldEffect` to help with the construction of proper effects and with folding over the stream of them.  

It is the experience of this writer - perhaps I got something wrong - that `type-aligned` is of value only where one is operating with a functor that splits, like 

    data Arith a = Plus a a | Times a a
    
then for sure you will use a right fold from the leaves in interpreting, and there is no hope of streaming. Where you are using functors that admit streaming, and comprehend the discipline of properly streaming program composition, it is generally a loss. (Similarly, I think there is no reason to use `Data.Sequence` and engage in elaborate construction of a `Seq` if you are proposing a strict left fold over the elements as they come.) In streaming program composition, especially with a transformer like `FreeT` `Stream` or `Coroutine`, one systematically avoids "re-traversing binds", and retaining references to items extracted, and accumulation in general. Everything must be destroyed as soon as it is created.

Whatever the merits of those remarks, here is a silly test program exhibiting the prompt definition of a few effects, summing them together in a single `do` block and running them together:



    {-# LANGUAGE GADTs #-}
    {-# LANGUAGE TypeFamilies #-}
    {-# LANGUAGE TypeOperators #-}
    {-# LANGUAGE DataKinds, PolyKinds #-}
    {-# LANGUAGE ScopedTypeVariables #-}
    {-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

    module Main (main) where
    import Streaming
    import qualified Streaming.Internal as S
    import qualified Streaming.Prelude as S
    import Streaming.Extensible
    import Control.Monad
    import Data.Function ((&))
    main =  do
        let effects = do
             yield "I am a String; I was yielded"
             n <- get 
             tweet ("Hey Twitter, I used `get` and got an Int: " ++ show n)
             put (n+1 ::Int)
             yield ("I am a pair of a String and an Int, and was yielded",12::Int)
             n <- get 
             tweet ("Hey Twitter, I used `get` and got an Integer this time: " ++ show n)
             put (n+1 ::Integer)
             liftIO $ print "<<<Hi, this is a shameless debug message coming from IO >>>"
        effects
        effects
   
      & ioTweetInterpreter                   -- render Tweets to stdout
      & runState (2::Integer)                -- initialize Integer state
      & runState (2::Int)                    -- initialize Int state
      & S.stdoutLn' . exposeYieldsAt ""      -- interpret yields at String
      & S.print . exposeYieldsAt ("",0::Int) -- interpret yields at (Int,String)
      & runEffects                           -- kill vestigial wrapping
      
    -- >>> main
    -- I am a String; I was yielded
    -- Hey Twitter, I used `get` and got an Int: 2
    -- ("I am a pair of a String and an Int, and was yielded",12)
    -- Hey Twitter, I used `get` and got an Integer this time: 2
    -- "<<<Hi, this is a shameless debug message coming from IO >>>"
    -- I am a String; I was yielded
    -- Hey Twitter, I used `get` and got an Int: 3
    -- ("I am a pair of a String and an Int, and was yielded",12)
    -- Hey Twitter, I used `get` and got an Integer this time: 3
    -- "<<<Hi, this is a shameless debug message coming from IO >>>"
    -- (4,(4,()))
    -- *Main
    --
      
    --------------------
    -- `tweet` effect
    -------------------- 

    data Twitter a where 
      Twitter :: String -> Twitter ()

    tweet str = liftEff (Twitter str) (\() -> ()) 

    tweets = do
      tweet "extensible"
      tweet "effects"


    handleTweets
       :: (Monad m)  => (String -> m ()) -> Effects (Twitter ': fs) m r -> Effects fs m r
    handleTweets act = foldEffect return effect go where
      go (Lan (Twitter str) out)  = lift (act str) >> out ()

    exposeTweets 
      :: Monad m => Effects (Twitter ': fs) m r -> Stream (Of String) (Effects fs m) r
    exposeTweets = maps (\(Lan (Twitter s) out) -> (s :> out ()) ) . expose

    ioTweetInterpreter = handleTweets (liftIO . putStrLn)
    pureTweetInterpreter = S.toList . exposeTweets


    --------------------------
    -- `get` and `put` effects
    -------------------------- 
    data State s r where
      Get :: State s s
      Put :: s -> State s ()

    get :: (Monad m, Elem (State s) fs) => Effects fs m s
    get = liftEff Get (\s -> s)

    put :: (Monad m, Elem (State s) fs) => s -> Effects fs m ()
    put s = liftEff (Put s) (\() -> ())

    runState
        :: Monad m =>
           s -> Stream (Effs (State s ': fs)) m r -> Stream (Effs fs) m (s,r)
    runState = loop where
      loop :: Monad m => s -> Stream (Effs (State s ': fs)) m r -> Stream (Effs fs) m (s,r)
      loop s str = do
        e <- lift $ inspect str
        case e of
          Left r -> return (s,r)
          Right fs -> case scrutinize fs of
            InL (Lan (Put s) out) -> loop s (out ()) 
            InL (Lan Get out)     -> loop s (out s)
            InR fs -> S.Step (fmap (loop s) fs)
              
    --------------------
    -- `yield` effect
    --------------------             

    -- we just yield with `Of a r` from Streaming.Prelude

    yield :: (Monad m, Elem (Of a) fs) =>  a -> Effects fs m ()
    yield x = liftEff (x:> ()) id  -- compare Streaming.yield x = wrap (x :> id)
    
    exposeYields  :: (Monad m)
      => Effects (Of a ': fs) m r
      -> Stream (Of a) (Effects fs m) r
    exposeYields = exposeFunctor

    exposeYieldsAt  :: (Monad m)
      => a -> Effects (Of a ': fs) m r
      -> Stream (Of a) (Effects fs m) r
    exposeYieldsAt a = exposeFunctor    
              
