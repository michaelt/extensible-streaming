# extensible-streaming

It is an apriori of the extensible effects advertisement campaign that we are trying to avoid
monad transformers. But why would I want to resist monad transformers? On the other hand, though, what could be more pleasing than to work with an extensible sum of functors? -- like the `Eff fs` defined here, more or less following the `freer` package. Actually, the items in `Eff fs` needn't be functors, nevertheless, by familiar tricks, `Eff fs` always is, and so we can stream such a bouquet of effects as we please:


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
       :: (Monad m)
       => (String -> m ())
       -> Effects (Twitter ': fs) m r
       -> Effects fs m r
    handleTweets act = effectFold return effect go where
      go (Lan (Twitter str) out)  = lift (act str) >> out ()

    exposeTweets 
      :: Monad m 
      => Effects (Twitter ': fs) m r 
      -> Stream (Of String) (Effects fs m) r
    exposeTweets = maps (\(Lan (Twitter s) out) -> (s :> out ()) ) . expose

    insertTweets 
       :: (Monad m, Elem Twitter fs) 
       => Stream (Of String) (Effects fs m) r 
       -> Effects fs m r
    insertTweets stream = run $ S.with stream tweet

    ioTweetInterpreter = handleTweets (liftIO . putStrLn)
    pureTweetInterpreter = S.toList . exposeTweets
    comment n str = insertTweets 
                  . intercalates (S.yield str) 
                  . chunksOf n 
                  . exposeTweets


    --------------------------
    -- `get` and `put` effects
    -------------------------- 
    data State s r where
      Get :: State s s
      Put :: s -> State s ()

    get :: (Monad m, Elem (State s) fs) => Effects fs m s
    get = liftEff Get id 

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

    yield :: (Monad m, Elem (Of a) fs) =>  a -> Effects fs m ()
    yield x = liftEff (x:> ()) id
    
    exposeYields  :: (Monad m)
      => Effects (Of a ': fs) m r
      -> Stream (Of a) (Effects fs m) r
    exposeYields = exposeFunctor

    exposeYieldsAt  :: (Monad m)
      => a -> Effects (Of a ': fs) m r
      -> Stream (Of a) (Effects fs m) r
    exposeYieldsAt a = exposeFunctor    
              
