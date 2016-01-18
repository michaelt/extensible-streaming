# extensible-streaming

It is an apriori of the extensible effects campaign that we are trying to avoid monad transformers. 

But why would I want to resist monad transformers? 

On the other hand, though, what could be more pleasing than to work with an extensible sum of functors? The `Effs fs` defined here is such a sum, implemented more or less following the `freer` package. 

Actually, the items in `Effs fs` needn't be functors, nevertheless, by familiar tricks, `Eff fs` always is, and so we can stream such a bouquet of effects as we please. 

There isn't any need for a special extensible effects library, in particular for a special monad. We just need a sum-of-functors (or rather -non-functors) functor containing `scrutinize` and `inject` to put things into the sum and extract them.  Such a thing should be put alongside e.g. `Data.Functor.Sum` in the `transformers` library, or something like that. Then any construction anywhere that can make use of a functor constraint can make use of this sort of sum or union of functors and quasi-functors.  Here, we are using `Stream f m r`, and just need a few combinators, like `liftEff` and `runEffects` and `foldEffect` to help with the construction of proper effects and with folding over the stream of them.  

It is the experience of this writer - perhaps I got something wrong - that `type-aligned` is of value only where one is operating with a functor that splits, like 

    data Arith a = Plus a a | Times a a
    
then for sure you will use a right fold from the leaves in interpreting, and there is no hope of streaming. Where you are using functors that admit streaming, and comprehend the discipline of properly streaming program composition, it is generally a loss. (Similarly, I think there is no reason to use `Data.Sequence` and engage in elaborate construction of a `Seq` if you are proposing a strict left fold over the elements as they come.) In streaming program composition, especially with a transformer like `FreeT` `Stream` or `Coroutine`, one systematically avoids "re-traversing binds", and retaining references to items extracted, and accumulation in general. Everything must be destroyed as soon as it is created.

Whatever the merits of those remarks, here is a simple test program exhibiting the convenient definition of a few effects, summing them together in a single `do` block and running them together. It 

- maintains two different internal state calculations, one for Int, one for Integer
- tweets occasional nonsense
- yields both Strings and (Int,String) pairs
- makes http get and post requests

the "interpreters" then put perfectly trivial interpretations on these 'effects'

    {-# LANGUAGE GADTs #-}
    {-# LANGUAGE TypeFamilies #-}
    {-# LANGUAGE TypeOperators #-}
    {-# LANGUAGE DataKinds, PolyKinds #-}
    {-# LANGUAGE ScopedTypeVariables #-}
    {-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

    module Main (main) where
    import Streaming
    import Streaming.Extensible
    import qualified Streaming.Prelude as S
    import Control.Monad
    import Data.Function ((&))
    import qualified Data.Map as M

    main =  do
        let effects = do
             yield "I am a String; I was yielded."
             n <- get 
             tweet ("Tweet: I used `get` and got an Int: " ++ show n)
             _PUT "comments" "Nice comment page."
             bytes <- _GET "comments"
             tweet ("Tweet: Check out this comments page I read: " ++ show bytes)
             put (n+1 ::Int)
             yield ("I am a (String, Int) pair, and was yielded: ",n+1::Int)
             n <- get 
             _PUT "comments" $ "I just got the number " ++ show n
             put (n+1 ::Integer)
        effects
        effects

      & pureHttp site                        
      & ioTweetInterpreter                   -- render Tweets to stdout
      & runState (2::Integer)                -- initialize Integer state
      & runState (2::Int)                    -- initialize Int state
      & S.stdoutLn' . extrudeYieldsAt ""      -- interpret yields at String
      & S.print . extrudeYieldsAt ("",0::Int) -- interpret yields at (Int,String)
      & runEffects                           -- kill vestigial wrapping
      & (>>= io)
     where
      io (int,(integer,(site,()))) = do
        putStrLn "\n-------\nFinished\n-------"
        putStr "Final Int state:  "
        print int
        putStr "Final Integer state:  "
        print integer
        putStrLn "Current site: "
        mapM_ print (M.toList site)
    
    -- >>> main
    -- I am a String; I was yielded.
    -- Tweet: I used `get` and got an Int: 2
    -- Tweet: Check out this comments page I read: "Nice comment page."
    -- ("I am a (String, Int) pair, and was yielded: ",3)
    -- I am a String; I was yielded.
    -- Tweet: I used `get` and got an Int: 3
    -- Tweet: Check out this comments page I read: "Nice comment page.\nI just got the number 2\nNice comment page."
    -- ("I am a (String, Int) pair, and was yielded: ",4)
    --
    -- -------
    -- Finished
    -- -------
    -- Final Int state:  4
    -- Final Integer state:  4
    -- Current site:
    -- ("comments","Nice comment page.\nI just got the number 2\nNice comment page.\nI just got the number 3")
    -- ("welcome","hello")


    --------------------
    -- `tweet` effect
    -------------------- 

    data Twitter a where 
      Twitter :: String -> Twitter ()

    tweet str = liftEff (Twitter str) (\() -> ()) 


    handleTweets :: (Monad m)  => (String -> m ()) -> Effects (Twitter ': fs) m r -> Effects fs m r
    handleTweets act = mapMEffect $ \(Lan (Twitter str) out) -> act str >> return (out ())


    extrudeTweets 
      :: Monad m => Effects (Twitter ': fs) m r -> Stream (Of String) (Effects fs m) r
    extrudeTweets = maps (\(Lan (Twitter s) out) -> (s :> out ()) ) . extrudeLan

    ioTweetInterpreter = handleTweets (liftIO . putStrLn)
    pureTweetInterpreter = S.toList . extrudeTweets


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

    runState :: Monad m => s -> Stream (Effs (State s ': fs)) m r -> Stream (Effs fs) m (s,r)
    runState = loop where
      loop :: Monad m => s -> Stream (Effs (State s ': fs)) m r -> Stream (Effs fs) m (s,r)
      loop s str = do
        e <- lift $ inspect str
        case e of
          Left r -> return (s,r)
          Right fs -> case scrutinize fs of
            InL (Lan (Put s) out) -> loop s (out ()) 
            InL (Lan Get out)     -> loop s (out s)
            InR fs                -> wrap (fmap (loop s) fs)

    -- runState' :: Monad m => s -> Stream (Effs (State s ': fs)) m r -> Stream (Effs fs) m (s,r)

    --------------------
    -- `yield` effect
    --------------------             

    -- we just yield with `Of a r` from Streaming.Prelude

    yield :: (Monad m, Elem (Of a) fs) =>  a -> Effects fs m ()
    yield x = liftEff (x:> ()) id  -- compare Streaming.yield x = wrap (x :> id)

    extrudeYields  :: (Monad m)
      => Effects (Of a ': fs) m r
      -> Stream (Of a) (Effects fs m) r
    extrudeYields = extrude

    extrudeYieldsAt  :: (Monad m)
      => a -> Effects (Of a ': fs) m r
      -> Stream (Of a) (Effects fs m) r
    extrudeYieldsAt a = extrude 


    --------------------
    -- HTTP effects
    --------------------      

    type Bytes = String
    type Path = String

    data Http a where -- compare to the 'normal' (functor) type in http://degoes.net/articles/modern-fp/
      GET :: Path -> Http Bytes
      PUT :: Path -> Bytes -> Http Bytes
      POST :: Path -> Bytes -> Http Bytes
      DELETE :: Path -> Http Bytes

    _GET :: (Monad m, Elem Http fs) => Path -> Effects fs m Bytes
    _GET path = liftEff (GET path) id 

    _PUT :: (Monad m, Elem Http fs) =>
         Path -> Bytes -> Effects fs m Bytes
    _PUT path bytes = liftEff (PUT path bytes) id

    _POST :: (Monad m, Elem Http fs) =>  Path -> Bytes -> Effects fs m Bytes
    _POST path bytes = liftEff (POST path bytes) id

    _DELETE :: (Monad m, Elem Http fs) => Path -> Effects fs m Bytes
    _DELETE path = liftEff (DELETE path) id

    site = M.fromList [("welcome","hello")]

    -- this in dire need of a combinator ...
    pureHttp = loop where
      loop :: Monad m   -- the type signature is needed here
            => M.Map Bytes Bytes 
            -> Stream (Effs (Http ': fs)) m r 
            -> Stream (Effs fs) m (M.Map Bytes Bytes,r)
      loop m str = do
        e <- lift $ inspect str
        case e of
          Left r -> return (m, r)
          Right fs -> case scrutinize fs of
            InL (Lan (GET p) out) -> case M.lookup p m of
              Nothing -> loop m (out "404") 
              Just b  -> loop m (out b) 
            InL (Lan (POST p b) out) -> loop (M.insert p b m) (out $ "posted " ++ p) 
            InL (Lan (DELETE p) out) -> case M.lookup p m of
              Nothing -> loop m (out $ p ++ " doesn't exist")
              Just b  -> loop (M.delete p m) (out $ "deleted" ++ p)
            InL (Lan (PUT p b) out)  -> case M.lookup "comments" m of
              Nothing -> loop (M.insert "comments" b m) (out "comments page created")
              Just a  -> loop (M.insert "comments" (a++"\n" ++ b) m) (out "comment added")
            InR fs                   -> wrap (fmap (loop m) fs)
    


