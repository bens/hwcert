{-# LANGUAGE Rank2Types #-}

module Graph where

import           Control.Arrow (first, (<<<))
import           Control.Monad.State
import qualified Data.Map as M
import           Data.Map (Map)
import qualified Data.Set as S
import           Data.Set (Set)

class Signals a where
    sigO :: a
    sigI :: a
    nand :: a -> a -> a
    bind :: a -> (a -> a) -> a

newtype Node = N Integer deriving Eq
instance Show Node where
    show (N n) = show n

type St = (Node, Map Integer [Node])

getNext :: State St Node
getNext = do
    (N n, mapping) <- get
    put (N (succ n), M.insertWith (++) n [] mapping)
    return (N n)

(==>) :: Node -> Node -> State St ()
N from ==> to = do
    (n, mapping) <- get
    put (n, M.insertWith (++) from [to] mapping)

newtype G = G { unG :: State St Node }

instance Signals G where
    sigO = G getNext
    sigI = G getNext
    nand (G x) (G y) = G $ do
        [a,b,c] <- sequence [x,y,getNext]
        mapM_ (c ==>) [a,b]
        return c
    bind x f = G $ unG . f . G . return =<< unG x

graph :: (forall s. (Signals s) => s) -> [(Node, [Node])]
graph x = nodify $ runState (unG x) (N 0, M.empty)
    where nodify = map (first N) . M.toList . snd . snd

test1 :: Signals s => s
test1 = bind sigO (\n -> n `nand` n)

test2 :: Signals s => s
test2 = bind test1 (\m -> bind (nand m m) (\n -> nand n (nand n n)))
