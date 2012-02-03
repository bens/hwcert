{-# LANGUAGE Rank2Types #-}

module Graph where

import           Control.Arrow (first, (<<<))
import           Control.Monad.State
import qualified Data.Map as M
import           Data.Map (Map)
import qualified Data.Set as S
import           Data.Set (Set)

-- Abstract signals class.
class Signals a where
    sigO, sigI :: a            -- constants
    nand :: a -> a -> a        -- not-and, the one binary operator
    bind :: a -> (a -> a) -> a -- explicit sharing

newtype Node = N Integer deriving Eq
instance Show Node where
    show (N n) = show n

type St = (Node, Map Integer [Node])

-- Generate a fresh node.
getNext :: State St Node
getNext = do
    (N n, mapping) <- get
    put (N (succ n), M.insertWith (++) n [] mapping)
    return (N n)

-- Declare a link from one node to another.
(==>) :: Node -> Node -> State St ()
N from ==> to = do
    (n, mapping) <- get
    put (n, M.insertWith (++) from [to] mapping)

-- It's much easier to define the Signals instance on a newtype than a
-- type synonym.
newtype G = G { unG :: State St Node }

instance Signals G where
    sigO = G getNext
    sigI = G getNext
    -- Run the two sub-computations, generate a fresh id, and declare the
    -- links.  Return the fresh id.
    nand (G x) (G y) = G $ do
        [a,b,c] <- sequence [x,y,getNext]
        c ==> a
        c ==> b
        return c
    -- Run the passed computation, then just return its id instead of
    -- re-running it whenever it's used in the function.
    bind x f = G $ unG . f . G . return =<< unG x

graph :: (forall s. (Signals s) => s) -> [(Node, [Node])]
graph x = nodify $ runState (unG x) (N 0, M.empty)
    where nodify = map (first N) . M.toList . snd . snd

-- 0
-- 1 -> 0, 0
test1 :: Signals s => s
test1 = bind sigO (\n -> n `nand` n)

-- 0
-- 1 -> 0, 0
-- 2 -> 1, 1
-- 3 -> 2, 2
-- 4 -> 3, 2
test2 :: Signals s => s
test2 = bind test1 (\m -> bind (nand m m) (\n -> nand n (nand n m)))
