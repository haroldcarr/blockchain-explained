{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies    #-}

module RedBlack where

import Prelude hiding (lookup)

import System.Random
import qualified Data.Map as M

--  Code adapted from:
--  https://www.cs.kent.ac.uk/people/staff/smk/redblack/Untyped.hs
--
--  This Red-Black tree satisfies a weaker invariant than the
--  traditional red-black trees. Nevertheless, after insterting
--  [1..n] randomly, the root of the tree is decently close to
--  n/2 for my taste.

data Color = R | B deriving (Eq , Show)
data RB a
  = E
  | T { color :: Color
      , left  :: RB a
      , value :: a
      , right :: RB a
      }
  deriving (Eq , Show)

-- | Paints a node black
darken :: RB a -> RB a
darken E  = E
darken rb = rb { color = B}

-- | Paints a node red
blush :: RB a -> RB a
blush E = E
blush rb = rb { color = R }

-- | Performs an action if the given node is black
--
rbOnBlack :: (RB a -> RB a) -> RB a -> RB a -> RB a
rbOnBlack f  _ x@(T B _ _ _) = f x
rbOnBlack _ el _             = el

-- | Inserts a node into a RB-tree
rbInsert :: (Ord a) => a -> RB a -> RB a
rbInsert a0 tr = darken (ins a0 tr)
  where
    ins :: (Ord a) => a -> RB a -> RB a
    ins a E = T R E a E
    ins a (T B l k r)
      = case compare a k of
          EQ -> T B l a r
          LT -> rbBalance (ins a l) k r
          GT -> rbBalance l k (ins a r)
    ins a (T R l k r)
      = case compare a k of
          EQ -> T R l a r
          LT -> T R (ins a l) k r
          GT -> T R l k (ins a r)

-- | Perform some balancing magic
rbBalance :: RB a -> a -> RB a -> RB a

rbBalance (T R ll x lr) y (T R rl z rr)
  = T R (T B ll x lr) y (T B rl z rr)

rbBalance (T R (T R lll lx llr) x lr) y r
  = T R (T B lll lx llr) x (T B lr y r)

rbBalance (T R ll x (T R lrl rx lrr)) y r
  = T R (T B ll x lrl) rx (T B lrr y r)

rbBalance l y (T R rl ry (T R rrl rry rrr))
  = T R (T B l y rl) ry (T B rrl rry rrr)

rbBalance l y (T R (T R rll rly rlr) ry rr)
  = T R (T B l y rll) rly (T B rlr ry rr)

rbBalance l y r
  = T B l y r

-- |Deletes a node from a RB tree
rbDelete :: (Ord a) => a -> RB a -> RB a
rbDelete x0 t = darken (del x0 t)
  where
    del :: (Ord a) => a -> RB a -> RB a
    del _ E = E
    del x (T _ l y r)
      = case compare x y of
          EQ -> rbApp l r
          LT -> rbOnBlack (\l' -> rbBalLeft (del x l') y r)
                          (T R (del x l) y r)
                          l
          GT -> rbOnBlack (\r' -> rbBalRight l y (del x r'))
                          (T R l y (del x r))
                          r

rbBalLeft :: RB a -> a -> RB a -> RB a
rbBalLeft (T R ll lx lr) y r = T R (T B ll lx lr) y r
rbBalLeft l y (T B rl rx rr) = rbBalance l y (T R rl rx rr)
rbBalLeft l y (T R (T B rll rlx rlr) rx rr)
  = T R (T B l y rll) rlx (rbBalance rlr rx (blush rr))

rbBalRight :: RB a -> a -> RB a -> RB a
rbBalRight l x (T R rl y rr)  = T R l x (T B rl y rr)
rbBalRight (T B ll x rl) y r = rbBalance (T R ll x rl) y r
rbBalRight (T R ll x (T B rll y rlr)) z r
   = T R (rbBalance (blush ll) x rll) y (T B rlr z r)

rbApp :: RB a -> RB a -> RB a
rbApp E x = x
rbApp x E = x
rbApp (T R ll x lr) (T R rl y rr)
  = case rbApp lr rl of
      T R m n o -> T R (T R ll x m) n (T R o y rr) -- XXX: two reds??
      mno       -> T R ll x (T R mno y rr)
rbApp (T B ll x lr) (T B rl y rr)
  = case rbApp lr rl of
      T R m n o -> T R (T B ll x m) n (T B o y rr)
      mno       -> rbBalLeft ll x (T B mno y rr)
rbApp a (T R b x c) = T R (rbApp a b) x c
rbApp (T R a x b) c = T R a x (rbApp b c)

rbLookup :: (Ord v) => v -> RB v -> Maybe v
rbLookup _ E = Nothing
rbLookup v (T _ l x r)
  = case compare v x of
      EQ -> Just x
      LT -> rbLookup v l
      GT -> rbLookup v r

rbPretty :: (Show v) => RB v -> IO ()
rbPretty = mapM_ putStrLn . draw
  where
    draw :: (Show v) => RB v -> [String]
    draw E                     = []
    draw (T b E v E) = [show b ++ " " ++ show v]
    draw (T b l v r) = (show b ++ " " ++ show v) : drawSubTrees [l , r]
      where
        drawSubTrees [] = []
        drawSubTrees [t] =
            "|" : shift "`- " "   " (draw t)
        drawSubTrees (t:ts) =
            "|" : shift "+- " "|  " (draw t) ++ drawSubTrees ts

        shift first other = zipWith (++) (first : repeat other)

makeTree :: (Ord k) => [ k ] -> RB k
makeTree = foldr rbInsert E

animate :: (Ord k,  Show k) => [k] -> IO ()
animate = aux E
  where
    separate = putStrLn (replicate 40 '#')

    aux :: (Ord k , Show k) => RB k  -> [k] -> IO ()
    aux _ [] = return ()
    aux t (k:ks)
      = do let t' = rbInsert k t
           rbPretty t'
           separate
           aux t' ks

fisherYatesStep :: RandomGen g
                => (M.Map Int a, g) -> (Int, a) -> (M.Map Int a, g)
fisherYatesStep (m, gen) (i, x) = ((M.insert j x . M.insert i (m M.! j)) m
                                  , gen')
  where
    (j, gen') = randomR (0, i) gen

fisherYates :: RandomGen g => [a] -> g -> ([a], g)
fisherYates [] g = ([], g)
fisherYates l g =
  toElems $ foldl fisherYatesStep (initial (head l) g)
                                    (numerate (tail l))
  where
    toElems (x, y) = (M.elems x, y)
    numerate = zip [1..]
    initial x gen = (M.singleton 0 x, gen)

shuffle :: [a] -> IO [a]
shuffle l = getStdRandom (fisherYates l)

insDelTree :: Int -> Int -> IO (RB Int)
insDelTree ins del
  = do ks <- shuffle [1 .. ins]
       let t0 = makeTree ks
       let t  = foldr rbDelete t0 [ins - del..ins]
       return t

test :: Int -> Int -> Int -> IO (RB Int)
test maxtree maxlkups deletes
  = do ks <- shuffle [1 .. maxtree]
       let t0   = makeTree ks
       let t    = foldr rbDelete t0 [1..deletes]
       res <- mapM (testLookup t) (take maxlkups (filter (> deletes) ks))
       if and res
         then putStrLn "!! Success !!"
         else putStrLn "!! Failure !!" >> print ks
       return t
  where
    testLookup :: RB Int -> Int -> IO Bool
    testLookup tr k
      = do let val = rbLookup k tr
           case val of
             Nothing -> putStrLn ("Can't find key: " ++ show k) >> return False
             Just v  -> do putStrLn ("Checking key: " ++ show k ++ " and value: "
                                                                ++ show v)
                           return True
