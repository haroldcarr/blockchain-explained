{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module VerifiedMap where

import Prelude hiding (lookup)

import qualified Codec.Digest.SHA as SHA
import qualified Data.ByteString  as BS
import Data.Proxy
import Data.Serialize
import GHC.Generics

import Control.Monad.Writer
import Control.Monad.Reader

import System.Random
import qualified Data.Map as M

import GHC.Exts (Constraint)

----------------
-- My Prelude --
----------------

split :: (a -> b) -> (a -> c) -> a -> (b , c)
split f g x = (f x , g x)

----------------
----------------
----------------

-- | Easy constraint synonym for us!
type Ser a = (Serialize a , Show a)

-- |The prover 'writes' the proof stream
type Prover w a   = Writer w a

-- |The verifier 'reads' the proof stream produced by the reader.
type Verifier r a = Reader r a


-- Verified Map
-- ############
-- ############

-- |The verified map interface I thought about is:
--
--
class VerifiedMap (m :: * -> * -> *) where
  type Ev  m :: *
  type Dig m :: *
  type Ctr m k v :: Constraint

  -- |Prover end: looking up.
  lkup  :: (Ord k , Ctr m k v) => k -> m k v -> Prover (Ev m) (Maybe v)

  -- |Inserting in the map
  insert :: (Ord k , Ctr m k v) => k -> v -> m k v -> m k v

  -- |Deletes a valu in the map
  delete :: (Ord k , Ctr m k v) => k -> m k v -> m k v
  
  --  XXX: Juno only cares about root and verify;
  --       Maybe we should split this typeclass
  
  -- |Getting the merkle root of the whole thing
  root :: (Ctr m k v) => m k v -> Dig m

  -- |Verifier end
  verify :: (Ctr m k v) => Proxy m -> Dig m -> k -> v -> Verifier (Ev m) Bool

------------------------------------
------------------------------------
------------------------------------
-- Our own key value tree now
------------------------------------
------------------------------------
------------------------------------

-- First and foremost, some hashing functionality
type Hash = BS.ByteString

type MerkleRoot = Hash

sha256 :: Serialize a => a -> Hash
sha256 = SHA.hash SHA.SHA256 . encode

shaConcat :: [Hash] -> Hash
shaConcat = sha256 . BS.concat

nullHash :: Hash
nullHash = BS.replicate 32 0

--------------------------------------------
--------------------------------------------
--------------------------------------------

-- Usefull constraints to have:
type Ser2 k v = (Ser k , Ser v)

-- | A Red-Black tree is colored,
data Color = R | B deriving (Eq , Show, Generic)
instance Serialize Color

-- | And our merkelized variant is defined as:
data RB k v
  = Tip
  | Bin { _color   :: Color  -- ^ Color of the node
        , _key     :: k      -- ^ key on this node
        , _val     :: v      -- ^ value on this node
        , _left    :: RB k v -- ^ left subtree
        , _right   :: RB k v -- ^ right subtree
        , _authL   :: !Hash   -- ^ merkle root of left subtree
        , _authR   :: !Hash   -- ^ merkle root of right subtree
        }
  deriving (Eq, Show, Generic)
instance (Ser2 k v) => Serialize (RB k v)

-- | Convenience pretty printer. Makes life easier.
rbPretty :: (Show k) => RB k v -> IO ()
rbPretty = mapM_ putStrLn . draw
  where
    draw :: (Show k) => RB k v -> [String]
    draw Tip                     = []
    draw (Bin b k _ Tip Tip _ _) = [show b ++ show k]
    draw (Bin b k _ l   r   _ _) = (show b ++ show k) : drawSubTrees [l , r]
      where
        drawSubTrees [] = []
        drawSubTrees [t] =
            "|" : shift "`- " "   " (draw t)
        drawSubTrees (t:ts) =
            "|" : shift "+- " "|  " (draw t) ++ drawSubTrees ts

        shift first other = zipWith (++) (first : repeat other)

-- | Evidence is a bit identifying left or right,
--   the hash of the oposite direction and the
--   hash of the key value pair at that node
data RBEvidence
  -- ^ Case we are at the root, we need the hashes
  --   of the left and right subtree
  = EvHere Hash Hash
  -- ^ Case we continue through the left, we need
  --   the hash of the left subtree and the rbKvHash
  | EvL Hash Hash
  -- ^ Case we continue from the right, analogous to above
  | EvR Hash Hash
  deriving (Eq , Show)


-- | A 'Prover' for a Reb-Black tree will produce constant evidence
--   a value is in the given tree, we implement it by the means of
--   a monad writer (much in the sense of the proof stream produced
--   by the lambda-auth from the auth. data structs, genericaly paper)
type RBProver = Writer [RBEvidence]

-- | A 'Verifier' hence consumes that data.
type RBVerifier = Reader [RBEvidence]

-- | Constructs evidence in the RBProver monad already.
--
--   PRECONDITION: n /= Tip
rbEvLeft , rbEvRight , rbEvHere :: (Ser2 k v)
                                => RB k v -> RBProver ()
rbEvLeft  n = tell [EvL (_authR n) (rbKvHash n)]
rbEvRight n = tell [EvR (_authL n) (rbKvHash n)]
rbEvHere  n = tell [EvHere (_authL n) (_authR n)]

-- | Gets a hash for the key-value stored in this node
rbKvHash :: (Ser2 k v) => RB k v -> Hash
rbKvHash n = rbKvHashRaw (_key n) (_val n)

rbKvHashRaw :: (Ser2 k v) => k -> v -> Hash
rbKvHashRaw k v = shaConcat [ encode k , encode v ]

-- | The merkle root has to include the Key-Value hash
--   so that we can prove/verify the key-value correlations.
rbMerkleRoot :: (Ser2 k v) => RB k v -> MerkleRoot
rbMerkleRoot Tip = nullHash
rbMerkleRoot n   = shaConcat [_authL n , rbKvHash n , _authR n]

-- | Smart leaf constructor
rbLeaf :: (Ser2 k v) => Color -> k -> v -> RB k v
rbLeaf c k v = Bin c k v Tip Tip nullHash nullHash

-- | Smart bin constructor
rbBin :: (Ser2 k v) => Color -> k -> v -> RB k v -> RB k v -> RB k v
rbBin c k v l r = Bin c k v l r (rbMerkleRoot l) (rbMerkleRoot r)

rbBlack , rbRed :: (Ser2 k v) => k -> v -> RB k v -> RB k v -> RB k v
rbBlack = rbBin B
rbRed   = rbBin R


-- | From here onwards, the code has been adapted from:
--
--  https://www.cs.kent.ac.uk/people/staff/smk/redblack/Untyped.hs 
--  
--  This Red-Black tree satisfies a weaker invariant than the
--  traditional red-black trees. Nevertheless, after insterting
--  [1..n] randomly, the root of the tree is decently close to
--  n/2 for my taste.

-- Some utility functions:
rbDarken :: RB k v -> RB k v
rbDarken Tip = Tip
rbDarken n   = n { _color = B}

rbBlush :: RB k v -> RB k v
rbBlush Tip = Tip
rbBlush n   = n { _color = R}

rbIsBlack , rbIsRed :: RB k v -> Bool
rbIsBlack = (== B) . _color
rbIsRed   = (== R) . _color

-- | Inserts (or modifies, if already existing) a new key-value
--   pair.
--
rbInsert :: (Ord k , Ser2 k v)
         => k -> v -> RB k v -> RB k v
rbInsert k v tr = rbDarken $ ins tr
  where
--  ins :: RB k v -> RB k v
    ins Tip = rbLeaf R k v
    ins n
      | rbIsBlack n
      = case compare k (_key n) of
          EQ -> n { _val = v }
          LT -> rbBalance (ins $ _left n) (_key n) (_val n) (_right n)
          GT -> rbBalance (_left n) (_key n) (_val n) (ins $ _right n)
      | otherwise
      = case compare k (_key n) of
          EQ -> n { _val = v}
          LT -> let l'  = ins $ _left n
                    lH' = rbMerkleRoot l'
                 in n { _left = l' , _authL = lH' }
          GT -> let r'  = ins $ _right n
                    rH' = rbMerkleRoot r'
                 in n { _right = r' , _authR = rH' }

-- | Balancing our tree.
--
--   This is a nasty function. We could simplify the code in the
--   expense of recomputing more hashes.
--
rbBalance :: (Ser2 k v) => RB k v -> k -> v -> RB k v -> RB k v
rbBalance n@(Bin R _ _ _ _ _ _) k1 v1 m@(Bin R _ _ _ _ _ _)
  = rbRed k1 v1 (rbDarken n) (rbDarken m)

rbBalance (Bin R k0 v0 ll@(Bin R _ _ _ _ _ _) lr llH lrH) k1 v1 r
  = let r'  = Bin B k1 v1 lr r lrH (rbMerkleRoot r)
     in Bin R k0 v0 (rbDarken ll) r' llH (rbMerkleRoot r')

rbBalance (Bin R k0 v0 ll (Bin R k1 v1 lrl lrr lrlH lrrH) llH _) k2 v2 r
  = let l' = Bin B k0 v0 ll lrl llH lrlH
        r' = Bin B k2 v2 lrr r lrrH (rbMerkleRoot r)
     in rbRed k1 v1 l' r'

rbBalance l k0 v0 (Bin R k1 v1 rl rr@(Bin R _ _ _ _ _ _) rlH rrH)
  = let l' = Bin B k0 v0 l rl (rbMerkleRoot l) rlH
     in Bin R k1 v1 l' (rbDarken rr) (rbMerkleRoot l') rrH

rbBalance l k0 v0 (Bin R k1 v1 (Bin R k2 v2 rll rlr rllH rlrH) rr _ rrH)
  = let l' = Bin B k0 v0 l rll (rbMerkleRoot l) rllH
        r' = Bin B k1 v1 rlr rr rlrH rrH
     in rbRed k2 v2 l' r'

rbBalance l k0 v0 r
  = rbBlack k0 v0 l r


-- |Deletion of a key in a tree
--
--  XXX: Finish this function!
--
rbDelete :: (Ord k , Ser2 k v)
         => k -> RB k v -> RB k v
rbDelete k t = rbDarken (del t)
  where
--  del :: (Ord k , Ser2 k v) => RB k v -> RB k v
    del Tip = Tip
    del (Bin _ k0 v0 l r lH rH)
      = case compare k k0 of
          EQ -> rbApp l r
          LT -> let l'  = del l
                    lH' = rbMerkleRoot l'
                 in if rbIsBlack l
                    then rbBalLeft l' k0 v0 r
                    else Bin R k0 v0 l' r lH' rH
          GT -> let r'  = del r
                    rH' = rbMerkleRoot r'
                 in if rbIsBlack r
                    then rbBalRight l k0 v0 r'
                    else Bin R k0 v0 l r' lH rH'

    rbBalLeft :: (Ser2 k v) => RB k v -> k -> v -> RB k v -> RB k v
    rbBalLeft l@(Bin R _ _ _ _ _ _) ky vy r
      = rbRed ky vy (rbDarken l) r
    rbBalLeft l ky vy r@(Bin B _ _ _ _ _ _)
      = rbBalance l ky vy (rbBlush r)
    rbBalLeft l ky vy (Bin R kx vx (Bin B krx vrx rll rlr rllH _)
                                   rr _ _)
      = let lH = rbMerkleRoot l
         in rbRed krx vrx (Bin B ky vy l rll lH rllH)
                          (rbBalance rlr kx vx (rbBlush rr))
                  
            
    rbBalRight :: (Ser2 k v) => RB k v -> k -> v -> RB k v -> RB k v
    rbBalRight l kx vx r@(Bin R _ _ _ _ _ _)
      = rbRed kx vx l (rbDarken r)
    rbBalRight l@(Bin B _ _ _ _ _ _) ky vy r
      = rbBalance (rbBlush l) ky vy r
    rbBalRight (Bin R kx vx ll (Bin B ky vy rll rlr _ rlrH) _ _)
               kz vz r
      = let rH = rbMerkleRoot r
         in rbRed ky vy (rbBalance (rbBlush ll) kx vx rll)
                        (Bin B kz vz rlr r rlrH rH)

    rbApp :: (Ser2 k v) => RB k v -> RB k v -> RB k v
    rbApp Tip x = x
    rbApp x Tip = x
    rbApp (Bin R kx vx ll lr llH _) (Bin R ky vy rl rr _ rrH)
      = case rbApp lr rl of
          Bin R ka va la ra laH raH
               -> rbRed ka va (Bin R kx vx ll la llH laH)
                              (Bin R ky vy ra rr raH rrH)
          lrrl -> let lrrlH = rbMerkleRoot lrrl
                      r'    = Bin R ky vy lrrl rr lrrlH rrH
                   in Bin R kx vx ll r' llH (rbMerkleRoot r')
    rbApp (Bin B kx vx ll lr llH _) (Bin B ky vy rl rr _ rrH)
      = case rbApp lr rl of
          Bin R ka va la ra laH raH
               -> rbRed ka va (Bin B kx vx ll la llH laH)
                              (Bin B ky vy ra rr raH rrH)
          lrrl -> rbBalLeft ll kx vx (Bin B ky vy lrrl rr (rbMerkleRoot lrrl) rrH)
    rbApp a (Bin R kx vx l r _ rH)
      = let l' = rbApp a l
         in Bin R kx vx l' r (rbMerkleRoot l') rH
    rbApp (Bin R kx vx l r lH _) a
      = let r' = rbApp r a
         in Bin R kx vx l r' lH (rbMerkleRoot r')

-- |Looks up a value in a Red-Black tree. Returns a proof that
--  that value belongs in the tree.
rbLookup :: (Ord k , Ser2 k v)
         => k -> RB k v -> RBProver (Maybe v)
rbLookup _ Tip = return Nothing
rbLookup k n
  = case compare k (_key n) of
      EQ -> rbEvHere  n >> return (Just $ _val n)
      LT -> rbEvLeft  n >> rbLookup k (_left n)
      GT -> rbEvRight n >> rbLookup k (_right n)

-- |Verifies that a key-value pair belongs in the tree that has the given root.
rbVerify :: (Ser2 k v) => MerkleRoot -> k -> v -> RBVerifier Bool
rbVerify root0 k v
  = do pstream <- ask
       let myRoot = go pstream
       return (Just root0 == myRoot)
  where
    go :: [RBEvidence] -> Maybe MerkleRoot
    go []               = Nothing
    go (EvHere l r:_)   = return $ shaConcat [ l , rbKvHashRaw k v , r ]
    go (EvL r kv : evs) = (\x -> shaConcat [x , kv , r]) <$> go evs
    go (EvR l kv : evs) = (\x -> shaConcat [l , kv , x]) <$> go evs


----------------------------------
----------------------------------
-- My instance

instance VerifiedMap RB where
  type Ev  RB = [RBEvidence]
  type Dig RB = Hash
  type Ctr RB k v = Ser2 k v

  lkup     = rbLookup
  root     = rbMerkleRoot
  verify _ = rbVerify
  insert   = rbInsert


----------------------------------
----------------------------------
-- Testing stuff!

makeTree :: (Ord k, Ser2 k v) => [ (k , v) ] -> RB k v
makeTree = foldr (\(k , v) t -> rbInsert k v t) Tip

t1 :: RB Int Int
t1 = makeTree $ zip [50 :: Int,34,142,1234,51,23,54] [1..]

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


-- | @test m n@ will populate an empty redblack tree with m key-value pairs,
--   inserted in random order, and will perform n verified lookups on those pairs
--
--   Reasonable performance for m around 10^5
--
--   Running @test 300000 500@ takes about one minute on my machine.
test :: Int -> Int -> Int -> IO (RB Int Int)
test maxtree maxlkups deletes
  = do ks <- shuffle [1 .. maxtree]
       vs <- shuffle [1 .. maxtree]
       let t0   = makeTree (zip ks vs)
       let t    = foldr rbDelete t0 [1..deletes]
       let root0 = rbMerkleRoot t
       putStrLn $ "Tree root is: " ++ show root0
       res <- mapM (testLookup root0 t) (take maxlkups (filter (> deletes) ks))
       if and res
         then putStrLn "!! Success !!"
         else putStrLn "!! Failure !!" >> print ks
       return t
  where
    testLookup :: MerkleRoot -> RB Int Int -> Int -> IO Bool
    testLookup root0 tr k
      = do let (val , prf) = runWriter $ rbLookup k tr
           case val of
             Nothing -> putStrLn ("Can't find key: " ++ show k) >> return False
             Just v  -> do putStrLn ("Checking key: " ++ show k ++ " and value: "
                                                                ++ show v)
                           if runReader (rbVerify root0 k v) prf
                           then putStrLn "    Ok!"  >> return True
                           else putStrLn "    Fail" >> return False
