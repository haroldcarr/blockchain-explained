authenticated map (merkle trees)
--------------------------------

This exposition focuses on high-level view of Merkle Trees along the
lines presented in the paper
[Authenticated Data Structures, Generically](http://www.cs.umd.edu/~amiller/gpads/).

A previous exposition
[TBD](TBD)
showed a low-level view of Merkle Trees.

setup
-----

```haskell
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE KindSignatures        #-}
-- MultiParamTypeClasses needed by stylish-haskell
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}

module VerifiedMap where

import qualified Codec.Digest.SHA     as SHA
import           Control.Monad.Reader
import           Control.Monad.Writer
import qualified Data.ByteString      as BS
import qualified Data.Map             as M
import           Data.Proxy
import           Data.Serialize
import           GHC.Exts             (Constraint)
import           GHC.Generics
import           Prelude              hiding (lookup)
import           System.Random
import           Test.Hspec
```

verified map
------------

A `VerifiedMap` an authenticated key/value map where `lookup` results
can be verified as authentic.

```haskell
class VerifiedMap (m :: * -> * -> *) where
  type Evidence  m     :: *
  type Digest    m     :: *
  type Ctr       m k v :: Constraint

  -- | Add a key/value to a map (or update a value if key exists).
  insert :: (Ord k , Ctr m k v) => k -> v -> m k v -> m k v

  -- | Lookup returns the value associated with a key.
  -- It also returns `Evidence` that can be used to
  -- independently verify that the map contains the key/value pair.
  lookup :: (Ord k , Ctr m k v) => k -> m k v -> Prover (Evidence m) (Maybe v)

  -- | Merkle root of a map.
  root   ::         (Ctr m k v) => m k v -> Digest m

  -- | Given a map's merkle root, a key/value pair and evidence,
  -- verifies that the map contains the key/value pair.
  verify ::         (Ctr m k v) => Proxy m -> Digest m -> k -> v -> Verifier (Evidence m) Bool

-- | Prover 'writes' to proof stream `w` and provides "result" `a`
type Prover w a   = Writer w a

-- | Verifier 'reads' and verifies proof stream `w` produces result `a`
type Verifier r a = Reader r a
```

------------------------------------------------------------------------

binary-tree implementation of `VerifiedMap`
-------------------------------------------

This exposition will use a simple binary tree implementation to enable
the focus to stay on the proofs and verification functions (rather than
the map implementation).

A conventional `BTree` is augemented to include the hashes of the left
and right branches.

```haskell
data BTree k v
  = Tip
  | Bin { _key   :: ! k           -- ^ key on this node
        , _val   :: ! v           -- ^ value on this node
        , _left  :: ! (BTree k v) -- ^ left subtree
        , _right :: ! (BTree k v) -- ^ right subtree
        , _authL :: ! Hash        -- ^ merkle root of left subtree
        , _authR :: ! Hash        -- ^ merkle root of right subtree
        }
  deriving (Eq, Show, Generic)
instance (Ser2 k v) => Serialize (BTree k v) -- not used in this exposition
```

where

```haskell
-- | constraint synonym
type Ser2 k v = (Ser k, Ser v)

-- | constraint synonym
type Ser a = (Serialize a , Show a)

type Hash = BS.ByteString
```

Insert is also conventional, except that hashes are recomputed to
account for the changed tree.

```haskell
-- | Insert
btInsert :: (Ord k , Ser2 k v) => k -> v -> BTree k v -> BTree k v
btInsert k v = go
 where
  go Tip = btLeaf k v
  go n =
    case compare k (_key n) of
      EQ -> n { _val = v }
      LT -> let l = lr (_left  n) in btBin (_key n) (_val n) l         (_right n)
      GT -> let r = lr (_right n) in btBin (_key n) (_val n) (_left n) r
  lr = btInsert k v
```

where

```haskell
-- | leaf constructor
btLeaf :: (Ser2 k v) => k -> v -> BTree k v
btLeaf k v = Bin k v Tip Tip nullHash nullHash

-- | bin constructor
btBin :: (Ser2 k v) => k -> v -> BTree k v -> BTree k v -> BTree k v
btBin k v l r = Bin k v l r (btMerkleRoot l) (btMerkleRoot r)

type MerkleRoot = Hash

-- | Merkle root includes Key-Value hash
--   to enable proving/verifing key-value correlations.
btMerkleRoot :: (Ser2 k v) => BTree k v -> MerkleRoot
btMerkleRoot Tip = nullHash
btMerkleRoot n   = shaConcat [_authL n , btKvHash n , _authR n]

-- | hash for key-value stored in node
btKvHash :: (Ser2 k v) => BTree k v -> Hash
btKvHash n = btKvHashRaw (_key n) (_val n)

btKvHashRaw :: (Ser2 k v) => k -> v -> Hash
btKvHashRaw k v = shaConcat [ encode k , encode v ]

sha256 :: Serialize a => a -> Hash
sha256 = SHA.hash SHA.SHA256 . encode

shaConcat :: [Hash] -> Hash
shaConcat = sha256 . BS.concat

nullHash :: Hash
nullHash = BS.replicate 32 0
```

lookup provides evidence
------------------------

The authenticated part is `lookup`:

```haskell
-- | Lookup
btLookup :: (Ord k , Ser2 k v) => k -> BTree k v -> BTreeProver (Maybe v)
btLookup _ Tip = return Nothing
btLookup k n =
  case compare k (_key n) of
    EQ -> btEvEQ n >> return (Just $ _val n)
    LT -> btEvLT n >> btLookup k (_left n)
    GT -> btEvGT n >> btLookup k (_right n)

-- | 'Prover' produces evidence that a key/value is in given tree.
type BTreeProver = Writer [BTreeEvidence]
```

`lookup` evidence is defined to be a list of

```haskell
-- | Evidence constructor identifies traversal direction
-- along with appropriate hashes.
data BTreeEvidence
  = EvEQ Hash Hash -- ^ hashes of left and right subtree
  | EvLT Hash Hash -- ^ hash of left and kvHash
  | EvGT Hash Hash -- ^ hash of right and kvHash
  deriving (Eq , Show)
```

The evidence is placed in a proof stream during `lookup` traversal by:

```haskell
-- | Constructs evidence in the BTreeProver monad. PRECONDITION: n /= Tip
btEvEQ, btEvLT , btEvGT :: (Ser2 k v) => BTree k v -> BTreeProver ()
btEvEQ n = tell [EvEQ (_authL n)   (_authR n)]
btEvLT n = tell [EvLT (_authR n) (btKvHash n)]
btEvGT n = tell [EvGT (_authL n) (btKvHash n)]
```

                   10
         5                    15
    3         7         13          17
                      11

```haskell
ex :: BTree Int Int
ex = btInsert 11 11 (btInsert 13 13 (btInsert 17 17 (btInsert 15 15
                     (btInsert 3  3 (btInsert  7  7 (btInsert  5  5
                                                     (btLeaf 10 10)))))))
-- | make the tests easier to read
evToL :: (Maybe a, [BTreeEvidence]) -> (Maybe a, [String])
evToL (ma, evs) = (ma, foldr (\ev a -> evl ev : a) [] evs)
 where evl ev = case ev of EvEQ _ _ -> "EvEQ"; EvLT _ _ -> "EvLT"; EvGT _ _ -> "EvGT"


t1 :: Spec
t1 =
  describe "t1" $ do
    it "btLookup 11 ex" $ evToL (runWriter (btLookup 11 ex))
       `shouldBe` (Just 11, ["EvGT", "EvLT", "EvLT", "EvEQ"])
    it "btLookup 17 ex" $ evToL (runWriter (btLookup 17 ex))
       `shouldBe` (Just 17, ["EvGT", "EvGT", "EvEQ"])
    it "btLookup  5 ex" $ evToL (runWriter (btLookup  5 ex))
       `shouldBe` (Just  5, ["EvLT", "EvEQ"])
    it "btLookup 10 ex" $ evToL (runWriter (btLookup 10 ex))
       `shouldBe` (Just 10, ["EvEQ"])
    -- When not in map the evidence shows the path taken to a Tip.
    it "btLookup  0 ex" $ evToL (runWriter (btLookup  0 ex))
       `shouldBe` (Nothing, ["EvLT","EvLT","EvLT"])
```

verify evidence
---------------

```haskell
-- | Verifies that a key/value pair belongs in a tree that has the given root.
btVerify :: (Ser2 k v) => MerkleRoot -> k -> v -> BTreeVerifier Bool
btVerify root0 k v = do
  pstream <- ask
  let myRoot = go pstream
  return (Just root0 == myRoot)
 where
  go :: [BTreeEvidence] -> Maybe MerkleRoot
  go             []    = Nothing
  go (EvEQ l  r : _)   = return $ shaConcat [ l , btKvHashRaw k v , r ]
  go (EvLT r kv : evs) = (\x -> shaConcat [x , kv , r]) <$> go evs
  go (EvGT l kv : evs) = (\x -> shaConcat [l , kv , x]) <$> go evs

-- | 'Verifier' consumes above data.
type BTreeVerifier = Reader [BTreeEvidence]
```

```haskell
t2 :: Spec
t2 =
  let root0       = root ex
      (_,proof11) = runWriter (btLookup 11 ex)
      (_,proof17) = runWriter (btLookup 17 ex)
  in describe "t2" $ do
      it "btVerify 11 11" $ runReader (btVerify root0 (11::Int) (11::Int)) proof11
         `shouldBe` True
      it "btVerify 17 17" $ runReader (btVerify root0 (17::Int) (17::Int)) proof17
         `shouldBe` True
      -- correct key, wrong value
      it "btVerify 17  9" $ runReader (btVerify root0 (17::Int) ( 9::Int)) proof17
         `shouldBe` False
      -- use bad proof on key/value not in map
      it "btVerify 14 14" $ runReader (btVerify root0 (14::Int) (14::Int)) proof17
         `shouldBe` False
```

make `BTree` a `VerifiedMap`
----------------------------

```haskell
instance VerifiedMap BTree where
  type Evidence  BTree     = [BTreeEvidence]
  type Digest    BTree     = Hash
  type Ctr       BTree k v = Ser2 k v

  insert   = btInsert
  root     = btMerkleRoot
  lookup   = btLookup
  verify _ = btVerify
```

test using interface
--------------------

```haskell
t3 :: Spec
t3 = do
  (_, r) <- runIO (test 10000 10000)
  describe "t3" $
    it "test 10000 10000" $ r `shouldBe` True

-- | @test m n@ populates an empty tree with m key-value pairs,
--   inserted in random order, then perform n verified lookups
test :: Int -> Int -> IO (BTree Int Int, Bool)
test maxtree maxlkups = do
  ks <- shuffle [1 .. maxtree]
  vs <- shuffle [1 .. maxtree]
  -- build a BTree
  let t     = foldr (\(k , v) acc -> btInsert k v acc) Tip (zip ks vs)
  let root0 = root t
  res <- mapM (testLookup root0 t) (take maxlkups ks)
  return (t, and res)
 where
  -- use generic `lookup` and `verify` in test
  testLookup root0 tr k = do
    let (val, proof) = runWriter $ lookup k tr
    case val of
      Nothing -> putStrLn ("Can't find key: " ++ show k) >> return False
      Just v  ->
        let msg = "verify k v: (" ++ show k ++ "," ++ show v ++ "): "
        in if runReader (verify (Proxy::Proxy BTree) root0 k v) proof then
             return True
           else
             putStrLn (msg ++ "FAIL") >> return False

fisherYatesStep :: RandomGen g
                => (M.Map Int a, g) -> (Int, a) -> (M.Map Int a, g)
fisherYatesStep (m, gen) (i, x) = ((M.insert j x . M.insert i (m M.! j)) m
                                  , gen')
  where (j, gen') = randomR (0, i) gen

fisherYates :: RandomGen g => [a] -> g -> ([a], g)
fisherYates [] g = ([], g)
fisherYates l g =
  toElems $ foldl fisherYatesStep (initial (head l) g) (numerate (tail l))
 where
  toElems (x, y) = (M.elems x, y)
  numerate = zip [1..]
  initial x gen = (M.singleton 0 x, gen)

shuffle :: [a] -> IO [a]
shuffle l = getStdRandom (fisherYates l)
```

credits
-------

The code above is modified from Victor Cacciari Miraldo's authenticated
red/black tree implementation.
