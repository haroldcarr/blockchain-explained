> {-# LANGUAGE ConstraintKinds       #-}
> {-# LANGUAGE DeriveGeneric         #-}
> {-# LANGUAGE KindSignatures        #-}
> -- MultiParamTypeClasses needed by stylish-haskell
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE ScopedTypeVariables   #-}
> {-# LANGUAGE TypeFamilies          #-}
>
> module VerifiedMap where
>
> import qualified Codec.Digest.SHA     as SHA
> import           Control.Monad.Reader
> import           Control.Monad.Writer
> import qualified Data.ByteString      as BS
> import qualified Data.Map             as M
> import           Data.Proxy
> import           Data.Serialize
> import           GHC.Exts             (Constraint)
> import           GHC.Generics
> import           Prelude              hiding (lookup)
> import           System.Random
> import           Test.Hspec

> -- | prover 'writes' proof stream
> type Prover w a   = Writer w a

> -- | verifier 'reads' proof stream
> type Verifier r a = Reader r a

> class VerifiedMap (m :: * -> * -> *) where
>   type Ev  m     :: *          -- ^ Evidence
>   type Dig m     :: *          -- ^ Digest
>   type Ctr m k v :: Constraint
>
>   lookup :: (Ord k , Ctr m k v) => k -> m k v -> Prover (Ev m) (Maybe v)
>   insert :: (Ord k , Ctr m k v) => k -> v -> m k v -> m k v
>   root   ::         (Ctr m k v) => m k v -> Dig m
>   verify ::         (Ctr m k v) => Proxy m -> Dig m -> k -> v -> Verifier (Ev m) Bool

------------------------------------------------------------------------------

> instance VerifiedMap BTree where
>   type Ev  BTree     = [BTreeEvidence]
>   type Dig BTree     = Hash
>   type Ctr BTree k v = Ser2 k v
>
>   lookup   = btLookup
>   root     = btMerkleRoot
>   verify _ = btVerify
>   insert   = btInsert

> -- | constraint synonym
> type Ser a = (Serialize a , Show a)

> -- | constraint synonym
> type Ser2 k v = (Ser k, Ser v)

> type Hash       = BS.ByteString

> data BTree k v
>   = Tip
>   | Bin { _key   :: k         -- ^ key on this node
>         , _val   :: v         -- ^ value on this node
>         , _left  :: BTree k v -- ^ left subtree
>         , _right :: BTree k v -- ^ right subtree
>         , _authL :: !Hash     -- ^ merkle root of left subtree
>         , _authR :: !Hash     -- ^ merkle root of right subtree
>         }
>   deriving (Eq, Show, Generic)
> instance (Ser2 k v) => Serialize (BTree k v)

> -- | Evidence
> --    identifies left or right
> --    hash of oposite direction
> --    hash of key value pair at that node
> data BTreeEvidence
>   -- ^ Case root : hashes of left and right subtree
>   = EvHere Hash Hash
>   -- ^ Case left : hash of left and kvHash
>   | EvL Hash Hash
>   -- ^ Case right: hash of right and kvHash
>   | EvR Hash Hash
>   deriving (Eq , Show)

> -- | Insert
> btInsert :: (Ord k , Ser2 k v)
>          => k -> v -> BTree k v -> BTree k v
> btInsert k v = go
>  where
>   go Tip = btLeaf k v
>   go n =
>     case compare k (_key n) of
>       EQ -> n { _val = v }
>       LT -> let l = lr (_left  n) in btBin (_key n) (_val n) l         (_right n)
>       GT -> let r = lr (_right n) in btBin (_key n) (_val n) (_left n) r
>   lr = btInsert k v

       LT -> let (l,btb) = lr (_left  n) in btb l         (_right n)
       GT -> let (r,btb) = lr (_right n) in btb (_left n) r
   lr n = (btInsert k v n , btBin (_key n) (_val n))

a003-0.0.0: test (suite: test)

Progress: 3/4test: No match in record selector _key

Completed 4 action(s).
Test suite failure for package a003-0.0.0
    test:  exited with: ExitFailure 1


> -- | Lookup
> btLookup :: (Ord k , Ser2 k v)
>          => k -> BTree k v -> BTreeProver (Maybe v)
> btLookup _ Tip = return Nothing
> btLookup k n =
>   case compare k (_key n) of
>     EQ -> btEvHere  n >> return (Just $ _val n)
>     LT -> btEvLeft  n >> btLookup k (_left n)
>     GT -> btEvRight n >> btLookup k (_right n)

> -- | 'Prover' produces constant evidence that a value is in given tree.
> --   Implemented with a monad writer (like proof stream produced
> --   by lambda-auth from the auth. data structs, genericaly paper)
> type BTreeProver = Writer [BTreeEvidence]

> -- | Constructs evidence in the RBProver monad already.
> --   PRECONDITION: n /= Tip
> btEvLeft , btEvRight , btEvHere :: (Ser2 k v)
>                                 => BTree k v -> BTreeProver ()
> btEvLeft  n = tell [EvL    (_authR n) (btKvHash n)]
> btEvRight n = tell [EvR    (_authL n) (btKvHash n)]
> btEvHere  n = tell [EvHere (_authL n)   (_authR n)]

> -- | hash for key-value stored in node
> btKvHash :: (Ser2 k v) => BTree k v -> Hash
> btKvHash n = btKvHashRaw (_key n) (_val n)
>
> btKvHashRaw :: (Ser2 k v) => k -> v -> Hash
> btKvHashRaw k v = shaConcat [ encode k , encode v ]

> -- | Verifies that a key-value pair belongs in the tree that has the given root.
> btVerify :: (Ser2 k v) => MerkleRoot -> k -> v -> BTreeVerifier Bool
> btVerify root0 k v = do
>   pstream <- ask
>   let myRoot = go pstream
>   return (Just root0 == myRoot)
>  where
>   go :: [BTreeEvidence] -> Maybe MerkleRoot
>   go []               = Nothing
>   go (EvHere l r:_)   = return $ shaConcat [ l , btKvHashRaw k v , r ]
>   go (EvL r kv : evs) = (\x -> shaConcat [x , kv , r]) <$> go evs
>   go (EvR l kv : evs) = (\x -> shaConcat [l , kv , x]) <$> go evs

> -- | 'Verifier' consumes above data.
> type BTreeVerifier = Reader [BTreeEvidence]

> type MerkleRoot = Hash

> sha256 :: Serialize a => a -> Hash
> sha256 = SHA.hash SHA.SHA256 . encode

> shaConcat :: [Hash] -> Hash
> shaConcat = sha256 . BS.concat

> nullHash :: Hash
> nullHash = BS.replicate 32 0

> -- | Merkle root includes Key-Value hash
> --   to enable proving/verifing key-value correlations.
> btMerkleRoot :: (Ser2 k v) => BTree k v -> MerkleRoot
> btMerkleRoot Tip = nullHash
> btMerkleRoot n   = shaConcat [_authL n , btKvHash n , _authR n]

> -- | leaf constructor
> btLeaf :: (Ser2 k v) => k -> v -> BTree k v
> btLeaf k v = Bin k v Tip Tip nullHash nullHash

> -- | bin constructor
> btBin :: (Ser2 k v) => k -> v -> BTree k v -> BTree k v -> BTree k v
> btBin k v l r = Bin k v l r (btMerkleRoot l) (btMerkleRoot r)

------------------------------------------------------------------------------

> -- | Pretty printer.
> btPretty :: (Show k) => BTree k v -> IO ()
> btPretty = mapM_ putStrLn . draw
>   where
>     draw :: (Show k) => BTree k v -> [String]
>     draw Tip                   = []
>     draw (Bin k _ Tip Tip _ _) = [show k]
>     draw (Bin k _ l   r   _ _) = show k : drawSubTrees [l,r]
>       where
>         drawSubTrees []     = []
>         drawSubTrees [t]    = "|" : shift "r- " "   " (draw t)
>         drawSubTrees (t:ts) = "|" : shift "l- " "|  " (draw t) ++ drawSubTrees ts
>         shift first other   = zipWith (++) (first : repeat other)


               10
     5                    x15
3         7         13          17
                 11    14

> example :: BTree Int Int
> example = btInsert 11 11 (btInsert 13 13 (btInsert 17 17 (btInsert 15 15
>                           (btInsert 3  3 (btInsert  7  7 (btInsert  5  5
>                                                           (btLeaf 10 10)))))))

btPretty example

------------------------------------------------------------------------------
-- Testing

> t1 :: Spec
> t1 = do
>   (_, r) <- runIO (test 10000 10000)
>   describe "t1" $
>     it "test 10000 10000" $ r `shouldBe` True

> -- | @test m n@ populates an empty tree with m key-value pairs,
> --   inserted in random order, then perform n verified lookups
> test :: Int -> Int -> IO (BTree Int Int, Bool)
> test maxtree maxlkups = do
>   ks <- shuffle [1 .. maxtree]
>   vs <- shuffle [1 .. maxtree]
>   let t     = makeTree (zip ks vs)
>   let root0 = btMerkleRoot t
>   -- putStrLn $ "Tree root is: " ++ show root0
>   res <- mapM (testLookup root0 t) (take maxlkups ks)
>   return (t, and res)
>  where
>   testLookup :: MerkleRoot -> BTree Int Int -> Int -> IO Bool
>   testLookup root0 tr k = do
>     let (val, proof) = runWriter $ btLookup k tr
>     case val of
>       Nothing -> putStrLn ("Can't find key: " ++ show k) >> return False
>       Just v  ->
>         let msg = "btVerify k v: (" ++ show k ++ "," ++ show v ++ "): "
>         in if runReader (btVerify root0 k v) proof then return True
>            else putStrLn (msg ++ "FAIL")             >> return False

> makeTree :: (Ord k, Ser2 k v) => [ (k , v) ] -> BTree k v
> makeTree = foldr (\(k , v) t -> btInsert k v t) Tip

> fisherYatesStep :: RandomGen g
>                 => (M.Map Int a, g) -> (Int, a) -> (M.Map Int a, g)
> fisherYatesStep (m, gen) (i, x) = ((M.insert j x . M.insert i (m M.! j)) m
>                                   , gen')
>   where (j, gen') = randomR (0, i) gen

> fisherYates :: RandomGen g => [a] -> g -> ([a], g)
> fisherYates [] g = ([], g)
> fisherYates l g =
>   toElems $ foldl fisherYatesStep (initial (head l) g) (numerate (tail l))
>  where
>   toElems (x, y) = (M.elems x, y)
>   numerate = zip [1..]
>   initial x gen = (M.singleton 0 x, gen)

> shuffle :: [a] -> IO [a]
> shuffle l = getStdRandom (fisherYates l)
