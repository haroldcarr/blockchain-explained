{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

the block in blockchain explained (merkle trees)
---------------------------------

setup:

> {-# LANGUAGE NoImplicitPrelude #-}
> {-# LANGUAGE OverloadedStrings #-}
>
> module Block where
>
> import           ClassyPrelude           as CP
> import           Control.Monad.ST.Strict (runST)
> import           Crypto.Hash.SHA256      as C  (hash)
> import           Data.ByteString.Char8   as BS (pack, replicate)
> import           Data.Char               (chr)
> import           Data.Map.Strict         as M
> import           Data.Sequence           as S
> import           Data.STRef.Strict
> import           Test.Hspec
> import           Test.RandomStrings

> {-# ANN module ("HLint: ignore Eta reduce"::String)         #-}
> {-# ANN module ("HLint: ignore Reduce duplication"::String) #-}

For this exposition, a block will be defined as:

> data Block =
>     Block {
>           header :: ! BlockHeader
>         , txs    :: ! Transactions
>     } deriving (Eq, Show)

where transactions are are an ordered sequence of data:

> type Transaction  = ByteString
> type Transactions = Seq BData

For this expostion the "transactions" are uninterpreted opaque data:

> type BData        = ByteString

In a "real" blockchain, this is where "smart contracts" would be involved.

The most important part, for now, is the header:

> data BlockHeader =
>     BlockHeader {
>           bPrevHash   :: ! BHash      -- ^ hash of previous block
>         , bMerkleRoot :: ! BHash      -- ^ hash of root of this block's transactions
>         , bTimestamp  :: ! BTimestamp -- ^ when this block was created
>     } deriving (Eq, Show)

where

> type BHash      = ByteString
> type BTimestamp = ByteString

The exposition
[The Chain in Blockchain]("http://haroldcarr.com/posts/2017-06-19-the-chain-in-blockchain.html")
explained how blocks are linked in chains using `bPrevHash` etc.
Here the focus is on `bMerkleRoot`.

The merkle root is hash of the hash of the bytes that make up each transaction.

The bytes of all transactions in the block are individually hashed, forming a list
of hashes:

> type HashDigest = ByteString
> type HashList   = Seq HashDigest
>
> txHashes :: Block -> HashList
> txHashes (Block _ transactions) = CP.map C.hash transactions

Then each each adjacent pair hashes are concatenated and hashed again,

> concatHash :: HashDigest -> HashDigest -> HashDigest
> concatHash x y = C.hash (x <> y)

forming the parent of those pairs.  This process is repeated on each level or ordered
parents until there is a single node.  That node is the "merkle root":

![img](https://orm-chimera-prod.s3.amazonaws.com/1234000001802/images/msbt_0703.png)

> createMerkleRoot :: HashList -> HashDigest
> createMerkleRoot hl0
>     | S.null hl0 = nullHash
>     | otherwise  = loop hl0
>   where
>
>     loop hl =
>         if S.length hl == 1 then S.index hl 0
>         else loop (combine (dupWhenOdd hl))
>
>     -- when odd duplicate last hash
>     dupWhenOdd hl =
>         if odd $ S.length hl then hl |> S.index hl (S.length hl - 1)
>         else hl
>
>     -- Make newHashList (1/2 size of given hashList)
>     -- where every element of newHashList is made
>     -- by taking adjacent pairs of given hashList,
>     -- concatenating their contents
>     -- then hashing that concatenated contents.
>     combine hl = runST $ do
>         newHashList <- newSTRef S.empty
>         forM_ (S.chunksOf 2 hl) $ \x ->
>             modifySTRef' newHashList (|> concatHash (S.index x 0) (S.index x 1))
>         readSTRef newHashList

where

> nullHash :: HashDigest
> nullHash = BS.replicate 32 (chr 0)

> t1 :: Spec
> t1 =
>     let one   = S.empty |> C.hash "01"
>         two   = one     |> C.hash "10"
>         three = two     |> C.hash "11"
>     in describe "t1" $ do
>         it "empty" $ createMerkleRoot S.empty `shouldBe` nullHash
>         it "one"   $ createMerkleRoot one     `shouldBe` C.hash "01"
>         it "two"   $ createMerkleRoot two     `shouldBe` concatHash (C.hash "01") (C.hash "10")
>         it "three" $ createMerkleRoot three
>                      `shouldBe`
>                      "\STX\SYN\n\251\228\227\135\246\SUB\EM\128\196\r\b\166\RS\NAK9\235X\236R\184\134\220\141wP\225\ACK\169\254"

The merkle root, besides acting as a "signature" of the transactions,
can be used by lightweight peers to ensure that a transaction is in a
block without needing to access (i.e., over a network connection) all
the transactions in a block
(e.g., Bitcoin's
[Simplified Payment Verification]("http://chimera.labs.oreilly.com/books/1234000001802/ch07.html#_merkle_trees_and_simplified_payment_verification_spv")).

A lightweight contacts a full node asking for a "merkle path" from a particular transaction,
through the merkle tree, to the merkle root.

![img](https://orm-chimera-prod.s3.amazonaws.com/1234000001802/images/msbt_0705.png)

Assume the lightweight node has transaction `K`.  To verify it is a member of the block it
hashes transaction `K`, forming `H_K`.  It sends `H_K` to the full node.  The full
node creates a merkle path by identifying which ordered set of hashes it needs to send to their
client so it can hash its transaction with the path to reach and match the root (a mismatch
would mean the transaction is not included in the block).  In this case the path would be

~~~haskell
[H_L, H_IJ, H_MNOP, H_ABCDEFGH]
~~~

Those are the hashes needed by the lightweight peer to hash from its transaction to the root.

To create the path an explicit tree may be used:

> -- | Left or Right neighbor
> type MerklePathElement = Either HashDigest HashDigest
> type MerklePath        = [ MerklePathElement ]
>
> -- | neighbor and parent are `Nothing` for the root
> data MerkleInfo =
>     MerkleInfo {
>           identity :: ! HashDigest                             -- ^ for testing
>         , neighbor :: ! (Maybe MerklePathElement)
>         , parent   :: ! (Maybe HashDigest)
>     } deriving (Eq, Show)
>
> type MerkleTreeMap = M.Map HashDigest MerkleInfo
>
> -- | This function has the same structure as `createMerkleRoot`.
> -- The difference is that this one creates a tree (using a Map).
> mkMerkleTreeMap :: HashList -> MerkleTreeMap
> mkMerkleTreeMap hl0
>     | S.null hl0 = M.empty
>     | otherwise  = loop (hl0, M.empty)
>   where
>     loop (hl, m) =
>         if S.length hl == 1 then
>             let h = S.index hl 0
>             in M.insert h (MerkleInfo h Nothing Nothing) m
>         else loop (combine (dupWhenOdd hl) m)
>
>     dupWhenOdd hl =
>         if odd $ S.length hl then hl |> S.index hl (S.length hl - 1)
>         else hl
>
>     combine hl m = runST $ do
>         newHashListAndMap <- newSTRef (S.empty, m)
>         forM_ (S.chunksOf 2 hl) $ \x -> do
>             let parentHash = concatHash (S.index x 0) (S.index x 1)
>                 leftHash   = S.index x 0
>                 rightHash  = S.index x 1
>                 l          = MerkleInfo leftHash  (Just (Right rightHash)) (Just parentHash)
>                 r          = MerkleInfo rightHash (Just (Left  leftHash))  (Just parentHash)
>             modifySTRef' newHashListAndMap (\(hl', m') ->
>                 ( hl' |> parentHash
>                 , M.insert leftHash l (M.insert rightHash r m')))
>         readSTRef newHashListAndMap

Then, given a hash of a transaction (and the tree created above), create a path to the root.

> merklePathTo :: HashDigest -> MerkleTreeMap -> MerklePath
> merklePathTo h m = go (m ! h) []
>   where
>     go (MerkleInfo _              _    Nothing) xs = CP.reverse xs
>     go (MerkleInfo _ (Just (Left  l)) (Just p)) xs = go (m ! p) (Left  l : xs)
>     go (MerkleInfo _ (Just (Right r)) (Just p)) xs = go (m ! p) (Right r : xs)
>     go MerkleInfo {}                             _ = error "merklePathTo"

> t2 :: Spec
> t2 = do
>     txs' <- runIO (S.replicateM 15 (do rw <- randomWord randomASCII 100; return (BS.pack rw)))
>     let hashList               = CP.map C.hash txs'
>         hkData                 = S.index txs' 10
>         hK'                    = C.hash hkData
>         m                      = mkMerkleTreeMap hashList
>         -- (Left hABCDEFGH, hIJKLMNOP)
>         (MerkleInfo _ (Just (Right       hL)) (Just hKL))               = m ! hK'
>         (MerkleInfo _ (Just (Left       hIJ)) (Just hIJKL))             = m ! hKL
>         (MerkleInfo _ (Just (Right    hMNOP)) (Just hIJKLMNOP))         = m ! hIJKL
>         (MerkleInfo _ (Just (Left hABCDEFGH)) (Just hABCDEFGHIJKLMNOP)) = m ! hIJKLMNOP
>     describe "t2" $ do
>         it "root" $
>             createMerkleRoot hashList
>             `shouldBe`
>             hABCDEFGHIJKLMNOP
>         it "merklePath" $
>             merklePathTo hK' (mkMerkleTreeMap hashList)
>             `shouldBe`
>             [Right hL, Left hIJ, Right hMNOP, Left hABCDEFGH]
>         it "mkMerkleTreeMap" $
>             mkMerkleTreeMap (S.empty |> "00" |> "01" |> "02" |> "03")
>             `shouldBe`
>             M.fromList [("00",MerkleInfo { identity = "00", neighbor = Just (Right "01")
>                                          , parent = Just "\136\139\EM\164;\NAK\SYN\131\200x\149\246!\GS\159\134@\249{\220\142\243/\ETX\219\224W\200\245\229m2"})
>                        ,("01",MerkleInfo { identity = "01", neighbor = Just (Left "00")
>                                          , parent = Just "\136\139\EM\164;\NAK\SYN\131\200x\149\246!\GS\159\134@\249{\220\142\243/\ETX\219\224W\200\245\229m2"})
>                        ,("02",MerkleInfo { identity = "02", neighbor = Just (Right "03")
>                                          , parent = Just "\194Wm\216T\SUB\"\\\206\SOHTu\226\213\171\186\201\159${\145DzS\137\130n+\198'@\192"})
>                        ,("03",MerkleInfo { identity = "03", neighbor = Just (Left "02")
>                                          , parent = Just "\194Wm\216T\SUB\"\\\206\SOHTu\226\213\171\186\201\159${\145DzS\137\130n+\198'@\192"})
>                        ,("\136\139\EM\164;\NAK\SYN\131\200x\149\246!\GS\159\134@\249{\220\142\243/\ETX\219\224W\200\245\229m2",MerkleInfo {identity = "\136\139\EM\164;\NAK\SYN\131\200x\149\246!\GS\159\134@\249{\220\142\243/\ETX\219\224W\200\245\229m2", neighbor = Just (Right "\194Wm\216T\SUB\"\\\206\SOHTu\226\213\171\186\201\159${\145DzS\137\130n+\198'@\192"), parent = Just "\156\160c\144$\227\138Z\254|x\231wk\DC3 \228;\235\130:\200\DLE\\0 \131\134w\130\163\243"})
>                        ,("\194Wm\216T\SUB\"\\\206\SOHTu\226\213\171\186\201\159${\145DzS\137\130n+\198'@\192",MerkleInfo {identity = "\194Wm\216T\SUB\"\\\206\SOHTu\226\213\171\186\201\159${\145DzS\137\130n+\198'@\192", neighbor = Just (Left "\136\139\EM\164;\NAK\SYN\131\200x\149\246!\GS\159\134@\249{\220\142\243/\ETX\219\224W\200\245\229m2"), parent = Just "\156\160c\144$\227\138Z\254|x\231wk\DC3 \228;\235\130:\200\DLE\\0 \131\134w\130\163\243"})
>                        ,("\156\160c\144$\227\138Z\254|x\231wk\DC3 \228;\235\130:\200\DLE\\0 \131\134w\130\163\243",MerkleInfo {identity = "\156\160c\144$\227\138Z\254|x\231wk\DC3 \228;\235\130:\200\DLE\\0 \131\134w\130\163\243", neighbor = Nothing, parent = Nothing})]

Once the light peer receives the merkle path from the full peer it can
verify that the transaction is in the block:

> isTxInBlock :: Transaction -> MerklePath -> HashDigest -> Bool
> isTxInBlock tx mp merkleRoot = loop (C.hash tx) mp == merkleRoot
>   where
>     loop h          []  = h
>     loop h (Left  x:xs) = go x h xs
>     loop h (Right x:xs) = go h x xs
>     go x y xs           = loop (concatHash x y) xs
>
> t3 :: Spec
> t3 = do
>     txs' <- runIO (S.replicateM 15 (do rw <- randomWord randomASCII 100; return (BS.pack rw)))
>     let hashList   = CP.map C.hash txs'
>         hKTX       = S.index txs' 10
>         hK         = C.hash hKTX
>         notHKTX    = S.index txs'  9
>         merkleRoot = createMerkleRoot hashList
>         merklePath = merklePathTo hK (mkMerkleTreeMap hashList)
>     describe "t3" $ do
>         it "hK" $
>             C.hash (S.index txs' 10) `shouldBe` hK
>         it "isTxInBlock True"  $
>             isTxInBlock    hKTX merklePath merkleRoot `shouldBe` True
>         it "isTxInBlock False" $
>             isTxInBlock notHKTX merklePath merkleRoot `shouldBe` False

Credits : Mastering Bitcoin
