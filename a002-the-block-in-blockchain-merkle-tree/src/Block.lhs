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

> {-# ANN module ("HLint: ignore Eta reduce"::String) #-}
> {-# ANN module ("HLint: ignore Reduce duplication"::String) #-}

> type BHash      = ByteString
> type BTimestamp = ByteString

> data BlockHeader =
>     BlockHeader {
>           bPrevHash   :: ! BHash      -- ^ hash of previous block
>         , bMerkleRoot :: ! BHash      -- ^ hash of root of this block's transactions
>         , bTimestamp  :: ! BTimestamp -- ^ when this block was created
>     } deriving (Eq, Show)

> type BData        = ByteString
> type Transactions = Seq BData

> data Block =
>     Block {
>           header :: ! BlockHeader
>         , txs    :: ! Transactions
>     } deriving (Eq, Show)

> type HashList   = Seq HashDigest
> type HashDigest = ByteString

> nullHash :: HashDigest
> nullHash = BS.replicate 32 (chr 0)

> concatHash :: HashDigest -> HashDigest -> HashDigest
> concatHash x y = C.hash (x <> y)

> createMerkleRoot :: HashList -> HashDigest
> createMerkleRoot hashList0
>     | S.null hashList0 = nullHash
>     | otherwise        = runST $ do
>         m <- newSTRef hashList0
>         loop m
>   where
>     loop m = do
>         hashList <- readSTRef m
>         if S.length hashList == 1 then
>             return (S.index hashList 0)
>         else do
>             -- when odd then duplicate last hash
>             when (odd $ S.length hashList) $
>                 modifySTRef m (|> S.index hashList (S.length hashList - 1))
>             newHashList <- newSTRef S.empty
>             hashList'   <- readSTRef m
>             -- Make newHashList (1/2 size of given hashList)
>             -- where every element of newHashList is made
>             -- by taking adjacent pairs of given hashList
>             -- and concatenating their contents
>             -- then hashing that concatenated contents.
>             forM_ (S.chunksOf 2 hashList') $ \x ->
>                 modifySTRef' newHashList (|> concatHash (S.index x 0) (S.index x 1))
>             loop newHashList

This version also returns a map of (hash -> (child hash, child hash) for testing.

> createMerkleRootAndMap :: HashList -> (HashDigest, M.Map HashDigest (HashDigest, HashDigest))
> createMerkleRootAndMap hashList0
>     | S.null hashList0 = (nullHash, M.empty)
>     | otherwise        = runST $ do
>         hl <- newSTRef (hashList0, M.empty)
>         loop hl
>   where
>     loop hl = do
>         (hashList, m) <- readSTRef hl
>         if S.length hashList == 1 then
>             return (S.index hashList 0, m)
>         else do
>             -- when odd then duplicate last hash
>             when (odd $ S.length hashList) $
>                 modifySTRef hl (\(hl',m') -> (hl' |> S.index hashList (S.length hashList - 1), m'))
>             newHashList   <- newSTRef (S.empty, m)
>             (hashList',_) <- readSTRef hl
>             -- Make newHashList (1/2 size of given hashList)
>             -- where every element of newHashList is made
>             -- by taking adjacent pairs of given hashList
>             -- and concatenating their contents
>             -- then hashing that concatenated contents.
>             forM_ (S.chunksOf 2 hashList') $ \x -> do
>                 let h = concatHash (S.index x 0) (S.index x 1)
>                 modifySTRef' newHashList (\(hl',m') ->
>                     ( hl' |> h
>                     , M.insert h (S.index x 0, S.index x 1) m'))
>             loop newHashList

> merklePathTo :: HashList -> M.Map HashDigest HashDigest
> merklePathTo hashList0
>     | S.null hashList0 = M.empty
>     | otherwise        = runST $ do
>         hl <- newSTRef (hashList0, M.empty)
>         loop hl
>   where
>     loop hl = do
>         (hashList, m) <- readSTRef hl
>         if S.length hashList == 1 then
>             return m
>         else do
>             -- when odd then duplicate last hash
>             when (odd $ S.length hashList) $
>                 modifySTRef hl (\(hl',m') -> (hl' |> S.index hashList (S.length hashList - 1), m'))
>             newHashList   <- newSTRef (S.empty, m)
>             (hashList',_) <- readSTRef hl
>             forM_ (S.chunksOf 2 hashList') $ \x -> do
>                 let parentHash = concatHash (S.index x 0) (S.index x 1)
>                     leftHash   = S.index x 0
>                     rightHash  = S.index x 1
>                     m1         = M.insert leftHash  parentHash m
>                     m2         = M.insert rightHash parentHash m1
>                 modifySTRef' newHashList (\(hl',_) -> ( hl' |> parentHash, m2))
>             loop newHashList

> t1 :: Spec
> t1 =
>     let one   = S.empty |> C.hash "00"
>         two   = one     |> C.hash "01"
>         three = two     |> C.hash "11"
>     in describe "t1" $ do
>         it "empty"    $ createMerkleRoot S.empty `shouldBe` nullHash
>         it "one"      $ createMerkleRoot one
>                       `shouldBe`
>                       "\241SC\146'\155\221\191\157C\221\232p\FS\181\190\DC4\184/v\236f\a\191\141j\213W\246\SI0N"
>         it "two"      $ createMerkleRoot two
>                       `shouldBe`
>                       "\196\215\&1\182\164\&2\SUBcsV\166 <\163\t\242W\t>\GS\149\195\164\241\222\225j\r\DC4gGB"
>         it "three"    $ createMerkleRoot three
>                       `shouldBe`
>                       "\253x\148`\EOT\205W\"\179\148\210\152_l\147J\145\155\to\210\136mI{\193U\253\RSkb\226"

> isTxInBlock :: ByteString -> [Either HashDigest HashDigest] -> HashDigest -> Bool
> isTxInBlock tx mp mr = loop (C.hash tx) mp == mr
>   where
>     loop h          []  = h
>     loop h (Left  x:xs) = go x h xs
>     loop h (Right x:xs) = go h x xs
>     go x y xs           = loop (concatHash x y) xs

> t2 :: Spec
> t2 = do
>     txs' <- runIO (S.replicateM 15 (do rw <- randomWord randomASCII 100; return (BS.pack rw)))
>     let txHashs                = CP.map C.hash txs'
>         (root, m)              = createMerkleRootAndMap txHashs
>         (hABCDEFGH, hIJKLMNOP) = m ! root
>         (hIJKL    , hMNOP)     = m ! hIJKLMNOP
>         (hIJ      , hKL)       = m ! hIJKL
>         (hK       , hL)        = m ! hKL
>         hkData                 = S.index txs' 10
>         hK'                    = C.hash hkData
>         merklePath             = [Right hL, Left hIJ, Right hMNOP, Left hABCDEFGH]
>     describe "t1" $ do
>         it "hK" $ hK' `shouldBe` hK
>         it "merklePath" $ merklePath `shouldBe` merklePath
>         it "isTxInBlock" $ isTxInBlock hkData merklePath root `shouldBe` True

{-
import           Crypto.Hash.SHA256    as C  (hash)
import           Data.Sequence         as S
:set -XOverloadedStrings
hashList = S.empty |> C.hash "00" |> C.hash "01" |> C.hash "11"
:b createMerkleRoot
createMerkleRoot hashList
-}
