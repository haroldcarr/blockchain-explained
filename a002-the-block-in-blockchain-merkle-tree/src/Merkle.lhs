the block in blockchain explained (merkle trees)
---------------------------------

setup:

> {-# LANGUAGE NoImplicitPrelude #-}
> {-# LANGUAGE OverloadedStrings #-}
>
> module Merkle where
>
> import           ClassyPrelude           as CP
> import           Control.Monad.ST.Strict (runST)
> import           Crypto.Hash.SHA256      as C  (hash)
> import           Data.ByteString.Char8   as BS (replicate)
> import           Data.Char               (chr)
> import           Data.Sequence           as S
> import           Data.STRef.Strict
> import           Test.Hspec

> type HashList   = Seq ByteString
> type HashDigest = ByteString

> nullHash :: HashDigest
> nullHash = BS.replicate 32 (chr 0)

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
>                 modifySTRef' newHashList (|> C.hash (S.index x 0 <> S.index x 1))
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

{-
import           Crypto.Hash.SHA256    as C  (hash)
import           Data.Sequence         as S
:set -XOverloadedStrings
hashList = S.empty |> C.hash "00" |> C.hash "01" |> C.hash "11"
:b createMerkleRoot
createMerkleRoot hashList
-}
