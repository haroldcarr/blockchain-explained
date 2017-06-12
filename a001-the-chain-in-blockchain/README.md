the chain in blockchain explained
---------------------------------

setup:

``` {.sourceCode .literate .haskell}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module Chain where

import           ClassyPrelude
import           Crypto.Hash.SHA256    as C (hash)
import           Data.ByteString       as BS (concat)
import           Data.ByteString.Char8 as BS (pack)
import           Data.Sequence         as S
import           Test.Hspec
```

The most straigtforward part of a blockchain is the chain itself, a
sequence of blocks:

``` {.sourceCode .literate .haskell}
type Blockchain = Seq Block
```

For the purposes of this exposition, a block in the chain is:

``` {.sourceCode .literate .haskell}
data Block =
  Block { bIndex        :: ! Int        -- ^ index of this block in the chain
        , bPreviousHash :: ! BHash      -- ^ hash of previous block
        , bTimestamp    :: ! BTimestamp -- ^ when this block was created
        , bData         :: ! BData      -- ^ this block's data
        , bHash         :: ! BHash      -- ^ this block's hash
        } deriving (Eq, Show)
```

where

``` {.sourceCode .literate .haskell}
type BHash      = ByteString
type BTimestamp = ByteString
type BData      = ByteString
```

A genesis block:

``` {.sourceCode .literate .haskell}
genesisBlock :: Block
genesisBlock =
 let idx      = 0
     prevHash = "0"
     ts       = "2017-03-05 10:49:02.084473 PST"
     bdata    = "GENESIS BLOCK DATA"
     bhash    = calculateHash idx prevHash ts bdata
 in Block idx prevHash ts bdata bhash
```

begins the chain:

``` {.sourceCode .literate .haskell}
genesisBlockchain :: Blockchain
genesisBlockchain  = S.singleton genesisBlock
```

The chain is tamper-proof because each block contains a hash of its
contents.

``` {.sourceCode .literate .haskell}
calculateHash :: Int -> BHash -> BTimestamp -> BData
              -> BHash
calculateHash i p t d = C.hash (BS.concat [BS.pack $ show i, p, t, d])
```

Since a block's contents includes the hash of the previous block, once a
block has been added to a chain, neither the block nor the previous
contents of the chain can be altered.

For example, using the following functions:

``` {.sourceCode .literate .haskell}
addBlock :: BTimestamp -> BData -> Blockchain
         -> Blockchain
addBlock ts bd bc =
  let newBlock = makeNextBlock bc ts bd
  in bc |> newBlock

makeNextBlock :: Blockchain -> BTimestamp -> BData
              -> Block
makeNextBlock blockchain tstamp bdata =
 let (i, ph, _, _, h) = makeNextBlockInfo blockchain tstamp bdata
 in Block i ph tstamp bdata h

makeNextBlockInfo :: Blockchain -> BTimestamp -> BData
                  -> (Int, BHash, BTimestamp, BData, BHash)
makeNextBlockInfo blockchain tstamp bdata =
  let prev = getLastCommittedBlock blockchain
      i    = bIndex prev + 1
      ph   = bHash prev
  in (i, ph, tstamp, bdata, calculateHash i ph tstamp bdata)

getLastCommittedBlock :: Blockchain
                      -> Block
getLastCommittedBlock bc =
  let i = S.length bc - 1
  in fromMaybe (error "getLastCommittedBlock") (getBlock bc i)
```

a new block may be added to the chain:

``` {.sourceCode .literate .haskell}
t1 :: Spec
t1 =
  let newChain = addBlock "2017-06-11 15:49:02.084473 PST"
                          "June 11 data"
                          genesisBlockchain
  in describe "t1: add new block to chain" $ do
       it "increases length" $
         S.length newChain `shouldBe` S.length genesisBlockchain + 1
       it "does not change existing blocks" $
         getBlock newChain 0 `shouldBe` Just genesisBlock
```

where

``` {.sourceCode .literate .haskell}
-- | Nothing if index out of range.
getBlock :: Blockchain -> Int
         -> Maybe Block
getBlock blockchain i | i < S.length blockchain = Just (S.index blockchain i)
                      | otherwise               = Nothing
```

The chained block hashes ensure the integrity of a blockchain:

``` {.sourceCode .literate .haskell}
t2 :: Spec
t2 =
  let newChain = addBlock "2017-06-12 15:49:02.084473 PST"
                          "June 12 data"
                          (addBlock "2017-06-11 15:49:02.084473 PST"
                                    "June 11 data"
                                    genesisBlockchain)
      altered1i  = (S.index newChain 1) { bIndex = 10 }
      badChain1i = S.update 1 altered1i newChain
      altered1p  = (S.index newChain 1) { bPreviousHash = "0" }
      badChain1p = S.update 1 altered1p newChain
      altered1d  = (S.index newChain 1) { bData  = "altered June 11 data" }
      badChain1d = S.update 1 altered1d newChain
      altered12  = (S.index newChain 2) { bData  = "altered June 12 data" }
      badChain12 = S.update 2 altered12 newChain
  in describe "t2: valid blockchain" $ do
    it "invalid empty" $
      isValidBlockchain S.empty    `shouldBe` Just "empty blockchain"
    it "valid genesisblockchain" $
      isValidBlockchain genesisBlockchain
                                   `shouldBe` Nothing
    it "invalid genesisblock" $
      isValidBlockchain (S.singleton altered12)
                                   `shouldBe` Just "invalid genesis block"
    it "valid newChain" $
      isValidBlockchain newChain   `shouldBe` Nothing
    it "invalid bIndex 1" $
      isValidBlockchain badChain1i `shouldBe` Just "invalid bIndex 1"
    it "invalid bPreviousHash 1" $
      isValidBlockchain badChain1p `shouldBe` Just "invalid bPreviousHash 1"
    it "invalid bHash 1" $
      isValidBlockchain badChain1d `shouldBe` Just "invalid bHash 1"
    it "invalid bHash 2" $
      isValidBlockchain badChain12 `shouldBe` Just "invalid bHash 2"
```

where

``` {.sourceCode .literate .haskell}
-- | Returns Nothing if valid.
-- Just reason if invalid
isValidBlockchain :: Blockchain
                  -> Maybe Text
isValidBlockchain bc
  | S.length bc == 0 = Just "empty blockchain"
  | S.length bc == 1 = if S.index bc 0 == genesisBlock then Nothing
                       else Just "invalid genesis block"
  | otherwise        = isvb 0
 where
  isvb i | i == S.length bc - 1 =  Nothing
         | otherwise            =  isValidBlock (S.index bc i) (S.index bc (i + 1))
                               <|> isvb (i + 1)

-- | Given a valid previous block and a block to check.
-- Returns Nothing if valid.
-- Just reason if invalid
isValidBlock :: Block -> Block
             -> Maybe Text
isValidBlock validBlock checkBlock
  | biv + 1              /= bic                      = err "invalid bIndex"
  | bHash validBlock     /= bPreviousHash checkBlock = err "invalid bPreviousHash"
  | calculateHashForBlock checkBlock
                         /= bHash checkBlock         = err "invalid bHash"
  | otherwise                                        = Nothing
 where
  biv = bIndex validBlock
  bic = bIndex checkBlock
  err msg = Just (msg <> " " <> tshow (biv + 1))

calculateHashForBlock :: Block
                      -> BHash
calculateHashForBlock b =
  calculateHash (bIndex b) (bPreviousHash b) (bTimestamp b) (bData b)
```

The above is the essence of the chain in blockchain.

Note that there was no discussion of

-   how to decide to add a block to a chain (e.g., mining, consensus)
-   merkle trees (i.e., an efficient, tamper-proof way to structure
    `bData` to hold more than one "transaction")
-   smart contracts (i.e., how to interpret the `bData` field in a
    `Block`)

A blockchain is a list of blocks, where each block

-   contains data that may be interpreted as smart contracts
-   contains the hash of the previous block
-   contains a hash of itself
    -   the fact that the self hash is created with the previous hash
        makes the chain tamper-proof

``` {.sourceCode .literate .haskell}
t3 :: Spec
t3 =
  let withOne = addBlock "2017-06-11 15:49:02.084473 PST"
                         "June 11 data"
                         genesisBlockchain
      withTwo = addBlock "2017-06-12 15:49:02.084473 PST"
                         "June 12 data"
                         withOne
  in describe "t3: list" $
     it "withTwo" $
     withTwo `shouldBe`
     S.fromList
     [ Block { bIndex = 0
             , bPreviousHash = "0"
             , bTimestamp = "2017-03-05 10:49:02.084473 PST"
             , bData = "GENESIS BLOCK DATA"
             , bHash = "'\234-\147\141\"\142\235\CAN \246\158<\159\199s\174\\\225<\174\188O\150oM\217\DC3'\237\DC4n"
             }
     , Block { bIndex = 1
             , bPreviousHash = "'\234-\147\141\"\142\235\CAN \246\158<\159\199s\174\\\225<\174\188O\150oM\217\DC3'\237\DC4n"
             , bTimestamp = "2017-06-11 15:49:02.084473 PST"
             , bData = "June 11 data"
             , bHash = "\145\238k24\175\147I\EOT\208\204\210\190s\192<b:\SOH\215\DC1\254)\173\EOT\186\220\US\SYNf\191\149"
             }
     , Block { bIndex = 2
             , bPreviousHash = "\145\238k24\175\147I\EOT\208\204\210\190s\192<b:\SOH\215\DC1\254)\173\EOT\186\220\US\SYNf\191\149"
             , bTimestamp = "2017-06-12 15:49:02.084473 PST"
             , bData = "June 12 data"
             , bHash = "\172\DEL\f\158e\DC4\159Us\188ny\235\v\146\201\138\244\179w\160\151\196;\203\165\232\145\156X\206$"
             }
     ]
```

The code for this exposition is available at :
https://github.com/haroldcarr/blockchain-explained/tree/master/a001-the-chain-in-blockchain

A discussion is at: \*\*\*\*\* TODO \*\*\*\*\*
