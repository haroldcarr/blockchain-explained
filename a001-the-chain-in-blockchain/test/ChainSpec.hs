module ChainSpec (spec) where

import           Chain
import           Test.Hspec

spec :: Spec
spec = do
    describe "1" $ do
        it "1.1" $ do
            '1' `shouldBe` '1'
            '1' `shouldBe` '1'
        it "1.2" $ do
            '1' `shouldBe` '1'
            '1' `shouldBe` '1'
    describe "2" $ do
        it "2.1" $ do
            '1' `shouldBe` '1'
            '1' `shouldBe` '1'
        it "2.2" $ do
            '1' `shouldBe` '1'
            '1' `shouldBe` '1'
