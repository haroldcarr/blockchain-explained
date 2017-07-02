module BTPP where

import VerifiedMap

btPretty :: (Show k) => BTree k v -> IO ()
btPretty = mapM_ putStrLn . draw
 where
  draw :: (Show k) => BTree k v -> [String]
  draw Tip                   = []
  draw (Bin k _ Tip Tip _ _) = [show k]
  draw (Bin k _ l   r   _ _) = show k : drawSubTrees [l,r]
   where
    drawSubTrees []     = []
    drawSubTrees [t]    = "|" : shift "r- " "   " (draw t)
    drawSubTrees (t:ts) = "|" : shift "l- " "|  " (draw t) ++ drawSubTrees ts
    shift first other   = zipWith (++) (first : repeat other)
