{-# LANGUAGE TemplateHaskell #-}

module Main where

import Test.QuickCheck
import Test.QuickCheck.All
import Data.Foldable (toList)
import Data.Tree.AVL.Static
import Data.Maybe
import System.Exit
import Data.List (nub, sort)

instance (Arbitrary a, Ord a) => Arbitrary (AVLTree a) where
  arbitrary = do
    n <- choose (0, 100)
    xs <- vector n
    return $ foldr insert empty xs
  shrink t = let xs = toList t
             in map (flip delete t) xs

prop_sizeEmpty = size empty == 0

prop_sizeInserted :: NonNegative Integer -> Bool
prop_sizeInserted (NonNegative k) = size (foldr insert empty [1..k]) == k

prop_toList xs = toList (foldr insert empty xs) == nub (sort xs)

prop_insertDelete t x = (isNothing $ search x t) ==>
                        toList (delete x (insert x t)) == toList t

prop_searchAfterInsert x t = (isNothing $ search x t) ==>
                             isJust . search x $ insert x t

prop_searchAfterDelete t x = (isJust $ search x t) ==>
                             isNothing . search x $ delete x t

prop_successor t = let z = begin t
                       zs = takeWhile isJust $ iterate (>>= successor) z
                       d = map value (catMaybes zs)
                   in toList t == d &&
                        sort d == d

prop_predecessor t = let z = end t
                         zs = takeWhile isJust $ iterate (>>= predecessor) z
                         d = reverse . map value $ catMaybes zs
                     in toList t == d &&
                          sort d == d

main = do
  result <- $(quickCheckAll)
  if result
  then exitSuccess
  else exitFailure
