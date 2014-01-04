{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
module Data.Tree.AVL.Static (
  AVLTree,
  empty,
  size,
  delete,
  value,
  insert,
  search,
  predecessor,
  successor,
  Zipper
) where

import Data.Tree.AVL.Static.Internal

empty :: AVLTree a
empty = T Nil 0

size :: AVLTree a -> Integer
size (T _ k) = k

insert :: Ord a => a -> AVLTree a -> AVLTree a
insert x t = case zipTo x (unZip t) of
  Zipper Nil ctx -> insertUnbalancedAt (Balanced x Nil Nil) ctx
  _ -> t

search :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
search x t = case zipTo x (unZip t) of
  Zipper Nil _ -> Nothing
  z -> Just z

predecessor :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
predecessor x t = search x t >>= zipToPredecessor

successor :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
successor x t = search x t >>= zipToSuccessor

delete :: Ord a => a -> AVLTree a -> AVLTree a
delete x t = case zipTo x (unZip t) of
  Zipper Nil _ -> t
  z -> deleteBST z
