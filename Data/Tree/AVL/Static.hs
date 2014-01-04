{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
module Data.Tree.AVL.Static (
  AVLTree,
  empty,
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
empty = T Nil

insert :: Ord a => a -> AVLTree a -> AVLTree a
insert x t@(T root) = case zipTo x (unZip root) of
  Zipper Nil ctx -> insertUnbalancedAt (Balanced x Nil Nil) ctx
  _ -> t

search :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
search x (T root) = case zipTo x (unZip root) of
  Zipper Nil _ -> Nothing
  t -> Just t

predecessor :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
predecessor x t = search x t >>= zipToPredecessor

successor :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
successor x t = search x t >>= zipToSuccessor

delete :: Ord a => a -> AVLTree a -> AVLTree a
delete x t@(T root) = case zipTo x $ unZip root of
  Zipper Nil _ -> t
  z -> deleteBST z
