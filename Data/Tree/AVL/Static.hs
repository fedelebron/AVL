{-# LANGUAGE GADTs #-}
module Data.Tree.AVL.Static (
  AVLTree,
  Zipper,
  empty,
  size,
  insert,
  search,
  delete,
  value,
  begin,
  end,
  predecessor,
  successor,
) where

import Data.Tree.AVL.Static.Internal

-- |An empty 'AVLTree'.
--
-- /O(1)/.
empty :: AVLTree a
empty = T Nil 0

-- |The number of nodes of an 'AVLTree'.
--
-- /O(1)/.
size :: AVLTree a -> Integer
size (T _ k) = k

-- |Insert a value into an 'AVLTree'.
-- If the value already exists, does nothing.
--
-- /O(log n)/.
insert :: Ord a => a -> AVLTree a -> AVLTree a
insert x t = case zipTo x (unZip t) of
  Zipper Nil ctx -> insertUnbalancedAt (Balanced x Nil Nil) ctx
  _ -> t

-- |Search for a node with a given value. Returns a 'Zipper' pointing to
-- a subtree whose root has that value, or 'Nothing' if the value is not
-- in the tree.
--
-- /O(log n)/.
search :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
search x t = case zipTo x (unZip t) of
  Zipper Nil _ -> Nothing
  z -> Just z

-- |Returns a 'Zipper' to the predecessor of a value in a tree. If the input
-- 'Zipper' points to the smallest element in the tree, returns Nothing.
--
-- /O(log n)/.
predecessor :: Ord a => Zipper a -> Maybe (Zipper a)
predecessor = zipToPredecessor

-- |Returns a 'Zipper' to the successor of a value in a tree. If the input
-- 'Zipper' points to the greatest element in the tree, returns Nothing.
--
-- /O(log n)/.
successor :: Ord a => Zipper a -> Maybe (Zipper a)
successor = zipToSuccessor

-- |Deletes a value from an 'AVLTree'. If the value does not exist in the tree,
-- does nothing.
--
-- /O(log n)/.
delete :: Ord a => a -> AVLTree a -> AVLTree a
delete x t = case zipTo x (unZip t) of
  Zipper Nil _ -> t
  z -> deleteBST z

-- |Returns a 'Zipper' to the smallest element in the tree, or Nothing if the
-- tree is empty.
--
-- /O(log n)/.
begin :: AVLTree a -> Maybe (Zipper a)
begin t | size t == 0 = Nothing
        | otherwise = Just . zipToSmallest . unZip $ t

-- |Returns a 'Zipper' to the greatest element in the tree, or Nothinf if the
-- tree is empty.
--
-- /O(log n)/.
end :: AVLTree a -> Maybe (Zipper a)
end t | size t == 0 = Nothing
      | otherwise = Just . zipToGreatest . unZip $ t
