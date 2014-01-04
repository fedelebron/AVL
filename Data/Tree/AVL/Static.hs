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

-- |An empty 'AVLTree'.
empty :: AVLTree a
empty = T Nil 0

-- |The number of nodes of an 'AVLTree'.
size :: AVLTree a -> Integer
size (T _ k) = k

-- |Insert a value into an 'AVLTree'.
-- |If the value already exists, does nothing.
insert :: Ord a => a -> AVLTree a -> AVLTree a
insert x t = case zipTo x (unZip t) of
  Zipper Nil ctx -> insertUnbalancedAt (Balanced x Nil Nil) ctx
  _ -> t

-- |Search for a node with a given value. Returns a 'Zipper' pointing to
-- | a subtree whose root has that value, or 'Nothing' if the value is not
-- | in the tree.
search :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
search x t = case zipTo x (unZip t) of
  Zipper Nil _ -> Nothing
  z -> Just z

-- |Returns a 'Zipper' to the predecessor of a value in a tree.
-- |Note the value needs to exist in the tree. If the value does not exist in
-- | the tree, or it has no predecessor, returns 'Nothing'.
predecessor :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
predecessor x t = search x t >>= zipToPredecessor

-- |Returns a 'Zipper' to the successor of a value in a tree.
-- |Note the value needs to exist in the tree. If the value does not exist in
-- | the tree, or it has no successor, returns 'Nothing'.
successor :: Ord a => a -> AVLTree a -> Maybe (Zipper a)
successor x t = search x t >>= zipToSuccessor

-- |Deletes a value from an 'AVLTree'. If the value does not exist in the tree,
-- | does nothing.
delete :: Ord a => a -> AVLTree a -> AVLTree a
delete x t = case zipTo x (unZip t) of
  Zipper Nil _ -> t
  z -> deleteBST z
