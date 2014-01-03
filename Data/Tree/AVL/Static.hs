{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
module Data.Tree.AVL.Static (
  AVLTree,
  empty,
  delete,
  get,
  insert,
  search,
  predecessor,
  successor,
  Iterator
) where

import Data.Tree.AVL.Static.Internal

data Iterator a = forall m. Iterator (Zipper m a)
get :: Iterator a -> a
get (Iterator z) = value z

empty :: AVLTree a
empty = T Nil

insert :: Ord a => a -> AVLTree a -> AVLTree a
insert x t@(T root) = case zipTo x (unZip root) of
  Zipper Nil ctx -> insertUnbalancedAt (Balanced x Nil Nil) ctx
  _ -> t

search :: Ord a => a -> AVLTree a -> Maybe (Iterator a)
search x (T root) = case zipTo x (unZip root) of
  Zipper Nil _ -> Nothing
  t -> Just (Iterator t)

predecessor :: Ord a => a -> AVLTree a -> Maybe (Iterator a)
predecessor x t = do
                    Iterator z <- search x t
                    p <- zipToPredecessor z
                    return $ Iterator p

successor :: Ord a => a -> AVLTree a -> Maybe (Iterator a)
successor x t = do
                  Iterator z <- search x t
                  p <- zipToSuccessor z
                  return $ Iterator p

delete :: Ord a => a -> AVLTree a -> AVLTree a
delete x t@(T root) = case zipTo x $ unZip root of
  Zipper Nil _ -> t
  z -> deleteBST z
