{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}

module Data.Tree.AVL.Static.Internal (
  AVLNode(..),
  AVLTree(T),
  insertUnbalancedAt,
  unZip,
  value,
  zipTo,
  zipToSmallest,
  zipToPredecessor,
  zipToSuccessor,
  Zipper(Zipper)
) where

import Control.Applicative ((<$>), (<*>))
import Data.Maybe (Maybe(..))

data Nat = Zero | Succ Nat deriving (Eq, Ord, Show)

data AVLNode :: Nat -> * -> * where
  Nil :: AVLNode Zero a
  Leftie :: a -> AVLNode (Succ n) a -> AVLNode n a -> AVLNode (Succ (Succ n)) a
  Rightie :: a -> AVLNode n a -> AVLNode (Succ n) a -> AVLNode (Succ (Succ n)) a
  Balanced :: a -> AVLNode n a -> AVLNode n a -> AVLNode (Succ n) a

deriving instance Show a => Show (AVLNode n a)

data AVLTree a = forall n. T (AVLNode n a)
deriving instance Show a => Show (AVLTree a)

{- Context for a Zipper.
 - BC = Balanced Context,
 - xyC = xie Context, having gone through the y branch.
 -       For instance, LRC means a Leftie context, where one has taken the Right
 -       path in the subtree. -}

data Context :: Nat -> Nat -> * -> * where
  BC :: Bool -> a -> AVLNode n a -> Context m (Succ n) a -> Context m n a
  LRC :: a -> AVLNode (Succ n) a -> Context m (Succ (Succ n)) a -> Context m n a
  LLC :: a -> AVLNode n a -> Context m (Succ (Succ n)) a -> Context m (Succ n) a
  RLC :: a -> AVLNode (Succ n) a -> Context m (Succ (Succ n)) a -> Context m n a
  RRC :: a -> AVLNode n a -> Context m (Succ (Succ n)) a -> Context m (Succ n) a
  Root :: Context n n a
deriving instance Show a => Show (Context m n a)

data Zipper m a = forall n. Zipper (AVLNode n a) (Context m n a)
deriving instance Show a => Show (Zipper m a)

value :: Zipper m a -> a
value (Zipper (Balanced x _ _) _) = x
value (Zipper (Leftie x _ _) _) = x
value (Zipper (Rightie x _ _) _) = x
value (Zipper Nil _) = error "Zipper points to Nil."

unZip :: AVLNode m a -> Zipper m a
unZip = flip Zipper Root

zipUp :: Zipper m a -> AVLNode m a
zipUp (Zipper t Root) = t
zipUp z = zipUp $ up z

up :: Zipper m a -> Zipper m a
up (Zipper x (LRC v y ctx)) = Zipper (Leftie v y x) ctx
up (Zipper x (LLC v y ctx)) = Zipper (Leftie v x y) ctx
up (Zipper x (RLC v y ctx)) = Zipper (Rightie v x y) ctx
up (Zipper x (RRC v y ctx)) = Zipper (Rightie v y x) ctx
up (Zipper x (BC True v y ctx)) = Zipper (Balanced v x y) ctx
up (Zipper x (BC False v y ctx)) = Zipper (Balanced v y x) ctx
-- TODO: Should I error out on Root?
up (Zipper x Root) = Zipper x Root

canGoUp :: Zipper m a -> Bool
canGoUp (Zipper _ Root) = False
canGoUp _ = True

left :: Zipper m a -> Zipper m a
left z@(Zipper (Balanced _ Nil _) ctx) = z
left (Zipper (Balanced x l r) ctx) = Zipper l (BC True x r ctx)
left (Zipper (Leftie x l r) ctx) = Zipper l (LLC x r ctx)
left z@(Zipper (Rightie _ Nil _) ctx) = z
left (Zipper (Rightie x l r) ctx) = Zipper l (RLC x r ctx)
-- TODO: Should I error out on Nil?
left z = z

right :: Zipper m a -> Zipper m a
right z@(Zipper (Balanced _ _ Nil) ctx) = z
right z@(Zipper (Leftie _ _ Nil) ctx) = z
right (Zipper (Rightie x l r) ctx) = Zipper r (RRC x l ctx)
right (Zipper (Leftie x l r) ctx) = Zipper r (LRC x l ctx)
right (Zipper (Balanced x l r) ctx) = Zipper r (BC False x l ctx)
-- TODO: Should I error out on Nil?
right z = z

canGoLeft :: Zipper m a -> Bool
canGoLeft (Zipper (Rightie _ Nil _) _) = False
canGoLeft (Zipper (Balanced _ Nil _) _) = False
canGoLeft (Zipper Nil _) = False
canGoLeft _ = True

canGoRight :: Zipper m a -> Bool
canGoRight (Zipper (Leftie _ _ Nil) _) = False
canGoRight (Zipper (Balanced _ _ Nil) _ ) = False
canGoRight (Zipper Nil _) = False
canGoRight _ = True

isLeft :: Zipper m a -> Bool
isLeft z | not (canGoUp z) = False
isLeft (Zipper _ (BC False _ _ _)) = False
isLeft (Zipper _ (RRC _ _ _)) = False
isLeft (Zipper _ (LRC _ _ _ )) = False
isLeft _ = True

isRight :: Zipper m a -> Bool
isRight = (&&) <$> canGoUp <*> (not . isLeft)

zipTo :: Ord a => a -> Zipper m a -> Zipper m a
zipTo x z@(Zipper (Balanced v l r) ctx) = case compare x v of
                                  EQ -> z
                                  LT -> zipTo x $ Zipper l (BC True v r ctx)
                                  GT -> zipTo x $ Zipper r (BC False v l ctx)
zipTo x z@(Zipper (Leftie v l r) ctx) = case compare x v of
                                  EQ -> z
                                  LT -> zipTo x $ Zipper l (LLC v r ctx)
                                  GT -> zipTo x $ Zipper r (LRC v l ctx)
zipTo x z@(Zipper (Rightie v l r) ctx) = case compare x v of
                                  EQ -> z
                                  LT -> zipTo x $ Zipper l (RLC v r ctx)
                                  GT -> zipTo x $ Zipper r (RRC v l ctx)
zipTo x z = z

insertUnbalancedAt :: forall m a n. AVLNode (Succ n) a -> Context m n a -> AVLTree a
insertUnbalancedAt t (LRC v y ctx) = T . zipUp $ Zipper (Balanced v y t) ctx
insertUnbalancedAt t (RLC v y ctx) = T . zipUp $ Zipper (Balanced v t y) ctx
insertUnbalancedAt t Root = T t

{- LLC -}
insertUnbalancedAt (Leftie b g p) (LLC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced b g (Balanced a p d)) ctx
insertUnbalancedAt (Rightie b g (Rightie p t1 t2)) (LLC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced p (Leftie b g t1) (Balanced a t2 d)) ctx
insertUnbalancedAt (Rightie b g (Leftie p t1 t2)) (LLC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced p (Balanced b g t1) (Rightie a t2 d)) ctx
insertUnbalancedAt (Rightie b g (Balanced p t1 t2)) (LLC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced p (Balanced b g t1) (Balanced a t2 d)) ctx
insertUnbalancedAt (Balanced b g p) (LLC a d ctx) = goUp
  where
    goUp = insertUnbalancedAt (Rightie b g (Leftie a p d)) ctx

{- RRC -}
insertUnbalancedAt (Rightie b g p) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced b (Balanced a d g) p) ctx
insertUnbalancedAt (Leftie b (Leftie g t1 t2) p) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced g (Balanced a d t1) (Rightie b t2 p)) ctx
insertUnbalancedAt (Leftie b (Rightie g t1 t2) p) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced g (Leftie a d t1) (Balanced b t2 p)) ctx
insertUnbalancedAt (Leftie b (Balanced g t1 t2) p) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced g (Balanced a d t1) (Balanced b t2 p)) ctx
insertUnbalancedAt (Balanced b p g) (RRC a d ctx) = goUp
  where
    goUp = insertUnbalancedAt (Leftie b (Rightie a d p) g) ctx

{- BC -}
insertUnbalancedAt (Leftie b g p) (BC True a d ctx) = goUp
  where
    goUp = insertUnbalancedAt (Rightie b g (Rightie a p d)) ctx
insertUnbalancedAt (Rightie b g p) (BC False a d ctx) = goUp
  where
    goUp = insertUnbalancedAt (Leftie b (Leftie a d g) p) ctx
insertUnbalancedAt t (BC False a d ctx) = insertUnbalancedAt (Rightie a d t) ctx
insertUnbalancedAt t (BC True a d ctx) = insertUnbalancedAt (Leftie a t d) ctx

zipToSuccessor :: Zipper m a -> Maybe (Zipper m a)
zipToSuccessor z | canGoRight z = Just . zipToSmallest $ right z
                 | otherwise = let parent = zipToFirstLeftChild z
                               in  up <$> parent
zipToPredecessor :: Zipper m a -> Maybe (Zipper m a)
zipToPredecessor z | canGoLeft z = Just . zipToSmallest $ left z
                   | otherwise = let parent = zipToFirstRightChild z
                                 in up <$> parent

zipToSmallest :: Zipper m a -> Zipper m a
zipToSmallest z | canGoLeft z = zipToSmallest (left z)
                | otherwise = z

zipToGreatest :: Zipper m a -> Zipper m a
zipToGreatest z | canGoRight z = zipToGreatest (right z)
                | otherwise = z

zipToFirstLeftChild :: Zipper m a -> Maybe (Zipper m a)
zipToFirstLeftChild z | isLeft z = Just z
zipToFirstLeftChild z | canGoUp z = zipToFirstLeftChild (up z)
                      | otherwise = Nothing

zipToFirstRightChild :: Zipper m a -> Maybe (Zipper m a)
zipToFirstRightChild z | isRight z = Just z
zipToFirstRightChild z | canGoUp z = zipToFirstRightChild (up z)
                       | otherwise = Nothing
