{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Tree.AVL.Static.Internal (
  AVLNode(..),
  AVLTree(T),
  insertUnbalancedAt,
  deleteBST,
  unZip,
  value,
  zipTo,
  zipToSmallest,
  zipToPredecessor,
  zipToSuccessor,
  Zipper(Zipper)
) where

import Control.Applicative ((<$>), (<*>))

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
left (Zipper (Balanced x l r) ctx) = Zipper l (BC True x r ctx)
left (Zipper (Leftie x l r) ctx) = Zipper l (LLC x r ctx)
left (Zipper (Rightie x l r) ctx) = Zipper l (RLC x r ctx)
-- TODO: Should I error out on Nil?
left z = z

right :: Zipper m a -> Zipper m a
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

isLeaf :: Zipper m a -> Bool
isLeaf = (&&) <$> (not . canGoLeft) <*> (not . canGoRight)

zipTo :: Ord a => a -> Zipper m a -> Zipper m a
zipTo _ z@(Zipper Nil _) = z
zipTo x z = let v = value z
            in case compare x v of
                 EQ -> z
                 LT -> zipTo x $ left z
                 GT -> zipTo x $ right z

insertUnbalancedAt :: AVLNode (Succ n) a -> Context m n a -> AVLTree a
insertUnbalancedAt t (LRC v y ctx) = T . zipUp $ Zipper (Balanced v y t) ctx
insertUnbalancedAt t (RLC v y ctx) = T . zipUp $ Zipper (Balanced v t y) ctx
insertUnbalancedAt t Root = T t

{- LLC -}
insertUnbalancedAt (Leftie b g p) (LLC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced b g (Balanced a p d)) ctx
insertUnbalancedAt (Rightie b g q) (LLC a d ctx) = T $ zipUp z
  where
    z = Zipper t ctx
    t = case q of
          Rightie p t1 t2 -> Balanced p (Leftie b g t1) (Balanced a t2 d)
          Leftie p t1 t2 -> Balanced p (Balanced b g t1) (Rightie a t2 d)
          Balanced p t1 t2 -> Balanced p (Balanced b g t1) (Balanced a t2 d)
insertUnbalancedAt (Balanced b g p) (LLC a d ctx) = goUp
  where
    goUp = insertUnbalancedAt (Rightie b g (Leftie a p d)) ctx

{- RRC -}
insertUnbalancedAt (Rightie b g p) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced b (Balanced a d g) p) ctx
insertUnbalancedAt (Leftie b q p) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper t ctx
    t = case q of
          Leftie g t1 t2 -> Balanced g (Balanced a d t1) (Rightie b t2 p)
          Rightie g t1 t2 -> Balanced g (Leftie a d t1) (Balanced b t2 p)
          Balanced g t1 t2 -> Balanced g (Balanced a d t1) (Balanced b t2 p)
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

fixContext :: forall m a n. Eq a => Context m n a -> a -> a -> Context m n a
fixContext ctx k k' = go ctx
  where
    z x = if x == k then k' else x
    go :: Context m' n' a -> Context m' n' a
    go Root = Root
    go (BC goLeft x y ctx) = BC goLeft (z x) y (go ctx)
    go (LLC x y ctx) = LLC (z x) y (go ctx)
    go (LRC x y ctx) = LRC (z x) y (go ctx)
    go (RRC x y ctx) = RRC (z x) y (go ctx)
    go (RLC x y ctx) = RLC (z x) y (go ctx)

deleteBST :: Eq a => Zipper m a -> AVLTree a
deleteBST (Zipper (Balanced _ Nil Nil) ctx) = rebalance Nil ctx
deleteBST (Zipper (Rightie _ Nil r) ctx) = rebalance r ctx
deleteBST (Zipper (Leftie _ l Nil) ctx) = rebalance l ctx
deleteBST z@(Zipper (Rightie k _ r) ctx) =
  let Just s = zipToSuccessor (right z)
  in case s of
       Zipper (Balanced k' Nil Nil) ctx' -> rebalance Nil (fixContext ctx' k k')
       Zipper (Rightie k' Nil r) ctx' -> rebalance r (fixContext ctx' k k')
       _ -> error "The impossible has happened, bad successor found."
deleteBST z@(Zipper (Leftie k l _) ctx) =
  let Just s = zipToPredecessor (left z)
  in case s of
       Zipper (Balanced k' Nil Nil) ctx' -> rebalance Nil (fixContext ctx' k k')
       Zipper (Leftie k' l Nil) ctx' -> rebalance l (fixContext ctx' k k')
       _ -> error "The impossible has happened, bad predecessor found."

rebalance :: forall m a n. AVLNode n a -> Context m (Succ n) a -> AVLTree a
rebalance t Root = T t
rebalance t (BC True a d ctx) = T . zipUp $ Zipper (Rightie a t d) ctx
rebalance t (BC False a d ctx) = T . zipUp $ Zipper (Leftie a d t) ctx
rebalance t (LLC a d ctx) = rebalance (Balanced a t d) ctx
rebalance t (RRC a d ctx) = rebalance (Balanced a d t) ctx
rebalance t (RLC a (Balanced d t1 t2) ctx) = T . zipUp $ z
  where
    z = Zipper (Leftie d (Rightie a t t1) t2) ctx
rebalance t (RLC a (Rightie d t1 t2) ctx) = rebalance z ctx
  where
    z = Balanced d (Balanced a t t1) t2
rebalance t (RLC a (Leftie d q t2) ctx) = rebalance z ctx
  where
    z = case q of
          Leftie t1 p1 p2 -> Balanced t1 (Balanced a t p1) (Rightie d p2 t2)
          Rightie t1 p1 p2 ->  Balanced t1 (Leftie a t p1) (Balanced d p2 t2)
          Balanced t1 p1 p2 -> Balanced t1 (Balanced a t p1) (Balanced d p2 t2)
rebalance t (LRC a (Balanced d t1 t2) ctx) = T . zipUp $ z
  where
    z = Zipper (Rightie d t1 (Leftie a t2 t)) ctx
rebalance t (LRC a (Leftie d t1 t2) ctx) = rebalance z ctx
  where
    z = Balanced d t1 (Balanced a t2 t)
rebalance t (LRC a (Rightie d t1 q) ctx) = rebalance z ctx
  where
    z = case q of
         Leftie t2 p1 p2 -> Balanced t2 (Balanced d t1 p1) (Rightie a p2 t)
         Rightie t2 p1 p2 -> Balanced t2 (Leftie d t1 p1) (Balanced a p2 t)
         Balanced t2 p1 p2 -> Balanced t2 (Balanced d t1 p1) (Balanced a p2 t)
