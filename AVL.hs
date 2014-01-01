{-# LANGUAGE GADTs, DataKinds, ExplicitForAll, StandaloneDeriving #-}

data N = Z | S N deriving (Eq, Ord, Show)

data AVLNode n a where
  Leaf :: a -> AVLNode Z a
  Leftie :: a -> AVLNode (S n) a -> AVLNode n a -> AVLNode (S (S n)) a
  Rightie :: a -> AVLNode n a -> AVLNode (S n) a -> AVLNode (S (S n)) a
  Balanced :: a -> AVLNode n a -> AVLNode n a -> AVLNode (S n) a

deriving instance Show a => Show (AVLNode n a)

data AVLTree a = forall n. T (AVLNode n a)
deriving instance Show a => Show (AVLTree a)

search :: (Ord a, Eq a) => forall n. AVLNode n a -> a -> Bool
search (Leaf y) x = x == y
search (Leftie z left right) x = case compare x z of
                                     EQ -> True
                                     LT -> search left x
                                     GT -> search right x

search (Rightie z left right) x = case compare x z of
                                     EQ -> True
                                     LT -> search left x
                                     GT -> search right x

search (Balanced z left right) x = case compare x z of
                                     EQ -> True
                                     LT -> search left x
                                     GT -> search right x

data Node a = forall n. Node (AVLNode n a)

left :: AVLNode (S n) a -> Node a
left (Leftie _ l r) = Node l
left (Rightie _ l r) = Node l
left (Balanced _ l r) = Node l

right :: AVLNode (S n) a -> Node a
right (Leftie _ l r) = Node r
right (Rightie _ l r) = Node r
right (Balanced _ l r) = Node r

main :: IO ()
main = return ()
