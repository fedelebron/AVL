{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Tree.AVL.Static.Internal where

import Prelude hiding (fmap)
import Control.Applicative (Applicative, pure, (<$>), (<*>))
import Data.Functor (Functor, fmap)
import Data.Traversable (Traversable, traverse)
import Data.Monoid (Monoid, mempty, (<>))
import Data.Foldable (Foldable, foldMap)

-- |A natural number datatype, hoisted to a Kind using DataKinds.
data Nat = Zero | Succ Nat deriving (Eq, Ord, Show)

-- |An @'AVLNode' n a@ is a node whose subtree has height @n@, and values of
-- type @a@.
data AVLNode :: Nat -> * -> * where
  Nil :: AVLNode Zero a
  Leftie :: a -> AVLNode (Succ n) a -> AVLNode n a -> AVLNode (Succ (Succ n)) a
  Rightie :: a -> AVLNode n a -> AVLNode (Succ n) a -> AVLNode (Succ (Succ n)) a
  Balanced :: a -> AVLNode n a -> AVLNode n a -> AVLNode (Succ n) a

deriving instance Show a => Show (AVLNode n a)
-- |An @'AVLTree' a@ is a statically balanced tree, whose non-nil values
-- have type @a@.
data AVLTree a = forall n. T (AVLNode n a) Integer
deriving instance Show a => Show (AVLTree a)

foldNode :: (b -> b -> a -> b) -> b -> AVLNode n a -> b
foldNode _ e Nil = e
foldNode f e (Balanced x l r) = f (foldNode f e l) (foldNode f e r) x
foldNode f e (Rightie x l r) = f (foldNode f e l) (foldNode f e r) x
foldNode f e (Leftie x l r) = f (foldNode f e l) (foldNode f e r) x

fmapNode :: (a -> b) -> AVLNode n a -> AVLNode n b
fmapNode _ Nil = Nil
fmapNode f (Balanced x l r) = Balanced (f x) (fmapNode f l) (fmapNode f r)
fmapNode f (Rightie x l r) = Rightie (f x) (fmapNode f l) (fmapNode f r)
fmapNode f (Leftie x l r) = Leftie (f x) (fmapNode f l) (fmapNode f r)

traverseNode :: Applicative f => (a -> f b) -> AVLNode n a -> f (AVLNode n b)
traverseNode _ Nil = pure Nil
traverseNode f (Balanced x l r) = flip Balanced <$> traverseNode f l
                                                <*> f x
                                                <*> traverseNode f r
traverseNode f (Rightie x l r) = flip Rightie <$> traverseNode f l
                                              <*> f x
                                              <*> traverseNode f r
traverseNode f (Leftie x l r) = flip Leftie <$> traverseNode f l
                                            <*> f x
                                            <*> traverseNode f r
instance Functor AVLTree where
  -- |Functor instance for AVLNodes. Note, this isn't actually a Functor, since
  -- we require f monotonic to maintain the AVL invariant. That is, the mapped
  -- morphism f needs to be (Ord a, Ord b) => a -> b, such that
  --
  --  >  x < x' => f x < f x'.
  fmap f (T r k) = T (fmapNode f r) k

instance Foldable AVLTree where
  -- | The folding is in-order.
  -- >>> let t = foldr insert empty [1..10]
  -- >>> foldr (++) [] (pure <$> t)
  -- >>> [1,2,3,4,5,6,7,8,9,10]
  -- >>> foldr (+) 0 t
  -- >>> 55
  foldMap f (T r _) = foldNode (\x y z -> x <> z <> y) mempty (fmapNode f r)

instance Traversable AVLTree where
  -- |Traversable instance for AVLNodes. This is an in-order traversal of the
  -- subtree rooted at a given node.
  -- >>> let t = foldr insert empty [1, 2, 3]
  -- >>> traverse print t
  -- >>> 1
  -- >>> 2
  -- >>> 3
  traverse f (T r k) = flip T k <$> traverseNode f r

-- |The context for an 'AVLTree'\'s 'Zipper'.
-- The idea is that it represents an entire 'AVLTree', save for a hole in it.
-- A 'Context' @n@ @a@ means an entire 'AVLTree' @a@, with a hole of height n.
-- Its use is that, in a 'Zipper', we have a simple way to move around in the
-- tree, starting at that hole.
--
-- See <http://strictlypositive.org/diff.pdf this> paper by Conor McBride for
-- more information.
data Context :: Nat -> * -> * where
  -- A balanced context. BC isLeft x y means the traversal went left,
  --  on a node Balanced x, where y is the subtree not taken in the
  --  traversal.
  BC :: Bool -> a -> AVLNode n a -> Context (Succ n) a -> Context n a
  -- A leftie context, where we've taken the right branch of the subtree.
  LRC :: a -> AVLNode (Succ n) a -> Context (Succ (Succ n)) a -> Context n a
  -- A leftie context, where we've taken the left branch of the subtree.
  LLC :: a -> AVLNode n a -> Context (Succ (Succ n)) a -> Context (Succ n) a
  -- A rightie context, where we've taken the left branch of the subtree.
  RLC :: a -> AVLNode (Succ n) a -> Context (Succ (Succ n)) a -> Context n a
  -- A rightie context, where we've taken the right branch of the subtree.
  RRC :: a -> AVLNode n a -> Context (Succ (Succ n)) a -> Context (Succ n) a
  -- The root context, where every traversal of an AVLTree starts.
  Root :: Integer -> Context n a
deriving instance Show a => Show (Context n a)

-- |A 'Zipper' is a useful construct for functional datastructure traversals.
-- For us, it can be thought of as a pointer to a subtree in an 'AVLTree'.
--
-- See <http://yquem.inria.fr/~huet/PUBLIC/zip.pdf Functional Pearls: Zippers>
-- for more information.
data Zipper a = forall n. Zipper (AVLNode n a) (Context n a)
deriving instance Show a => Show (Zipper a)

-- |Gets the value at the root of the subtree pointed by that 'Zipper'.
value :: Zipper a -> a
value (Zipper (Balanced x _ _) _) = x
value (Zipper (Leftie x _ _) _) = x
value (Zipper (Rightie x _ _) _) = x
value (Zipper Nil _) = error "Zipper points to Nil."

-- |Constructs a 'Zipper' to the root of the given tree.
unZip :: AVLTree a -> Zipper a
unZip (T r k) = Zipper r (Root k)

-- |Given a function that manipulates the tree size (number of nodes), and a
-- 'Zipper', constructs an 'AVLTree' with the new height, by "zipping up" to
-- the root of the tree pointed to by the 'Zipper'.
zipUp :: (Integer -> Integer) -> Zipper a -> AVLTree a
zipUp f (Zipper t (Root k)) = T t (f k)
zipUp f z = zipUp f (up z)

-- |Navigates up in a 'Zipper'.
up :: Zipper a -> Zipper a
up (Zipper x (LRC v y ctx)) = Zipper (Leftie v y x) ctx
up (Zipper x (LLC v y ctx)) = Zipper (Leftie v x y) ctx
up (Zipper x (RLC v y ctx)) = Zipper (Rightie v x y) ctx
up (Zipper x (RRC v y ctx)) = Zipper (Rightie v y x) ctx
up (Zipper x (BC True v y ctx)) = Zipper (Balanced v x y) ctx
up (Zipper x (BC False v y ctx)) = Zipper (Balanced v y x) ctx
-- TODO: Should I error out on Root?
up z@(Zipper _ (Root _)) = z

-- |Returns whether we can navigate up.
canGoUp :: Zipper a -> Bool
canGoUp (Zipper _ (Root _)) = False
canGoUp _ = True

-- |Navigates left in a 'Zipper'.
left :: Zipper a -> Zipper a
left (Zipper (Balanced x l r) ctx) = Zipper l (BC True x r ctx)
left (Zipper (Leftie x l r) ctx) = Zipper l (LLC x r ctx)
left (Zipper (Rightie x l r) ctx) = Zipper l (RLC x r ctx)
-- TODO: Should I error out on Nil?
left z = z

-- |Returns whether we can navigate left.
canGoLeft :: Zipper a -> Bool
canGoLeft (Zipper (Rightie _ Nil _) _) = False
canGoLeft (Zipper (Balanced _ Nil _) _) = False
canGoLeft (Zipper Nil _) = False
canGoLeft _ = True

-- |Navigates right in a 'Zipper'.
right :: Zipper a -> Zipper a
right (Zipper (Rightie x l r) ctx) = Zipper r (RRC x l ctx)
right (Zipper (Leftie x l r) ctx) = Zipper r (LRC x l ctx)
right (Zipper (Balanced x l r) ctx) = Zipper r (BC False x l ctx)
-- TODO: Should I error out on Nil?
right z = z

-- |Returns whether we can navigate right.
canGoRight :: Zipper a -> Bool
canGoRight (Zipper (Leftie _ _ Nil) _) = False
canGoRight (Zipper (Balanced _ _ Nil) _ ) = False
canGoRight (Zipper Nil _) = False
canGoRight _ = True

-- |Returns whether the pointed to subtree is a left child of its parent.
isLeft :: Zipper a -> Bool
isLeft z | not (canGoUp z) = False
isLeft (Zipper _ (BC False _ _ _)) = False
isLeft (Zipper _ (RRC _ _ _)) = False
isLeft (Zipper _ (LRC _ _ _ )) = False
isLeft _ = True

-- |Returns whether the pointed to subtree is a right child of its parent.
isRight :: Zipper a -> Bool
isRight = (&&) <$> canGoUp <*> (not . isLeft)

-- |Returns whether the pointed to subtree is a leaf.
isLeaf :: Zipper a -> Bool
isLeaf = (&&) <$> (not . canGoLeft) <*> (not . canGoRight)

-- |Descends (never ascends) to a subtree whose root has a given value.
-- If no such subtree exists, points to a 'Nil' where the value would be found,
--  were it to exist.
zipTo :: Ord a => a -> Zipper a -> Zipper a
zipTo _ z@(Zipper Nil _) = z
zipTo x z = let v = value z
            in case compare x v of
                 EQ -> z
                 LT -> zipTo x $ left z
                 GT -> zipTo x $ right z

-- |Insert an 'AVLNode' of height (n + 1) in a 'Context' with a hole of size n.
-- Since this cannot be done in the usual way, rotations are used to return
-- an 'AVLTree' that may nothave the same height as the 'Context'\'s tree did,
-- or have the same structure, but holds the same values, and has this enlarged
--  'AVLNode' in it.
insertUnbalancedAt :: AVLNode (Succ n) a -> Context n a -> AVLTree a
insertUnbalancedAt t (LRC v y ctx) = zipUp (+1) $ Zipper (Balanced v y t) ctx
insertUnbalancedAt t (RLC v y ctx) = zipUp (+1) $ Zipper (Balanced v t y) ctx
insertUnbalancedAt t (Root k) = T t (k + 1)

{- LLC -}
insertUnbalancedAt (Leftie b g p) (LLC a d ctx) = zipUp (+1) z
  where
    z = Zipper (Balanced b g (Balanced a p d)) ctx
insertUnbalancedAt (Rightie b g q) (LLC a d ctx) = zipUp (+1) z
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
insertUnbalancedAt (Rightie b g p) (RRC a d ctx) = zipUp (+1) z
  where
    z = Zipper (Balanced b (Balanced a d g) p) ctx
insertUnbalancedAt (Leftie b q p) (RRC a d ctx) = zipUp (+1) z
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

-- |Given a 'Zipper' to a node in the tree, returns a 'Zipper' to the successor
-- of this node. If no such successor exists, returns 'Nothing'.
zipToSuccessor :: Zipper a -> Maybe (Zipper a)
zipToSuccessor z | canGoRight z = Just . zipToSmallest $ right z
                 | otherwise = let parent = zipToFirstLeftChild z
                               in  up <$> parent
-- |Given a 'Zipper' to a node in the tree, returns a Zipper to the predecessor
-- of this node. If no such predecessor exists, returns 'Nothing'.
zipToPredecessor :: Zipper a -> Maybe (Zipper a)
zipToPredecessor z | canGoLeft z = Just . zipToGreatest $ left z
                   | otherwise = let parent = zipToFirstRightChild z
                                 in up <$> parent
-- |Given a 'Zipper' to a node @X@ in the tree, returns a 'Zipper' to the
-- smallest node in the subtree rooted at @X@.
zipToSmallest :: Zipper a -> Zipper a
zipToSmallest z | canGoLeft z = zipToSmallest (left z)
                | otherwise = z
-- |Given a 'Zipper' to a node @X@ in the tree, returns a 'Zipper' to the
-- greatest node in the subtree rooted at @X@.
zipToGreatest :: Zipper a -> Zipper a
zipToGreatest z | canGoRight z = zipToGreatest (right z)
                | otherwise = z

-- |Given a 'Zipper' @Z@, which points to a subtree @S@, returns a 'Zipper' to
-- the first ancestor of @S@ which is a left child of its parent. If such an
-- ancestor does not exist, returns 'Nothing'.
zipToFirstLeftChild :: Zipper a -> Maybe (Zipper a)
zipToFirstLeftChild z | isLeft z = Just z
zipToFirstLeftChild z | canGoUp z = zipToFirstLeftChild (up z)
                      | otherwise = Nothing

-- |Given a 'Zipper' @Z@, which points to a subtree @S@, returns a 'Zipper' to
-- the first ancestor of @S@ which is a right child of its parent. If such an
-- ancestor does not exist, returns 'Nothing'.
zipToFirstRightChild :: Zipper a -> Maybe (Zipper a)
zipToFirstRightChild z | isRight z = Just z
zipToFirstRightChild z | canGoUp z = zipToFirstRightChild (up z)
                       | otherwise = Nothing

-- |Replaces a given value by another, in the 'AVLTree' represented by a
-- 'Context'.
fixContext :: forall a n. Eq a => a -> a -> Context n a -> Context n a
fixContext k k' = go
  where
    z x = if x == k then k' else x
    go :: Context n' a -> Context n' a
    go r@(Root _) = r
    go (BC goLeft x y ctx) = BC goLeft (z x) y (go ctx)
    go (LLC x y ctx) = LLC (z x) y (go ctx)
    go (LRC x y ctx) = LRC (z x) y (go ctx)
    go (RRC x y ctx) = RRC (z x) y (go ctx)
    go (RLC x y ctx) = RLC (z x) y (go ctx)

-- |Given a 'Zipper' @Z@, deletes the value at the root of the subtree pointed
-- to by @Z@. It returns a modified 'AVLTree' with this change applied.
-- The removal is straight-up BST removal, folowed by an AVL rebalancing.
deleteBST :: Eq a => Zipper a -> AVLTree a
deleteBST (Zipper (Balanced _ Nil Nil) ctx) = rebalance Nil ctx
deleteBST (Zipper (Rightie _ Nil r) ctx) = rebalance r ctx
deleteBST (Zipper (Leftie _ l Nil) ctx) = rebalance l ctx
deleteBST z@(Zipper (Rightie k _ _) _) =
  let Just s = zipToSuccessor z
  in case s of
       Zipper (Balanced k' Nil Nil) ctx' -> rebalance Nil (fixContext k k' ctx')
       Zipper (Rightie k' Nil r) ctx' -> rebalance r (fixContext k k' ctx')
       _ -> error "The impossible has happened, bad successor found."
deleteBST z@(Zipper (Leftie k _ _) _) =
  let Just s = zipToPredecessor z
  in case s of
       Zipper (Balanced k' Nil Nil) ctx' -> rebalance Nil (fixContext k k' ctx')
       Zipper (Leftie k' l Nil) ctx' -> rebalance l (fixContext k k' ctx')
       _ -> error "The impossible has happened, bad predecessor found."
deleteBST z@(Zipper (Balanced k _ _) _) =
  let Just s = zipToSuccessor z
  in case s of
       Zipper (Balanced k' Nil Nil) ctx' -> rebalance Nil (fixContext k k' ctx')
       Zipper (Rightie k' Nil r) ctx' -> rebalance r (fixContext k k' ctx')
       _ -> error "The impossible has happened, bad successor found."
deleteBST (Zipper Nil _) = error "You cannot delete Nil."

-- | Given an 'AVLNode' @n@ @a@, and a 'Context' with a hole of size @(n + 1)@,
-- returns an 'AVLTree' @a@ with the 'AVLNode' being placed in that 'Context'.
-- Since this cannot be done normally, it uses rotations to return an 'AVLTree'
-- that has the same elements as the 'Context' and the 'AVLNode' together,
-- but may have a different structure than the tree the 'Context' represented.
rebalance :: AVLNode n a -> Context (Succ n) a -> AVLTree a
rebalance t (Root k) = (T t (k - 1))
rebalance t (BC True a d ctx) = zipUp (subtract 1) $ Zipper (Rightie a t d) ctx
rebalance t (BC False a d ctx) = zipUp (subtract 1) $ Zipper (Leftie a d t) ctx
rebalance t (LLC a d ctx) = rebalance (Balanced a t d) ctx
rebalance t (RRC a d ctx) = rebalance (Balanced a d t) ctx
rebalance t (RLC a (Balanced d t1 t2) ctx) = zipUp (subtract 1) z
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
rebalance t (LRC a (Balanced d t1 t2) ctx) = zipUp (subtract 1) z
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
