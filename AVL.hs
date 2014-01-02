{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}

data Nat = Zero | Succ Nat deriving (Eq, Ord, Show)
type One = Succ Zero
type Two = Succ One

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

unZip :: AVLNode n a -> Zipper n a
unZip = flip Zipper Root

zipUp :: Zipper m a -> AVLNode m a
zipUp (Zipper x Root) = x
zipUp (Zipper x (BC goLeft v y ctx)) = zipUp $ Zipper tree ctx
  where
    tree | goLeft = Balanced v y x
         | otherwise = Balanced v x y
zipUp (Zipper x (LRC v y ctx)) = zipUp $ Zipper (Leftie v y x) ctx
zipUp (Zipper x (LLC v y ctx)) = zipUp $ Zipper (Leftie v x y) ctx
zipUp (Zipper x (RLC v y ctx)) = zipUp $ Zipper (Rightie v x y) ctx
zipUp (Zipper x (RRC v y ctx)) = zipUp $ Zipper (Rightie v y x) ctx


zipTo :: Ord a => a -> Zipper n a -> Zipper n a
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


empty :: AVLTree a
empty = T Nil

insert :: Ord a => a -> AVLTree a -> AVLTree a
insert x t@(T root) = case zipTo x (unZip root) of
  Zipper Nil ctx -> insertUnbalancedAt (Balanced x Nil Nil) ctx
  _ -> t

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
insertUnbalancedAt (Rightie b p g) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced b g (Balanced a p d)) ctx
insertUnbalancedAt (Leftie b (Leftie p t1 t2) g) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced p (Leftie b g t2) (Balanced a t1 d)) ctx
insertUnbalancedAt (Leftie b (Rightie p t1 t2) g) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced p (Balanced b g t2) (Rightie a t1 d)) ctx
insertUnbalancedAt (Leftie b (Balanced p t1 t2) g) (RRC a d ctx) = T $ zipUp z
  where
    z = Zipper (Balanced p (Balanced b g t2) (Balanced a t1 d)) ctx
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


main :: IO ()
main = return ()
