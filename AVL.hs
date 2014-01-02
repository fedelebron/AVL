{-# LANGUAGE GADTs, DataKinds, ExplicitForAll, StandaloneDeriving, KindSignatures #-}

data Nat = Zero | Succ Nat deriving (Eq, Ord, Show)


data AVLNode :: Nat -> * -> * where
  Leaf :: a -> AVLNode Zero a
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


singleton :: a -> AVLTree a
singleton = T . Leaf

insert :: Ord a => a -> AVLTree a -> AVLTree a
insert x t@(T root) = case zipTo x (unZip root) of
  Zipper (Leaf y) ctx = insertAt (if Leaf x) ctx
  _ -> t

insertAt :: AVLNode n a -> Context m n a -> AVLTree a
insertAt = undefined

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

left :: AVLNode (Succ n) a -> Node a
left (Leftie _ l r) = Node l
left (Rightie _ l r) = Node l
left (Balanced _ l r) = Node l

right :: AVLNode (Succ n) a -> Node a
right (Leftie _ l r) = Node r
right (Rightie _ l r) = Node r
right (Balanced _ l r) = Node r

main :: IO ()
main = return ()
