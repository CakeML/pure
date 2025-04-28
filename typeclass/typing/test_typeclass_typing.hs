import Prelude hiding (Monoid(..),Semigroup(..),Foldable(..))

class Semigroup a where
  mappend :: a -> a -> a

class Semigroup a => Monoid a where
  mempty :: a

class Foldable t where
  foldMap :: Monoid m => (a -> m) -> t a -> m
  toList :: t a -> [a]
  toList = foldMap (\x -> [x])

instance Semigroup Integer where
  mappend x y = x + y

instance Monoid Integer where
  mempty = 0

instance Semigroup [a] where
  mappend = append

instance Monoid [a] where
  mempty = []

instance Foldable [] where
  foldMap f t = case t of
    h:tl -> mappend (f h) (foldMap f tl)
    _ -> mempty

instance (Monoid a,Monoid b) => Monoid (a,b) where
  mempty = (mempty,mempty)

instance (Semigroup a,Semigroup b) => Semigroup (a,b) where
  mappend x y = case (x,y) of
    ((x1,x2),(y1,y2)) -> (mappend x1 y1,mappend x2 y2)

append :: [a] -> [a] -> [a]
append l r = case l of
  h:tl -> h:append tl r
  [] -> r

test :: (Integer,Integer)
test =
  let
    fold::(Foldable t,Monoid m) => t m -> m
    fold = foldMap id
  in fold (fold (toList [[(1::Integer,1::Integer)]]))

