import Prelude hiding (Monoid(..),Semigroup(..),Foldable(..))

data Semigroup a = SemigroupDict (a -> a -> a)

data Monoid a = MonoidDict (Semigroup a) a

data Foldable t = FoldableDict
    (forall a m. Monoid m -> (a -> m) -> t a -> m)
    (forall a. t a -> [a])

mappend = \x -> case x of
  SemigroupDict y -> y

getSemigroup = \x -> case x of
  MonoidDict y _ -> y

mempty = \x -> case x of
  MonoidDict _ y -> y

foldMap = \x -> case x of
  FoldableDict y _ -> y

toList = \x -> case x of
  FoldableDict _ y -> y

semigroupInt = SemigroupDict (\x y -> x + (y::Integer))

monoidInt = MonoidDict semigroupInt (0::Integer)

foldableList = FoldableDict
  (\m f t -> case t of
    h:tl -> (mappend (getSemigroup m)) (f h) ((foldMap foldableList m) f tl)
    _ -> mempty m)
  (default_toList foldableList)

default_toList = \y -> (foldMap y monoidList) (\x -> x:[])

semigroupList = SemigroupDict append 

monoidList = MonoidDict semigroupList []

monoidTuple = \m1 m2 ->
  MonoidDict
    (semigroupTuple (getSemigroup m1) (getSemigroup m2))
    (mempty m1,mempty m2)

semigroupTuple = \s1 s2 -> SemigroupDict $
  \x y -> case (x,y) of
    ((x1,x2),(y1,y2)) -> (mappend s1 x1 y1, mappend s2 x2 y2)

append l r = case l of
  h:tl -> h:append tl r
  [] -> r

test = let fold = \f0 m1 -> (foldMap f0 m1) (\x -> x) in
  (fold foldableList (monoidTuple monoidInt monoidInt))
    ((fold foldableList monoidList)
      ((toList foldableList) [[(1::Integer,1::Integer)]]))

