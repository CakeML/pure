main :: IO ()
main = Ret ()

-- Binary trees

data Tree a = Leaf | Branch (Tree a) a (Tree a)

fold :: (a -> b -> b -> b) -> b -> Tree a -> b
fold f acc t = case t of Leaf -> acc
                         Branch l a r -> f a (fold f acc l) (fold f acc r)

flatten :: ([a] -> a -> [a] -> [a]) -> Tree a -> [a]
flatten f t =
  case t of Leaf -> []
            Branch l a r -> f (flatten f l) a (flatten f r)

inorder :: Tree a -> [a]
inorder t = flatten (\l a r -> l ++ (a : r)) t

preorder :: Tree a -> [a]
preorder t = flatten (\l a r -> a : l ++ r) t

postorder :: Tree a -> [a]
postorder t = flatten (\l a r -> l ++ r ++ [a]) t

invert :: Tree a -> Tree a
invert t = case t of Leaf -> Leaf
                     Branch l a r -> Branch (invert l) a (invert r)


-- Rose trees

data Rose a = Tree a [Rose a]

foldRose :: (a -> [b] -> b) -> Rose a -> b
foldRose f t =
  case t of Tree a rs -> f a (map (foldRose f) rs)

flattenRose t =
  case t of Tree a rs -> a : concat (map flattenRose rs)

invertRose t =
  case t of Tree a rs -> Tree a (reverse rs)


-- Helpers

l1 ++ l2 = case l1 of [] -> l2
                      h:t -> h : (t ++ l2)

reverse :: [a] -> [a]
reverse l =
  let revA a l = case l of [] -> a
                           h:t -> revA (h:a) t
  in revA [] l

map :: (a -> b) -> [a] -> [b]
map f l = case l of [] -> []
                    h:t -> f h : map f t

concat :: [[a]] -> [a]
concat ll = case ll of [] -> []
                       h:t -> h ++ concat t

