-- basics

f $ x = f x

-- lists

l1 ++ l2 =
  case l1 of
   [] -> l2
   h:t -> h : (t ++ l2)

map :: (a -> b) -> [a] -> [b]
map f l =
   case l of
     [] -> []
     h:t -> f h : map f t

flat :: [[a]] -> [a]
flat ll =
  case ll of
   [] -> []
   h:t -> h ++ flat t

length :: [a] -> Integer
length l =
  case l of
   [] -> 0
   h:t -> 1 + length t

-- string functions

str_concat :: String -> String -> String
str_concat s1 s2 = #(__Concat) s1 s2

-- monads

return v = Ret v

-- basic I/O

print s = Act (#(stdout) (str_concat s "\n"))

-- user-defined datatypes

data Rose a = Tree a [Rose a]

flatten t =
  case t of
   Tree a rs -> a : flat (map flatten rs)

data Foo a b = C Bool a Integer | D b [Bar a]

data Bar d = E d | F (Foo d Integer)

f x = case x of
        C b a i -> i + 1
        _ -> 3

-- main program

main = do
  print (if length (flatten (Tree 1 [Tree 2 [], Tree 3 []])) == 3
         then "Yes" else "No")
  print (if f (D 1 [E ()]) == 3
         then "Yes!" else "No!")
  return ()
