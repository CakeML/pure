-- Generate a binary search tree, then invert it and find its max depth
main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print $ "Generating tree with " ++ toString n ++ " insertions..."
  let t = loop n 42 Leaf
  let t' = invert t
  print $ "Max depth: " ++ toString (maxHeight t')
  Ret ()

-- Main loop
loop :: Integer
loop n rand t = if n < 0 then t
                else let rand' = lcg rand
                         t' = insertInteger (rand' `mod` mask) t
                     in loop (n - 1) rand' t'


-- Linear congruential generator
-- From https://en.wikipedia.org/wiki/Linear_congruential_generator#Parameters_in_common_use (`glibc` entry)
lcg :: Integer -> Integer
lcg seed = (a * seed + c) `mod` m

mask = 2 ** 16

m = 2 ** 31
a = 1103515245
c = 12345


-- Binary trees
data Tree a = Leaf | Branch (Tree a) a (Tree a)

insertInteger :: Integer -> Tree Integer -> Tree Integer
insertInteger n t =
  case t of Leaf -> Branch Leaf n Leaf
            Branch l a r -> if n == a then Branch l n r
                            else if n < a then Branch (insertInteger n l) a r
                            else Branch l a (insertInteger n r)

invert :: Tree a -> Tree a
invert t = case t of Leaf -> Leaf
                     Branch l a r -> Branch (invert l) a (invert r)

maxHeight :: Tree a -> Integer
maxHeight t = case t of Leaf -> 0
                        Branch l a r -> 1 + max (maxHeight l) (maxHeight r)


-- Helpers

x ** a =
  let expAux acc a = if a < 1 then acc else expAux (acc * x) (a - 1)
  in expAux 1 a

max :: Integer -> Integer -> Integer
max x y = if x < y then y else x


-- I/O helpers

f $ x = f x

s1 ++ s2 = #(__Concat) s1 s2

reverse :: [a] -> [a]
reverse l =
  let revA a l = case l of [] -> a
                           h:t -> revA (h:a) t
  in revA [] l

fromString :: String -> Integer
fromString s =
  let fromStringI i limit acc s =
        if limit == i then acc
        else if limit < i then acc
        else
          fromStringI (i + 1) limit (acc * 10 + (#(__Elem) s i - 48)) s
  in fromStringI 0 (#(__Len) s) 0 s

toString :: Integer -> String
toString i =
  let toString0 i =
        if i == 0 then []
        else (mod i 10 + 48) : toString0 (div i 10)
  in if i < 0 then "-" ++ (implode $ reverse $ toString0 (0-i))
     else if i == 0 then "0"
     else implode $ reverse $ toString0 i

implode l =
  case l of
    [] -> ""
    h:t -> #(__Implode) h ++ implode t

read_arg1 = Act (#(cline_arg) " ")

print s = Act (#(stdout) (s ++ "\n"))

