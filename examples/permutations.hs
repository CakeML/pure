-- Finding permutations of a list
-- adapted from GHC's Data.List

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print $ "Finding no. permutations for [1.." ++ toString n ++ "]"
  let perms = permutations (numbersUpTo n)
  print $ "Computed " ++ (toString (length perms)) ++ " permutations"
  printIntegers (numbersUpTo n)
  Ret permutations
  Ret ()


permutations :: [a] -> [[a]]
permutations xs0 =
  let interleave t ts xs r = snd (interleave' t ts id xs r)

      interleave' t ts f l r =
        case l of [] -> (ts, r)
                  y:ys -> let p = interleave' t ts (\x -> f (y:x)) ys r
                          in case p of (us,zs) -> (y:us, f (t:y:us) : zs)

      perms l is =
        case l of [] -> []
                  t:ts -> foldr (interleave t ts)
                            (perms ts (t:is)) (permutations is)

  in xs0 : perms xs0 []

numbersUpTo :: Integer -> [Integer]
numbersUpTo n =
  if n < 0 then [] else
  let numbersAux start =
        if start < n + 1 then start : numbersAux (start + 1)
        else []
  in numbersAux 1

printIntegers :: [Integer] -> IO String
printIntegers l = case l of [] -> printOnly "\n"
                            h:t -> do printOnly (toString h ++ " ") ; printIntegers t


-- Helper functions

id :: a -> a
id x = x

snd :: (a,b) -> b
snd p = case p of (a,b) -> b


length :: [a] -> Integer
length l = case l of [] -> 0
                     h:t -> 1 + length t

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f acc l = case l of [] -> acc
                          h:t -> f h (foldr f acc t)

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
        else (i `mod` 10 + 48) : toString0 (i `div` 10)
  in if i < 0 then "-" ++ (implode $ reverse $ toString0 (0-i))
     else if i == 0 then "0"
     else implode $ reverse $ toString0 i

implode l =
  case l of
    [] -> ""
    h:t -> #(__Implode) h ++ implode t

read_arg1 = Act (#(cline_arg) " ")

print s = Act (#(stdout) (s ++ "\n"))

printOnly s = Act (#(stdout) s)

