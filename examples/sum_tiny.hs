
numbers :: [Integer]
numbers =
  let num n = n : num (n + 1)
  in num 0

sum :: [Integer] -> Integer
sum = foldr (\m n -> m + n) 0

sum_many_times n ns =
  if n < 1 then 0 else
  if sum ns < 1 then sum_many_times (n-1) ns
                else sum_many_times (n-1) ns

main :: IO ()
main = do
  let ns = take 1000 numbers
      k = sum_many_times 1000000 ns
  print $ if k < 1 then "hi" else "hello"
  return ()


-- Standard functions

f $ x = f x

foldr :: (a -> b -> b) -> b -> [a] -> [b]
foldr f x l =
   case l of
     [] -> x
     h:t -> f h (foldr f x t)

take :: Integer -> [a] -> [a]
take n l =
  if n == 0 then []
  else
   case l of
     [] -> []
     h:t -> h : take (n - 1) t


-- I/O helpers

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
          fromStringI (i + 1) limit (acc * 10 + (str_elem s i - 48)) s
  in fromStringI 0 (strlen s) 0 s

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


-- Overloads

s1 ++ s2 = #(__Concat) s1 s2

str_elem :: String -> Integer -> Integer
str_elem s i = #(__Elem) s i

strlen :: String -> Integer
strlen s = #(__Len) s

return v = Ret v
