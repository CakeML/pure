-- basics

f $ x = f x

-- list

reverse :: [a] -> [a]
reverse l =
  let revA a l =
        case l of [] -> a
                  h:t -> revA (h:a) t
  in
    revA [] l

l1 ++ l2 =
  case l1 of
   [] -> l2
   h:t -> h : (t ++ l2)

take :: Integer -> [a] -> [a]
take n l =
  if n == 0 then []
  else
   case l of
     [] -> []
     h:t -> h : take (n - 1) t

drop :: Integer -> [a] -> [a]
drop n l =
  if n == 0 then l
  else
   case l of
     [] -> []
     h:t -> drop (n - 1) t

map :: (a -> b) -> [a] -> [b]
map f l =
   case l of
     [] -> []
     h:t -> f h : map f t

filter :: (a -> Bool) -> [a] -> [a]
filter p l =
  case l of
   [] -> []
   h:t -> if p h then h : filter p t else filter p t

tail :: [a] -> [a]
tail l =
  case l of
   [] -> []
   h:t -> t

length :: [a] -> Integer
length l =
  case l of
   [] -> 0
   h:t -> 1 + length t

flat :: [[a]] -> [a]
flat ll =
  case ll of
   [] -> []
   h:t -> h ++ flat t

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f e l =
  case l of
   [] -> e
   h:t -> f h (foldr f e t)

null l =
  case l of
   [] -> True
   h:t -> False

numbers :: [Integer]
numbers =
  let num n = n : num (n + 1)
  in num 0

-- string functions

str_elem :: String -> Integer -> Integer
str_elem s i = #(__Elem) s i

str_len :: String -> Integer
str_len s = #(__Len) s

str_concat :: String -> String -> String
str_concat s1 s2 = #(__Concat) s1 s2

implode :: [Integer] -> String
implode l =
  case l of
    [] -> ""
    h:t -> str_concat (#(__Implode) h) (implode t)

explode :: String -> [Integer]
explode s =
  let
    l = str_len s
    from i = if i < l then str_elem s i : from (i+1) else []
  in from 0

str_to_intI :: Integer -> Integer -> Integer -> String -> Integer
str_to_intI i limit acc s =
  if limit == i then acc
  else if limit < i then acc
  else
    str_to_intI (i + 1) limit (acc * 10 + (str_elem s i - 48)) s

str_to_int :: String -> Integer
str_to_int s = str_to_intI 0 (str_len s) 0 s

int_to_str0 :: Integer -> [Integer]
int_to_str0 i =
  if i == 0 then []
  else (mod i 10 + 48) : int_to_str0 (div i 10)

int_to_str :: Integer -> String
int_to_str i =
  if i < 0 then str_concat "-" (implode $ reverse $ int_to_str0 (0-i))
  else if i == 0 then "0"
  else implode $ reverse $ int_to_str0 i

bool_to_str :: Bool -> String
bool_to_str b =
  case b of
   True -> "True"
   False -> "False"

-- monads

return v = Ret v

-- basic I/O

print s = Act (#(stdout) (str_concat s "\n"))

print_only s = Act (#(stdout) s)

print_int i = print_only (int_to_str i)

print_list f l =
  let
    aux xs = case xs of
              [] -> print_only "]"
              h:t -> do
                       f h
                       print_only (if null t then "" else ", ")
                       aux t
  in do
       print_only "["
       aux l

-- main program

list = take 4 numbers

main = do
  print (int_to_str $ length list)
  print (int_to_str $ length $ tail list)
  print (int_to_str $ foldr (\x y -> x + y) 0 list)
  print_list print_int list ; print ""
  print_list print_int (filter (\x -> mod x 2 == 0) $ take 20 numbers) ; print ""
  print_list print_int (map (\x -> x + 50) list) ; print ""
  print_list (print_list print_int) [[1,2],[3,4]] ; print ""
  return ()
