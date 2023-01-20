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

take :: Int -> [a] -> [a]
take n l =
  if n == 0 then []
  else
   case l of
     [] -> []
     h:t -> h : take (n - 1) t

drop :: Int -> [a] -> [a]
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

numbers :: [Int]
numbers =
  let num n = n : num (n + 1)
  in num 0

-- string functions

str_elem :: String -> Int -> Int
str_elem s i = #(__Elem) s i

str_len :: String -> Int
str_len s = #(__Len) s

str_concat :: String -> String -> String
str_concat s1 s2 = #(__Concat) s1 s2

str_substr :: String -> Int -> Int
str_substr s i j = #(__Substring) s i j

str_eq :: String -> String -> Bool
str_eq s1 s2 = #(__StrEq) s1 s2

str_lt :: String -> String -> Bool
str_lt s1 s2 = #(__StrLt) s1 s2

str_gt :: String -> String -> Bool
str_gt s1 s2 = #(__StrGt) s1 s2

str_leq :: String -> String -> Bool
str_leq s1 s2 = #(__StrLeq) s1 s2

str_geq :: String -> String -> Bool
str_geq s1 s2 = #(__StrGeq) s1 s2

implode :: [Int] -> String
implode l =
  case l of
    [] -> ""
    h:t -> str_concat (#(__Implode) h) (implode t)

explode :: String -> [Int]
explode s =
  let
    l = str_len s
    from i = if i < l then str_elem s i : from (i+1) else []
  in from 0

str_to_intI :: Int -> Int -> Int -> String -> Int
str_to_intI i limit acc s =
  if limit == i then acc
  else if limit < i then acc
  else
    str_to_intI (i + 1) limit (acc * 10 + (str_elem s i - 48)) s

str_to_int :: String -> Int
str_to_int s = str_to_intI 0 (str_len s) 0 s

int_to_str0 :: Int -> [Int]
int_to_str0 i =
  if i == 0 then []
  else (mod i 10 + 48) : int_to_str0 (div i 10)

int_to_str :: Int -> String
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

app :: (a -> IO b) -> [a] -> IO ()
app f l =
  case l of
    [] -> return ()
    h:t -> do f h ; app f t

-- basic I/O

read_arg n =
  let make_str n = if n < 1 then ""
                   else str_concat " " (make_str (n - 1))
  in Act (#(cline_arg) (make_str n))

print s = Act (#(stdout) (str_concat s "\n"))

-- arrays

arr_alloc len init_el = Alloc len init_el

arr_len loc = Length loc

arr_elem loc index = Deref loc index

arr_update loc index x = Update loc index x

-- factorial

factA :: Int -> Int -> Int
factA a n =
  if n < 2 then a
  else factA (a * n) (n - 1)

factorials :: [Int]
factorials = map (factA 1) numbers

-- main program

main = do
  arg1 <- read_arg 1
  -- simple echo
  print arg1
  -- string and list functions
  print (implode $ explode arg1)
  print (implode (explode arg1 ++ explode arg1))
  print (bool_to_str (1 < 2))
  print (str_substr "Hello" 1 2)
  print (bool_to_str (str_eq "Hello" "There"))
  print (bool_to_str (str_lt "Hello" "There"))
  -- integers
  print (int_to_str (1 + 2))
  print (int_to_str (1 - 2))
  print (int_to_str (1 * 2))
  print (int_to_str (div 1 2))
  print (int_to_str (mod 1 2))
  -- arrays
  a <- arr_alloc 10 "Hi"
  n <- arr_len a
  print (int_to_str n)
  s <- arr_elem a 5
  print s
  arr_update a 5 "There"
  s <- arr_elem a 5
  print s
  return ()
