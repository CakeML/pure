-- basics

f $ x = f x

-- lists

reverse :: [a] -> [a]
reverse l =
  let revA a l =
        case l of [] -> a
                  h:t -> revA (h:a) t
  in
    revA [] l

-- string functions

str_elem :: String -> Int -> Int
str_elem s i = #(__Elem) s i

str_len :: String -> Int
str_len s = #(__Len) s

str_concat :: String -> String -> String
str_concat s1 s2 = #(__Concat) s1 s2

implode :: [Int] -> String
implode l =
  case l of
    [] -> ""
    h:t -> str_concat (#(__Implode) h) (implode t)

int_to_str0 :: Int -> [Int]
int_to_str0 i =
  if i == 0 then []
  else (mod i 10 + 48) : int_to_str0 (div i 10)

int_to_str :: Int -> String
int_to_str i =
  if i < 0 then str_concat "-" (implode $ reverse $ int_to_str0 (0-i))
  else if i == 0 then "0"
  else implode $ reverse $ int_to_str0 i

-- monads

return v = Ret v

-- printing

print s = Act (#(stdout) (str_concat s "\n"))

-- arrays

arr_alloc len init_el = Alloc len init_el

arr_len loc = Length loc

arr_elem loc index = Deref loc index

arr_update loc index x = Update loc index x

-- main program

main = do
  -- allocate and array
  a <- arr_alloc 10 "Hi"
  -- check length
  n <- arr_len a
  print (int_to_str n)
  -- look up element at element 5
  s <- arr_elem a 5
  print s
  -- update element at index 5
  arr_update a 5 "There"
  s <- arr_elem a 5
  print s
  -- attempt to look up element at index 15 in array of length 10
  Handle (do
            arr_elem a 15
            print "OK")
         (\e ->
            print "Oops")
  -- raise an exception
  Raise Subscript
  print "Execution never gets here"
  return ()
