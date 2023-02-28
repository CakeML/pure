read_arg1 = Act (#(cline_arg) " ")

str_elem :: String -> Int -> Int
str_elem s i = #(__Elem) s i

strlen :: String -> Int
strlen s = #(__Len) s

numbers :: [Int]
numbers =
  let num n = n : num (n + 1)
  in num 0

take :: Int -> [a] -> [a]
take n l =
  if n == 0 then []
  else
   case l of
     [] -> []
     h:t -> h : take (n - 1) t

factA :: Int -> Int -> Int
factA a n =
  if n < 2 then a
  else factA (a * n) (n - 1)

map :: (a -> b) -> [a] -> [b]
map f l =
   case l of
     [] -> []
     h:t -> f h : map f t

factorials :: [Int]
factorials = map (factA 1) numbers

fromStringI :: Int -> Int -> Int -> String -> Int
fromStringI i limit acc s =
  if limit == i then acc
  else if limit < i then acc
  else
    fromStringI (i + 1) limit (acc * 10 + (str_elem s i - 48)) s

fromString :: String -> Int
fromString s = fromStringI 0 (strlen s) 0 s

f $ x = f x

s1 ++ s2 = #(__Concat) s1 s2

implode l =
  case l of
    [] -> ""
    h:t -> #(__Implode) h ++ implode t

toString0 :: Int -> [Int]
toString0 i =
  if i == 0 then []
  else (mod i 10 + 48) : toString0 (div i 10)

reverse :: [a] -> [a]
reverse l =
  let revA a l =
        case l of [] -> a
                  h:t -> revA (h:a) t
  in
    revA [] l


toString :: Int -> String
toString i =
  if i < 0 then "-" ++ (implode $ reverse $ toString0 (0-i))
  else if i == 0 then "0"
  else implode $ reverse $ toString0 i

print s = Act (#(stdout) (s ++ "\n"))

return v = Ret v

app :: (a -> IO b) -> [a] -> IO ()
app f l =
  case l of
    [] -> return ()
    h:t -> do f h ; app f t

main = do
  arg1 <- read_arg1
  -- fromString == 0 on malformed input
  let i = fromString arg1
      facts = take i factorials
  app (\i -> print $ toString i) facts
