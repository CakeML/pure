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

return :: a -> IO a
return x = Ret x

head :: [a] -> IO a
head l = case l of
           [] -> Raise Subscript
           h:t -> return h

str_elem :: String -> Int -> Int
str_elem s i = #(__Elem) s i

strlen :: String -> Int
strlen s = #(__Len) s

print :: String -> IO ()
print s = do Act (#(stdout) (#(__Concat) s "\n"))
             return ()


app :: (a -> IO b) -> [a] -> IO ()
app f l = case l of [] -> return ()
                    h:t -> do f h
                              app f t

fromStringI :: Int -> Int -> Int -> String -> Int
fromStringI i limit acc s =
  if i > limit then acc
  else
    fromStringI (i + 1) limit (acc * 10 + (str_elem s i - 48)) s

fromString :: String -> Int
fromString s = fromStringI 0 (strlen s) 0 s

toString0 :: Int -> String
toString0 i =
  if i == 0 then []
  else chr (mod i 10 + 48) : toString0 (div i 10)

toString :: Int -> String
toString i =
  if i < 0 then "-" ++ reverse (toString0 i)
  else if i == 0 then "0"
  else reverse $ toString0 i

get_cline_arg :: Int -> IO String
get_cline_arg i = Act (#(getArg) (toString i))

main :: IO ()
main =
  do
    arg0 <- get_cline_arg 0
    let i = fromString arg0
    let facts = take i factorials
    app (\i -> print $ toString i) facts
