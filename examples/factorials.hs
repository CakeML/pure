numbers :: [Integer]
numbers =
  let num n = n : num (n + 1)
  in num 0

factA :: Integer -> Integer -> Integer
factA a n =
  if n < 2 then a
  else factA (a * n) (n - 1)

factorials :: [Integer]
factorials = map (factA 1) numbers

app :: (a -> IO b) -> [a] -> IO ()
app f l = case l of
            []  -> return ()
            h:t -> do f h ; app f t

main :: IO ()
main = do
  arg1 <- read_arg1
  -- fromString == 0 on malformed input
  let i = fromString arg1
      facts = take i factorials
  app (\i -> print $ toString i) facts


-- Code below this line omitted from the paper


-- Standard functions

f $ x = f x

map :: (a -> b) -> [a] -> [b]
map f l =
   case l of
     [] -> []
     h:t -> f h : map f t

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

