-- Primality testing using two methods

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print $ "Finding prime no. " ++ toString n
  let a = primeA n
      b = primeB n
  print $ "Sieve of Eratosthenes: " ++ toString a
  print $ "Divisor testing: " ++ toString b
  Ret ()


-- Method 1: sieve of Eratosthenes

primesA :: [Integer]
primesA =
  let sieve l =
        case l of
          [] -> [] -- should not happen
          h:t -> h : filter (\n -> not $ mod n h == 0) (sieve t)
  in sieve $ numbers 2

primeA :: Integer -> Integer
primeA n = idx n primesA


-- Method 2: divisor testing

isPrime :: Integer -> Bool
isPrime n =
  let checkPrime div n = if n < div * div then True
                         else if mod n div == 0 then False
                         else checkPrime (div + 1) n
  in if n < 2 then False else checkPrime 2 n

primesB :: [Integer]
primesB = filter isPrime $ numbers 2

primeB :: Integer -> Integer
primeB n = idx n primesB


-- Helper functions

f $ x = f x

not :: Bool -> Bool
not b = case b of True -> False
                  False -> True

filter :: (a -> Bool) -> [a] -> [a]
filter f l =
  case l of
    [] -> []
    h:t -> if f h then h : filter f t
           else filter f t

idx :: Integer -> [Integer] -> Integer
idx n l =
  case l of
    [] -> ~1 -- should not happen
    h:t -> if n == 0 then h else idx (n - 1) t

numbers :: Integer -> [Integer]
numbers n = n : numbers (n + 1)


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


-- Overloads

s1 ++ s2 = #(__Concat) s1 s2

str_elem :: String -> Integer -> Integer
str_elem s i = #(__Elem) s i

strlen :: String -> Integer
strlen s = #(__Len) s





