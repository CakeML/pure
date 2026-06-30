-- nofib spectral/primetest: probabilistic primality testing of large integers.
-- The original runs a Rabin-Miller test on Mersenne numbers read from stdin.
-- Here the single argument is an exponent p; we test whether the Mersenne
-- number M_p = 2^p - 1 is prime using deterministic-witness Miller-Rabin
-- (square-and-multiply modular exponentiation on big integers).

main :: IO ()
main = do
  arg1 <- read_arg1
  let p = fromString arg1
      m = powInt 2 p - 1
  print ("M" ++ toString p ++ " = 2^" ++ toString p ++ " - 1 is "
         ++ (if isPrime m then "prime" else "composite"))
  Ret ()

-- modular exponentiation: b^e mod m
powMod :: Integer -> Integer -> Integer -> Integer
powMod b e m =
  let go acc base e =
        if e == 0 then acc
        else let acc' = if e `mod` 2 == 1 then (acc * base) `mod` m else acc
                 base' = (base * base) `mod` m
             in go acc' base' (e `div` 2)
  in go (1 `mod` m) (b `mod` m) e

powInt :: Integer -> Integer -> Integer
powInt b e = if e == 0 then 1 else b * powInt b (e - 1)

-- write m = 2^r * d with d odd; returns (r, d)
factor2 :: Integer -> Integer -> (Integer, Integer)
factor2 m r = if m `mod` 2 == 0 then factor2 (m `div` 2) (r + 1) else (r, m)

mrWitness :: Integer -> Integer -> Integer -> Integer -> Bool
mrWitness n d r a =
  let x = powMod a d n
  in if orB (x == 1) (x == n - 1) then True
     else mrLoop n (r - 1) ((x * x) `mod` n)

mrLoop :: Integer -> Integer -> Integer -> Bool
mrLoop n cnt x =
  if cnt < 1 then False
  else if x == n - 1 then True
       else mrLoop n (cnt - 1) ((x * x) `mod` n)

witnesses :: [Integer]
witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

allWitness :: Integer -> Integer -> Integer -> [Integer] -> Bool
allWitness n d r ws =
  case ws of
    [] -> True
    a:rest -> if not (a < n) then True
              else if mrWitness n d r a then allWitness n d r rest else False

isPrime :: Integer -> Bool
isPrime n =
  if n < 2 then False
  else if n == 2 then True
  else if n `mod` 2 == 0 then False
  else case factor2 (n - 1) 0 of
         (r, d) -> allWitness n d r witnesses


-- Helpers

orB :: Bool -> Bool -> Bool
orB a b = case a of True -> True
                    False -> b

not :: Bool -> Bool
not b = case b of True -> False
                  False -> True


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
        else fromStringI (i + 1) limit (acc * 10 + (#(__Elem) s i - 48)) s
  in fromStringI 0 (#(__Len) s) 0 s

toString :: Integer -> String
toString i =
  let toString0 i =
        if i == 0 then []
        else (i `mod` 10 + 48) : toString0 (i `div` 10)
  in if i < 0 then "-" ++ (implode $ reverse $ toString0 (0 - i))
     else if i == 0 then "0"
     else implode $ reverse $ toString0 i

implode l =
  case l of
    [] -> ""
    h:t -> #(__Implode) h ++ implode t

read_arg1 = Act (#(cline_arg) " ")

print s = Act (#(stdout) (s ++ "\n"))
