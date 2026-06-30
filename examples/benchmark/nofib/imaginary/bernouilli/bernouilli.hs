-- nofib imaginary/bernouilli: compute the n-th Bernoulli number (haskell-cafe,
-- March 2003). The single argument is n. The original uses Data.Ratio; PureLang
-- has only Integer, so rationals are explicit reduced (num, den) pairs (Rat).
-- Output matches Haskell's `Ratio` show, e.g. "5 % 66".

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print ("bernoulli " ++ toString n ++ " = " ++ showRat (bernoulli n))
  Ret ()

data Rat = Rat Integer Integer    -- numerator, denominator (>0, reduced)

bernoulli :: Integer -> Rat
bernoulli n =
  if n == 0 then Rat 1 1
  else if n == 1 then mkRat (0 - 1) 2
  else if odd n then Rat 0 1
  else
    let pwrs = idxLL (n - 1) neg_powers
        terms = map
                  (\kc -> case kc of
                     (k, combs) ->
                       let s = sumI (zipWithMul pwrs (tail (tail combs)))
                       in mkRat (s - k) (k + 1))
                  (zip (enumFromTo 2 n) pascal)
    in addRat (mkRat (0 - 1) 2) (sumRat terms)

-- Infinite table: powers !! m = [ r^(m+1) | r <- [2..] ]
powers :: [[Integer]]
powers = enumFrom 2 : map (\row -> zipWithMul (enumFrom 2) row) powers

-- neg_powers !! m = [ (-1)^r * r^(m+1) | r <- [2..] ]
neg_powers :: [[Integer]]
neg_powers = map (\row -> zipWithSign boolStream row) powers

boolStream :: [Bool]
boolStream = True : False : boolStream

-- pascal !! m is the (m+2)-th row of Pascal's triangle, starting [1,2,1]
pascal :: [[Integer]]
pascal = (1 : 2 : 1 : []) : map (\line -> zipWithAdd (append line [0]) (0 : line)) pascal


-- Rational arithmetic

mkRat :: Integer -> Integer -> Rat
mkRat n d =
  if d == 0 then Rat 0 1
  else let sgn = if d < 0 then 0 - 1 else 1
           g0 = gcdI (absI n) (absI d)
           g = if g0 == 0 then 1 else g0
       in Rat (sgn * n `div` g) (sgn * d `div` g)

addRat :: Rat -> Rat -> Rat
addRat x y = case x of
               Rat a b -> case y of
                            Rat c d -> mkRat (a * d + c * b) (b * d)

sumRat :: [Rat] -> Rat
sumRat l = case l of [] -> Rat 0 1
                     h:t -> addRat h (sumRat t)

showRat :: Rat -> String
showRat r = case r of Rat a b -> toString a ++ " % " ++ toString b

gcdI :: Integer -> Integer -> Integer
gcdI a b = if b == 0 then a else gcdI b (a `mod` b)

absI :: Integer -> Integer
absI i = if i < 0 then 0 - i else i

odd :: Integer -> Bool
odd k = k `mod` 2 == 1


-- List helpers

sumI :: [Integer] -> Integer
sumI l = case l of [] -> 0
                   h:t -> h + sumI t

tail :: [a] -> [a]
tail l = case l of [] -> []
                   h:t -> t

map :: (a -> b) -> [a] -> [b]
map f l = case l of [] -> []
                    h:t -> f h : map f t

append :: [a] -> [a] -> [a]
append l1 l2 = case l1 of [] -> l2
                          h:t -> h : append t l2

enumFrom :: Integer -> [Integer]
enumFrom k = k : enumFrom (k + 1)

enumFromTo :: Integer -> Integer -> [Integer]
enumFromTo a b = if b < a then [] else a : enumFromTo (a + 1) b

idxLL :: Integer -> [[Integer]] -> [Integer]
idxLL n l = case l of [] -> []
                      h:t -> if n == 0 then h else idxLL (n - 1) t

zip :: [a] -> [b] -> [(a, b)]
zip as bs = case as of
              [] -> []
              a:ta -> case bs of [] -> []
                                 b:tb -> (a, b) : zip ta tb

zipWithMul :: [Integer] -> [Integer] -> [Integer]
zipWithMul as bs = case as of
                     [] -> []
                     a:ta -> case bs of [] -> []
                                        b:tb -> a * b : zipWithMul ta tb

zipWithAdd :: [Integer] -> [Integer] -> [Integer]
zipWithAdd as bs = case as of
                     [] -> []
                     a:ta -> case bs of [] -> []
                                        b:tb -> a + b : zipWithAdd ta tb

zipWithSign :: [Bool] -> [Integer] -> [Integer]
zipWithSign bsl xs = case bsl of
                       [] -> []
                       b:tb -> case xs of [] -> []
                                          x:tx -> (if b then x else 0 - x)
                                                  : zipWithSign tb tx


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
