-- nofib imaginary/wheel-sieve1: Colin Runciman's "Mark I" lazy wheel sieve.
-- Computes the n-th prime (0-indexed). The single argument is n.
-- List comprehensions are desugared to concatMap/filter and the nested
-- `Wheel s ns : ws` patterns are split into separate cases (PureLang has no
-- nested patterns). The self-referential `primes` knot relies on laziness.

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print ("prime " ++ toString n ++ " = " ++ toString (prime n))
  Ret ()

data Wheel = Wheel Integer [Integer]

prime :: Integer -> Integer
prime n =
  let primes = sieve (wheels primes) primes (squares primes) n
  in idx n primes

sieve :: [Wheel] -> [Integer] -> [Integer] -> Integer -> [Integer]
sieve wl ps qs input =
  case wl of
    [] -> []
    w:ws ->
      case w of
        Wheel s ns ->
          let k0 = minI (input * input) (head ps - 1)
              noFactor x = if not (2 < s) then True else notDivBy ps qs x
              -- The leading `1 :` keeps the first multiple (o = s) available
              -- without forcing k0 (which needs `head ps`); this unties the
              -- self-referential `primes` knot, matching the original's `s:[..]`.
              front =
                concatMap
                  (\kk ->
                     let o = s * kk
                     in concatMap (\nn -> let n' = nn + o
                                          in if noFactor n' then [n'] else [])
                                  ns)
                  (1 : enumFromTo 2 k0)
          in append front (sieve ws (tail ps) (tail qs) input)

notDivBy :: [Integer] -> [Integer] -> Integer -> Bool
notDivBy ps qs n =
  case ps of
    [] -> True
    p:ps' ->
      case qs of
        [] -> True
        q:qs' -> orB (q > n) (andB (n `mod` p > 0) (notDivBy ps' qs' n))

squares :: [Integer] -> [Integer]
squares ps = map (\p -> p * p) ps

wheels :: [Integer] -> [Wheel]
wheels ps =
  let ws = Wheel 1 [1] : zipWith nextSize ws ps
  in ws

nextSize :: Wheel -> Integer -> Wheel
nextSize w p =
  case w of
    Wheel s ns ->
      let ns' =
            concatMap
              (\kk ->
                 let o = s * kk
                 in concatMap (\nn -> let n' = nn + o
                                      in if n' `mod` p > 0 then [n'] else [])
                              ns)
              (enumFromTo 0 (p - 1))
      in Wheel (s * p) ns'


-- List helpers

andB :: Bool -> Bool -> Bool
andB a b = case a of True -> b
                     False -> False

orB :: Bool -> Bool -> Bool
orB a b = case a of True -> True
                    False -> b

not :: Bool -> Bool
not b = case b of True -> False
                  False -> True

minI :: Integer -> Integer -> Integer
minI a b = if a < b then a else b

head :: [Integer] -> Integer
head l = case l of [] -> 0
                   h:t -> h

tail :: [a] -> [a]
tail l = case l of [] -> []
                   h:t -> t

idx :: Integer -> [Integer] -> Integer
idx n l = case l of [] -> 0
                    h:t -> if n == 0 then h else idx (n - 1) t

map :: (a -> b) -> [a] -> [b]
map f l = case l of [] -> []
                    h:t -> f h : map f t

append :: [a] -> [a] -> [a]
append l1 l2 = case l1 of [] -> l2
                          h:t -> h : append t l2

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f acc l = case l of [] -> acc
                          h:t -> f h (foldr f acc t)

concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = foldr (\a -> append (f a)) []

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f as bs =
  case as of [] -> []
             a:ta -> case bs of [] -> []
                                b:tb -> f a b : zipWith f ta tb

enumFromTo :: Integer -> Integer -> [Integer]
enumFromTo a b = if b < a then [] else a : enumFromTo (a + 1) b


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
