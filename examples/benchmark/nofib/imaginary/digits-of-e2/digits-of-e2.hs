-- nofib imaginary/digits-of-e2: compute n digits of e using the factorial-base
-- carry-propagation method (John Hughes). The single argument is the number of
-- output characters; we print e as "2.71828...".
--
-- The original leaves `carryPropagate base []` undefined and relies on lazy
-- irrefutable patterns never forcing it. PureLang's `case` is strict, so we
-- terminate the recursion explicitly; the `2*n`-element budget keeps this
-- boundary out of the first n reported digits.

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print (e n)
  Ret ()

e :: Integer -> String
e n =
  let seed = 2 : replicate (2 * n - 1) 1
      stream = genStream (n + 2) seed
      digits = concatStrs (map (\xs -> toString (head xs)) stream)
  in #(__Substring) (#(__Concat) "2." (#(__Substring) digits 1)) 0 n

genStream :: Integer -> [Integer] -> [[Integer]]
genStream cnt xs =
  if cnt == 0 then []
  else xs : genStream (cnt - 1) (carryPropagate 2 (map (\d -> 10 * d) (tail xs)))

carryPropagate :: Integer -> [Integer] -> [Integer]
carryPropagate base l =
  case l of
    [] -> [0]
    d:ds ->
      let carryguess = d `div` base
          remainder = d `mod` base
          rest = carryPropagate (base + 1) ds
      in case rest of
           [] -> [0]
           nextcarry:fraction ->
             let dCorrected = d + nextcarry
             in if carryguess == (d + 9) `div` base
                then carryguess : (remainder + nextcarry) : fraction
                else (dCorrected `div` base) : (dCorrected `mod` base) : fraction


-- List helpers

head :: [Integer] -> Integer
head l = case l of [] -> 0
                   h:t -> h

tail :: [a] -> [a]
tail l = case l of [] -> []
                   h:t -> t

map :: (a -> b) -> [a] -> [b]
map f l = case l of [] -> []
                    h:t -> f h : map f t

replicate :: Integer -> a -> [a]
replicate n x = if n < 1 then [] else x : replicate (n - 1) x

concatStrs :: [String] -> String
concatStrs l = case l of [] -> ""
                         h:t -> #(__Concat) h (concatStrs t)


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
