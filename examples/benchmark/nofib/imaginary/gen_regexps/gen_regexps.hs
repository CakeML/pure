-- nofib imaginary/gen_regexps: Wentworth's generator of all expansions of a
-- generalised regular expression. The single argument is the regex, e.g.
--   "[a-j][a-j][0-9]"  or  "<1-30>foo".
-- Following the RJE variant, we print the total number of characters produced
-- (rather than the expansions themselves), which is deterministic and avoids a
-- huge output. PureLang strings are byte arrays, so we work on lists of
-- character codes (Integer).

main :: IO ()
main = do
  regex <- read_arg1
  print ("characters generated: " ++ toString (numchars (expand (explode regex))))
  Ret ()

-- A "string" here is a [Integer] of character codes. expand : regex -> [string]
expand :: [Integer] -> [[Integer]]
expand l =
  case l of
    [] -> [[]]
    h:t -> if h == 60 then numericRule t          -- '<'
           else if h == 91 then alphabeticRule t   -- '['
           else constantRule (h : t)

constantRule :: [Integer] -> [[Integer]]
constantRule l = case l of [] -> [[]]
                           c:rest -> map (\z -> c : z) (expand rest)

-- after '[': a '-' b ']' rest
alphabeticRule :: [Integer] -> [[Integer]]
alphabeticRule l =
  case l of
    a:rest1 ->
      case rest1 of
        dash:rest2 ->
          case rest2 of
            b:rest3 ->
              case rest3 of
                close:rest ->
                  let range = if not (b < a) then enumFromTo a b
                              else enumFromToDown a b
                  in concatMap (\c -> map (\z -> c : z) (expand rest)) range
                [] -> [[]]
            [] -> [[]]
        [] -> [[]]
    [] -> [[]]

-- after '<': p '-' r '>' s
numericRule :: [Integer] -> [[Integer]]
numericRule x =
  let pq = span45 x                       -- split on '-'
  in case pq of
       (p, q0) ->
         let q = dropFirst q0
             rs = span62 q                 -- split on '>'
         in case rs of
              (r, s0) ->
                let s = dropFirst s0
                    u = mknum p
                    v = mknum r
                    range = if u < v then enumFromTo u v else enumFromToDown u v
                    width = max (length (intDigits u)) (length (intDigits v))
                in concatMap
                     (\i -> map (\z -> append (pad width (intDigits i)) z) (expand s))
                     range

mknum :: [Integer] -> Integer
mknum = foldl (\u c -> u * 10 + (c - 48)) 0

-- decimal digits of a non-negative integer as char codes
intDigits :: Integer -> [Integer]
intDigits i =
  let go i = if i == 0 then [] else (i `mod` 10 + 48) : go (i `div` 10)
  in if i == 0 then [48] else reverse (go i)

pad :: Integer -> [Integer] -> [Integer]
pad width s = append (replicate (width - length s) 48) s

numchars :: [[Integer]] -> Integer
numchars l = sum (map length l)


-- List / string helpers

not :: Bool -> Bool
not b = case b of True -> False
                  False -> True

max :: Integer -> Integer -> Integer
max a b = if a < b then b else a

explode :: String -> [Integer]
explode s =
  let go i n = if not (i < n) then [] else #(__Elem) s i : go (i + 1) n
  in go 0 (#(__Len) s)

length :: [a] -> Integer
length l = case l of [] -> 0
                     h:t -> 1 + length t

sum :: [Integer] -> Integer
sum l = case l of [] -> 0
                  h:t -> h + sum t

map :: (a -> b) -> [a] -> [b]
map f l = case l of [] -> []
                    h:t -> f h : map f t

append :: [a] -> [a] -> [a]
append l1 l2 = case l1 of [] -> l2
                          h:t -> h : append t l2

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f acc l = case l of [] -> acc
                          h:t -> f h (foldr f acc t)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f acc l = case l of [] -> acc
                          h:t -> foldl f (f acc h) t

concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = foldr (\a -> append (f a)) []

replicate :: Integer -> a -> [a]
replicate n x = if n < 1 then [] else x : replicate (n - 1) x

enumFromTo :: Integer -> Integer -> [Integer]
enumFromTo a b = if b < a then [] else a : enumFromTo (a + 1) b

enumFromToDown :: Integer -> Integer -> [Integer]
enumFromToDown a b = if a < b then [] else a : enumFromToDown (a - 1) b

dropFirst :: [a] -> [a]
dropFirst l = case l of [] -> []
                        h:t -> t

-- span (/= '-')  (45)
span45 :: [Integer] -> ([Integer], [Integer])
span45 l = case l of
             [] -> ([], [])
             h:t -> if h == 45 then ([], h : t)
                    else case span45 t of (a, b) -> (h : a, b)

-- span (/= '>')  (62)
span62 :: [Integer] -> ([Integer], [Integer])
span62 l = case l of
             [] -> ([], [])
             h:t -> if h == 62 then ([], h : t)
                    else case span62 t of (a, b) -> (h : a, b)


-- I/O helpers

f $ x = f x

s1 ++ s2 = #(__Concat) s1 s2

reverse :: [a] -> [a]
reverse l =
  let revA a l = case l of [] -> a
                           h:t -> revA (h:a) t
  in revA [] l

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
