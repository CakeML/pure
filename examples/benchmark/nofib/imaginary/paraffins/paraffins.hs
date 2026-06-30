-- nofib imaginary/paraffins: count paraffins (alkanes) and radicals up to size n
-- (Steve Heller, via MIT). The single argument is n.
--
-- The original memoises radical lists in a Data.Array knot. PureLang has no
-- immutable arrays, so we use a lazy self-referential list as the memo. Only
-- list *lengths* affect the counts, so each radical is represented by a dummy 0.

main :: IO ()
main = do
  arg1 <- read_arg1
  let num = fromString arg1
      rads = radical_generator num
  print (showList (map (\i -> length (idxL i rads)) (enumFromTo 0 num)))
  print (showList (bcp_until num))
  print (showList (ccp_until num))
  print (showList (paraffins_until num))
  Ret ()

-- A radical list is represented by [Integer] of dummies; its length is the count.
radical_generator :: Integer -> [[Integer]]
radical_generator num =
  let ms = map (\j -> if j == 0 then [0] else rads_of_size_n ms j) (enumFromTo 0 num)
  in ms

rads_of_size_n :: [[Integer]] -> Integer -> [Integer]
rads_of_size_n ms n =
  concatMap
    (\ijk -> case ijk of
       (i, j, k) ->
         concatMap
           (\rir -> case rir of
              [] -> []
              ri:ris ->
                concatMap
                  (\rjr -> case rjr of
                     [] -> []
                     rj:rjs -> map (\rk -> 0)
                                   (if j == k then rj : rjs else idxL k ms))
                  (remainders (if i == j then rir else idxL j ms)))
           (remainders (idxL i ms)))
    (three_partitions (n - 1))

bcp_generator :: [[Integer]] -> Integer -> [Integer]
bcp_generator ms n =
  if odd n then []
  else concatMap
         (\r1r -> case r1r of
            [] -> []
            r1:r1s -> map (\r2 -> 0) (r1 : r1s))
         (remainders (idxL (n `div` 2) ms))

ccp_generator :: [[Integer]] -> Integer -> [Integer]
ccp_generator ms n =
  concatMap
    (\ijkl -> case ijkl of
       (i, j, k, l) ->
         concatMap
           (\rir -> case rir of
              [] -> []
              ri:ris ->
                concatMap
                  (\rjr -> case rjr of
                     [] -> []
                     rj:rjs ->
                       concatMap
                         (\rkr -> case rkr of
                            [] -> []
                            rk:rks -> map (\rl -> 0)
                                          (if k == l then rk : rks else idxL l ms))
                         (remainders (if j == k then rj : rjs else idxL k ms)))
                  (remainders (if i == j then rir else idxL j ms)))
           (remainders (idxL i ms)))
    (four_partitions (n - 1))

three_partitions :: Integer -> [(Integer, Integer, Integer)]
three_partitions m =
  concatMap
    (\i -> concatMap
             (\j -> let k = m - (i + j) in [(i, j, k)])
             (enumFromTo i ((m - i) `div` 2)))
    (enumFromTo 0 (m `div` 3))

four_partitions :: Integer -> [(Integer, Integer, Integer, Integer)]
four_partitions m =
  concatMap
    (\i -> concatMap
             (\j -> concatMap
                      (\k -> let l = m - (i + j + k) in [(i, j, k, l)])
                      (enumFromTo (max j (((m + 1) `div` 2) - i - j)) ((m - i - j) `div` 2)))
             (enumFromTo i ((m - i) `div` 3)))
    (enumFromTo 0 (m `div` 4))

remainders :: [Integer] -> [[Integer]]
remainders l = case l of [] -> []
                         h:t -> (h : t) : remainders t

bcp_until :: Integer -> [Integer]
bcp_until n =
  let rads = radical_generator (n `div` 2)
  in map (\j -> length (bcp_generator rads j)) (enumFromTo 1 n)

ccp_until :: Integer -> [Integer]
ccp_until n =
  let rads = radical_generator (n `div` 2)
  in map (\j -> length (ccp_generator rads j)) (enumFromTo 1 n)

paraffins_until :: Integer -> [Integer]
paraffins_until n =
  let rads = radical_generator (n `div` 2)
  in map (\j -> length (bcp_generator rads j) + length (ccp_generator rads j))
         (enumFromTo 1 n)


-- Helpers

odd :: Integer -> Bool
odd k = k `mod` 2 == 1

max :: Integer -> Integer -> Integer
max a b = if a < b then b else a

length :: [a] -> Integer
length l = case l of [] -> 0
                     h:t -> 1 + length t

idxL :: Integer -> [[Integer]] -> [Integer]
idxL n l = case l of [] -> []
                     h:t -> if n == 0 then h else idxL (n - 1) t

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

enumFromTo :: Integer -> Integer -> [Integer]
enumFromTo a b = if b < a then [] else a : enumFromTo (a + 1) b

showList :: [Integer] -> String
showList l =
  let go l = case l of [] -> ""
                       h:t -> #(__Concat) (toString h) (if nullL t then "" else ",") (go t)
  in #(__Concat) "[" (go l) "]"

nullL :: [a] -> Bool
nullL l = case l of [] -> True
                    h:t -> False


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
