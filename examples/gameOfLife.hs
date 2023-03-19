-- Game of Life example

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
      parsed = parse circuit
      result = step n parsed
  printGOL result
  Ret ()

circuit :: String
-- This circuit consists of a 100x100 grid containing 5 Gosper guns. The
-- circuit is self-contained, i.e., does not touch the borders of the
-- 100x100 box that it operates within.
circuit = "$bo98bo7$86b2o$86b2o11$68b2o14b2o3b2o$68b2o16b3o$85bo3bo$86bobo$87bo$" ++
          "52b2o$52b2o3$88b3o$82bobo$65b2o3b2o10b2o4bobo$83bo3b5o$66bo3bo15b2o3b" ++
          "2o$67b3o16b2o3b2o$67b3o2$49b2o3b2o20bo$51b3o20b2o12b2o$50bo3bo20b2o$" ++
          "51bobo$52bo13bo5bo6b2o$34bo30b3o5bo4b2o$34bobo28b3o3b3o6bo$17b2o18b2o" ++
          "4b2o$15bo3bo17b2o4b2o18b2o3b2o19b2obob2o$9b2o3bo5bo16b2o14b3o7b2o3b2o" ++
          "19bo5bo$9b2o2b2obo3bo8bo4bobo10bobo40bo3bo$14bo5bo9bo3bo12b2o4bobo31bo" ++
          "3b3o$15bo3bo5bo2b3o17bo3b5o9bo19b2o$17b2o32b2o3b2o7bobo18bobo$51b2o3b" ++
          "2o6b2o6bobo$64b2o9bo6b2o$64b3o8bo6bobo$41bo12bo10bobo4bo2bo3b2obobo$" ++
          "37bob2o11b2o12b2o5b3o3bobobo$35bobo2b2o39bo8bo$36b2o13bo28b2o8bo$79b3o" ++
          "7bobo$52bo2bo23b3o6b2ob2o$54b2o23b3o5bo5bo$80b2o8bo$44bo36bo5b2o3b2o$" ++
          "45bo33bobobo$43b3o33b2obobo$82bobo6bo$74bobo5b2o7bo$73bo18bo$73bo$73bo" ++
          "2bo$73b3o13b2o$89b2o6$59bo$60bo$58b3o21$bo98bo$!"


-- Stepping through the game

step :: Integer -> [[Integer]] -> [[Integer]]
step n l = if n == 0 then l else step (n - 1) (next l)

next :: [[Integer]] -> [[Integer]]
next l = case l of [] -> []
                   h:t -> nextRows (zero h) h t

nextRows :: [Integer] -> [Integer] -> [[Integer]] -> [[Integer]]
nextRows xs ys rows =
  case rows of [] -> nextRow 0 (hd xs) (tl xs)
                             0 (hd ys) (tl ys)
                             0  0      (zero $ tl ys) : []
               zs:rest -> nextRow 0 (hd xs) (tl xs)
                                  0 (hd ys) (tl ys)
                                  0 (hd zs) (tl zs) : nextRows ys zs rest

nextRow :: Integer -> Integer -> [Integer] -> Integer -> Integer -> [Integer] -> Integer -> Integer -> [Integer] -> [Integer]
nextRow x1 x2 xs
        y1 y2 ys
        z1 z2 zs =
  case xs of
    [] -> nextCell x1 x2 0
                   y1 y2 0
                   z1 z2 0 : []
    x3:xs' ->
      let y3  = hd ys
          ys' = tl ys
          z3  = hd zs
          zs' = tl zs in
      nextCell x1 x2 x3
               y1 y2 y3
               z1 z2 z3 :
               nextRow x2 x3 xs'
                       y2 y3 ys'
                       z2 z3 zs'

nextCell :: Integer -> Integer -> Integer -> Integer ->  Integer ->  Integer ->  Integer ->  Integer ->  Integer -> Integer
nextCell x1 x2 x3
         y1 y2 y3
         z1 z2 z3 =
  let sum = x1 + x2 + x3 + y1 + 0 + y3 + z1 + z2 + z3 in
    if y2 == 0 then if sum == 3 then 1 else 0
    else if or (sum == 2) (sum == 3) then 1 else 0


-- Parsing and printing

parse :: String -> [[Integer]]
parse s =
  let width = 102
  in map (pad width 0) $ split $ expand s

expand :: String -> String
expand s =
  let expandAux idx count =
        if strlen s < idx + 1 then "" else
          let e = str_elem s idx
          in if and (47 < e) (e < 58) then expandAux (idx + 1) (count * 10 + e - 48)
             else (implode $ replicate (max 1 count) e) ++ (expandAux (idx + 1) 0)
  in expandAux 0 0

split :: String -> [[Integer]]
split s =
  let splitAux idx acc =
        if strlen s < idx + 1 then [] else
          let e = str_elem s idx in
            if e == 33 then [reverse acc] -- check for '!'
            else if e == 36 then reverse acc : splitAux (idx + 1) [] -- check for '$'
            else splitAux (idx + 1) ((if e == 111 then 1 else 0) : acc) -- check for 'b'/'o'
  in splitAux 0 []

printGOL :: [[Integer]] -> IO String
printGOL l =
  let rowToString l = case l of [] -> ""
                                h:t -> if h == 0 then "-" ++ rowToString t
                                       else "#" ++ rowToString t
      toString l = case l of [] -> ""
                             h:t -> rowToString h ++ "\n" ++ toString t
  in print $ toString l


-- Helper functions

zero :: [Integer] -> [Integer]
zero l = case l of [] -> []
                   h:t -> 0 : zero t

hd :: [Integer] -> Integer
hd l = case l of [] -> 0
                 h:t -> h


-- Standard functions

f $ x = f x

or :: Bool -> Bool -> Bool
or b1 b2 = case b1 of True  -> True
                      False -> b2

and :: Bool -> Bool -> Bool
and b1 b2 = case b1 of False -> False
                       True  -> b2

max :: Integer -> Integer -> Integer
max x y = if x < y then y else x

tl :: [a] -> [a]
tl l = case l of [] -> []
                 h:t -> t

length :: [a] -> Integer
length l = case l of [] -> 0
                     h:t -> 1 + length t

map :: (a -> b) -> [a] -> [b]
map f l = case l of [] -> []
                    h:t -> f h : map f t

reverse :: [a] -> [a]
reverse l =
  let revA a l = case l of [] -> a
                           h:t -> revA (h:a) t
  in revA [] l

append :: [a] -> [a] -> [a]
append l r = case l of [] -> r
                       h:t -> h : append t r

replicate :: Integer -> a -> [a]
replicate n a = if n < 1 then [] else a : replicate (n - 1) a


pad :: Integer -> a -> [a] -> [a]
pad n a l = append l $ replicate (n - length l) a


-- I/O helpers

fromDigit :: String -> Integer -> Integer
fromDigit s i = str_elem s i - 48

fromString :: String -> Integer
fromString s =
  let fromStringI i limit acc s =
        if limit == i then acc
        else if limit < i then acc
        else
          fromStringI (i + 1) limit (acc * 10 + fromDigit s i) s
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

str_eq :: String -> String -> Bool
str_eq s1 s2 = #(__StrEq) s1 s2
