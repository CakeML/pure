-- Compute number of N-Queens solutions (brute force)
-- adapted from albertnetymk.github.io


main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print $ "Finding no. N-Queens solutions for board size " ++ toString n
  let boards = queens n
  print $ "No. solutions: " ++ toString (length boards)
  Ret ()

queens :: Integer -> [[Integer]]
queens n =
  if n < 0 then [] else
  let test x c n = and [not (x == c), not (x == c + n), not (x == c - n)]

      noCapture x l n =
        case l of
          [] -> True
          h:t -> and [test x h n, noCapture x t (n + 1)]

      extend current board =
        if current < n + 1 then
          let rest = extend (current + 1) board
          in if noCapture current board 1 then (current : board) : rest else rest
        else []

      iter boards counter =
        if counter == n then boards
        else iter (concatMap (extend 1) boards) (counter + 1)

  in iter [[]] 0

printBoard :: [[Integer]] -> IO String
printBoard l =
  let rowToString l = case l of [] -> ""
                                h:t -> toString h ++ rowToString t
      boardToString l = case l of [] -> ""
                                  h:t -> rowToString h ++ "\n" ++ boardToString t
  in print (boardToString l)


-- Helper functions

and :: [Bool] -> Bool
and l = case l of [] -> True
                  h:t -> if h then and t else False

not :: Bool -> Bool
not b = case b of True -> False
                  False -> True

length :: [a] -> Integer
length l = case l of [] -> 0
                     h:t -> 1 + length t

append :: [a] -> [a] -> [a]
append l1 l2 = case l1 of [] -> l2
                          h:t -> h : append t l2

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f acc l = case l of [] -> acc
                          h:t -> f h (foldr f acc t)

concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = foldr (\a -> append (f a)) []


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
        else
          fromStringI (i + 1) limit (acc * 10 + (#(__Elem) s i - 48)) s
  in fromStringI 0 (#(__Len) s) 0 s

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

