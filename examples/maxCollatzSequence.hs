-- Calculate longest Collatz sequence less than n (inefficiently, i.e. w/o memo)
-- import Prelude hiding (map, take)

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print $ "Finding longest Collatz sequence less than " ++ toString n
  let res = maxCollatzSequence n
  print $ "Number with longest sequence: " ++ toString (fst res)
  print $ "Length of sequence: " ++ toString (snd res)
  Ret ()

maxCollatzSequence :: Int -> (Int, Int)
maxCollatzSequence n = maxIndex (take n collatzSequences)

collatzSequences :: [Int]
collatzSequences = map collatzSequence (numbers 0)

collatzSequence :: Int -> Int
collatzSequence n =
  let seqAux acc n =
        if n < 1 then (0-1)
        else if n == 1 then acc
        else seqAux (acc + 1) (collatz n)
  in seqAux 0 n

collatz :: Int -> Int
collatz n = if mod n 2 == 0 then div n 2 else 3 * n + 1


-- Helper functions

numbers :: Int -> [Int]
numbers n = n : numbers (n + 1)

maxIndex :: [Int] -> (Int, Int)
maxIndex l =
  let maxAux maxIdx maxElem idx l =
        case l of [] -> (maxIdx, maxElem)
                  h:t -> if maxElem < h then maxAux idx h (idx + 1) t
                         else maxAux maxIdx maxElem (idx + 1) t
  in maxAux (0-1) (0-1) 0 l

map :: (a -> b) -> [a] -> [b]
map f l = case l of [] -> []
                    h:t -> f h : map f t

take :: Int -> [a] -> [a]
take n l =
  if n < 1 then []
  else case l of [] -> []
                 h:t -> h : take (n - 1) t

fst :: (a, b) -> a
fst p = case p of (a,b) -> a

snd :: (a, b) -> b
snd p = case p of (a,b) -> b


-- I/O helpers

f $ x = f x

s1 ++ s2 = #(__Concat) s1 s2

reverse :: [a] -> [a]
reverse l =
  let revA a l = case l of [] -> a
                           h:t -> revA (h:a) t
  in revA [] l

fromString :: String -> Int
fromString s =
  let fromStringI i limit acc s =
        if limit == i then acc
        else if limit < i then acc
        else
          fromStringI (i + 1) limit (acc * 10 + (#(__Elem) s i - 48)) s
  in fromStringI 0 (#(__Len) s) 0 s

toString :: Int -> String
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

