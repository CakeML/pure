-- Simple functional and imperative quicksort
-- import Prelude hiding (and)

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  printOnly $ "Sorting the *list* [" ++ toString n ++ "..0]... "
  let res = qsortList (numbersList n)
  print $ if isSortedList res then "Success!" else "Failure :("
  printOnly $ "Sorting the *array* [" ++ toString n ++ "..0]... "
  a <- numbersArray n
  len <- Length a
  qsortArray a
  ok <- isSortedArray a
  print $ if ok then "Success!" else "Failure :("
  Ret ()


-- Functional quicksort

qsortList :: [Int] -> [Int]
qsortList l =
  case l of
    [] -> []
    h:t ->
      let parts = partitionList h t
      in case parts of
          (less, greaterEq) ->
            append (qsortList less) (h : qsortList greaterEq)


partitionList :: Int -> [Int] -> ([Int],[Int])
partitionList pivot l =
  case l of
    [] -> ([],[])
    h:t ->
      let rest = partitionList pivot t
      in case rest of
          (less, greaterEq) ->
            if h < pivot then (h:less, greaterEq)
            else (less, h:greaterEq)


-- Imperative quicksort

qsortArray :: Array Int -> IO ()
qsortArray a =
  let qsortAux a lo hi =
        if lo < 0 then Ret ()
        else if hi < lo + 1 then Ret ()
        else do
          pivot <- partitionArray a lo hi
          qsortAux a lo (pivot - 1)
          qsortAux a (pivot + 1) hi
  in do
    len <- Length a
    qsortAux a 0 (len - 1)


partitionArray :: Array Int -> Int -> Int -> IO Int
partitionArray a lo hi = do
  pivotElem <- Deref a hi
  let loop i j = do
        if j < hi then do
          jElem <- Deref a j
          if jElem < pivotElem + 1 then do
            do swap a (i + 1) j ; loop (i + 1) (j + 1)
            else loop i (j + 1)
         else Ret i
  i <- loop (lo - 1) lo
  swap a (i + 1) hi
  Ret (i + 1)

swap :: Array a -> Int -> Int -> IO ()
swap a i j = do
  iElem <- Deref a i
  jElem <- Deref a j
  Update a i jElem
  Update a j iElem


-- List helper functions

append :: [a] -> [a] -> [a]
append l1 l2 = case l1 of [] -> l2
                          h:t -> h : append t l2

numbersList :: Int -> [Int]
numbersList n = if n < 0 then []
                else n : numbersList (n - 1)

-- numbersList :: Int -> [Int]
-- numbersList n =
--   let numbersAux current =
--         if current < n then current : numbersAux (current + 1) else []
--   in if n < 0 then [] else numbersAux 0

isSortedList :: [Int] -> Bool
isSortedList l =
  let sortedAux last l =
        case l of [] -> True
                  h:t -> if last < h + 1 then sortedAux h t
                         else False
  in case l of [] -> True
               h:t -> sortedAux h t


-- Array helper functions

numbersArray :: Int -> IO (Array Int)
numbersArray n =
  let length = if n < 0 then 0 else n
      fill a next remaining =
        if remaining == 0 then Ret ()
        else do
          Update a next remaining
          fill a (next + 1) (remaining - 1)
  in do
    a <- Alloc length 0
    fill a 0 length
    Ret a

isSortedArray :: Array Int -> IO Bool
isSortedArray a =
  let loop lastElem nextIdx len =
        if nextIdx < len then do
          nextElem <- Deref a nextIdx
          if lastElem < nextElem + 1 then
            loop nextElem (nextIdx + 1) len
           else Ret False
        else Ret True
  in do
    len <- Length a
    if len < 1 then Ret True else do
      first <- Deref a 0
      loop first 1 len

printArray :: Array Int -> IO ()
printArray a =
  let printAux i len =
        if i < len then do
          elem <- Deref a i
          printOnly (toString elem)
          if i < len - 1 then
            do printOnly ", " ; Ret ()
            else Ret ()
          printAux (i + 1) len
        else Ret ()
  in do
    printOnly "["
    len <- Length a
    printAux 0 len
    printOnly "]\n"
    Ret ()


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

printOnly s = Act (#(stdout) s)

print s = Act (#(stdout) (s ++ "\n"))

