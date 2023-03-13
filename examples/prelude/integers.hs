main :: IO ()
main = Ret ()

numbers :: Integer -> [Integer]
numbers n = n : numbers (n + 1)

abs :: Integer -> Integer
abs n = if n < 0 then 0 - n else n

isEven :: Integer -> Bool
isEven n = if n == 0 then True
           else isOdd (abs n - 1)

isOdd :: Integer -> Bool
isOdd n = if n == 0 then False
          else isEven (abs n - 1)

exp :: Integer -> Integer -> Integer
exp n a =
  let expAux acc a = if a < 1 then acc else expAux (acc * n) (a - 1)
  in exp 1 a

ntimes :: Integer -> (a -> a) -> a -> a
ntimes n f x = if n < 1 then x
               else ntimes (n - 1) f (f x)

fibonacci :: Integer -> Integer
fibonacci n =
  if n < 1 then 0 else
  let fib n a b = if n == 0 then b
                  else fib (n - 1) b (a + b)
  in fib n 0 1

factorial :: Integer -> Integer
factorial n =
  if n < 1 then 0 else
  let fact n acc = if n == 1 then acc
                   else fact (n - 1) (n * acc)
  in fact n 1

gcd :: Integer -> Integer -> Integer
gcd n m =
  let gcd' a b = if b == 0 then a
                 else gcd' b (a `mod` b)
  in gcd' (abs n) (abs m)

collatz :: Integer -> [Integer]
collatz n =
  let n' = abs n
      rest = if n' < 2 then []
             else if n' `mod` 2 == 0 then collatz (n `div` 2)
             else collatz (3 * n + 1)
  in n' : rest

primitiveRecursion :: (Integer -> Integer) -> (Integer -> Integer -> Integer -> Integer) -> (Integer -> Integer -> Integer)
primitiveRecursion f g x y =
  if y == 0 then f x
  else g x (y - 1) (primitiveRecursion f g x (y - 1))

minimisation :: (Integer -> Integer -> Integer) -> Integer -> Integer
minimisation f x =
  let min' f x n = if f x n == 0 then n
                   else min' f x (n + 1)
  in min' f x 0

ackermann :: Integer -> Integer -> Integer
ackermann m n =
  if m < 0 then ackermann (abs m) n
  else if n < 0 then ackermann m (abs n)
  else if m == 0 then n + 1
  else if n == 0 then (m - 1)
  else ackermann (m - 1) (ackermann m (n - 1))

fromString :: String -> Integer
fromString s =
  let fromStringAux i limit acc s =
        if limit == i then acc
        else if limit < i then acc
        else fromStringAux (i + 1) limit (acc * 10 + (#(__Elem) s i - 48)) s
  in fromStringAux 0 (#(__Len) s) 0 s

toString :: Integer -> String
toString i =
  let toStringAux acc i = if i == 0 then acc
                          else toStringAux ((i `mod` 10 + 48) : acc) (i `div` 10)
      implode l = case l of [] -> ""
                            h:t -> #(__Concat) (#(__Implode) h) (implode t)
  in if i < 0 then #(__Concat) "-" (toString (abs i))
     else if i == 0 then "0"
     else implode (toStringAux [] i)

