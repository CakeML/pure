numbers :: [Int]
numbers =
  let num n = n : num (n + 1)
  in num 0

-- take :: Int -> [a] -> [a]
-- take n l =
--   if n == 0 then []
--   else
--    case l of
--      [] -> []
--      h:t -> h : take (n - 1) t

factA :: Int -> Int -> Int
factA a n = if n < 2 then a else factA (a * n) (n - 1)

fact :: Int -> Int
fact = factA 1

-- map :: (a -> b) -> [a] -> [b]
-- map f l =
--   case l of
--     [] -> []
--     h:t -> f h : map f t

factorials :: [Int]
factorials = map fact numbers

-- head :: [a] -> IO a
-- head l = case l of
--            [] -> raise "Empty"
--            h:t -> return h

-- ffi_action :: Message -> IO String
-- array_length :: Array a -> IO Int
-- return :: a -> IO a

str_elem :: String -> Int -> Int
str_elem s i = ord (s !! i)

strlen :: String -> Int
strlen = length
