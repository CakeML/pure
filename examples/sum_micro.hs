
numbers :: [Integer]
numbers = [1,2,3,4]

add :: Integer -> Integer -> Integer
add n m = n + m

sum :: [Integer] -> Integer
sum = foldr add 0

main :: IO ()
main = seq (sum numbers) (return ())


-- Standard functions

foldr :: (a -> b -> b) -> b -> [a] -> [b]
foldr f x l =
   case l of
     [] -> x
     h:t -> f h (foldr f x t)

print s = Act (#(stdout) (s ++ "\n"))


-- Overloads

s1 ++ s2 = #(__Concat) s1 s2

return v = Ret v
