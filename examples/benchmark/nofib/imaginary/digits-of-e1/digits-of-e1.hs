-- nofib imaginary/digits-of-e1: compute the first n digits of e using a
-- continued-fraction "spigot" (Dale Thurston). The single argument is the
-- number of digits. We print the digits as "2.71828..." (the original hashes
-- the list; here we show it directly).

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print (showE (e n))
  Ret ()

-- The continued-fraction expansion of e: [2,1,2,1,1,4,1,1,6,1,...]
eContFrac :: [Integer]
eContFrac = 2 : aux 2

aux :: Integer -> [Integer]
aux n = 1 : n : 1 : aux (n + 2)

-- ratTrans (a,b,c,d) x: emit (a + b*x)/(c + d*x) as a continued fraction.
ratTrans :: (Integer, Integer, Integer, Integer) -> [Integer] -> [Integer]
ratTrans t xs =
  case t of
    (a, b, c, d) ->
      let q = b `div` d
          noPole = orB (signum c == signum d) (absI c < absI d)
          determined = andB (not ((a + b) < (c + d) * q))
                            ((c + d) * q + (c + d) > a + b)
      in if andB noPole determined
         then q : ratTrans (c, d, a - q * c, b - q * d) xs
         else case xs of
                [] -> []
                x:rest -> ratTrans (b, a + x * b, d, c + x * d) rest

takeDigits :: Integer -> [Integer] -> [Integer]
takeDigits n l =
  if n == 0 then []
  else case l of
         [] -> []
         x:xs -> x : takeDigits (n - 1) (ratTrans (10, 0, 0, 1) xs)

e :: Integer -> [Integer]
e n = takeDigits n eContFrac

showE :: [Integer] -> String
showE l = case l of
            [] -> ""
            h:t -> toString h ++ "." ++ concatDigits t

concatDigits :: [Integer] -> String
concatDigits l = case l of [] -> ""
                           h:t -> toString h ++ concatDigits t


-- Helpers

andB :: Bool -> Bool -> Bool
andB a b = case a of True -> b
                     False -> False

orB :: Bool -> Bool -> Bool
orB a b = case a of True -> True
                    False -> b

not :: Bool -> Bool
not b = case b of True -> False
                  False -> True

signum :: Integer -> Integer
signum i = if i < 0 then 0 - 1 else if i == 0 then 0 else 1

absI :: Integer -> Integer
absI i = if i < 0 then 0 - i else i


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
