-- nofib imaginary/exp3_8: compute 3^n using Peano numerals (unary naturals)
-- and print the resulting integer. Stresses allocation and lazy evaluation.
-- The original computes `int (3 ^ 8)` = 6561.

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print ("int (3 ^ " ++ toString n ++ ") = "
         ++ toString (natToInt (powNat (intToNat 3) n)))
  Ret ()

data Nat = Z | S Nat

addNat :: Nat -> Nat -> Nat
addNat m n = case m of Z -> n
                       S m' -> S (addNat m' n)

mulNat :: Nat -> Nat -> Nat
mulNat m n = case m of Z -> Z
                       S m' -> addNat n (mulNat m' n)

powNat :: Nat -> Integer -> Nat
powNat base e = if e == 0 then S Z else mulNat base (powNat base (e - 1))

intToNat :: Integer -> Nat
intToNat i = if i < 1 then Z else S (intToNat (i - 1))

natToInt :: Nat -> Integer
natToInt n =
  let go acc m = case m of Z -> acc
                           S m' -> go (acc + 1) m'
  in go 0 n


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
