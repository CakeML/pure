-- nofib imaginary/tak: the Takeuchi function, a classic recursion micro-benchmark.
-- Single argument n; computes `tak (3n) (2n) n` (n = 8 gives the classic `tak 24 16 8`).

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
      x = 3 * n
      y = 2 * n
  print ("tak " ++ toString x ++ " " ++ toString y ++ " " ++ toString n
         ++ " = " ++ toString (tak x y n))
  Ret ()

tak :: Integer -> Integer -> Integer -> Integer
tak x y z =
  if not (y < x) then z
  else tak (tak (x - 1) y z) (tak (y - 1) z x) (tak (z - 1) x y)


-- Helper functions

not :: Bool -> Bool
not b = case b of True -> False
                  False -> True


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
