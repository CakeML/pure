-- nofib imaginary/rfib: the notorious `nfib` recursion benchmark.
-- The original returns `Double`; PureLang has only `Integer`, so this is the
-- integer `nfib` (nfib n = number of calls, = 2*fib(n+1) - 1).

main :: IO ()
main = do
  arg1 <- read_arg1
  let n = fromString arg1
  print ("nfib " ++ toString n ++ " = " ++ toString (nfib n))
  Ret ()

nfib :: Integer -> Integer
nfib n = if n < 2 then 1 else nfib (n - 1) + nfib (n - 2) + 1


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
