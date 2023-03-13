main :: IO ()
main = Ret ()

get :: String -> Integer -> Integer
get s idx = #(__Elem) s idx

index :: String -> Integer -> Maybe Integer
index s idx = if idx < 0 then Nothing
              else if length s < idx + 1 then Nothing
              else Just (get s idx)

length :: String -> Integer
length s = #(__Len) s

concat :: String -> String -> String
concat s1 s2 = #(__Concat) s1 s2

substring2 :: String -> Integer -> String
substring2 s start = #(__Substring) s start

substring3 :: String -> Integer -> Integer -> String
substring3 s start len = #(__Substring) s start len

equal :: String -> String -> Bool
equal s1 s2 = #(__StrEq) s1 s2

less :: String -> String -> Bool
less s1 s2 = #(__StrLt) s1 s2

greater :: String -> String -> Bool
greater s1 s2 = #(__StrGt) s1 s2

leq :: String -> String -> Bool
leq s1 s2 = #(__StrLeq) s1 s2

geq :: String -> String -> Bool
geq s1 s2 = #(__StrGeq) s1 s2

implode :: [Integer] -> String
implode l = case l of [] -> ""
                      h:t -> concat (#(__Implode) h) (implode t)

explode :: String -> [Integer]
explode s =
  let from i = if i < length s then get s i : from (i + 1) else []
  in from 0

reverse :: String -> String
reverse s =
  let revAux i limit acc = if i == limit then acc else
                           revAux (i + 1) limit ((get s i) : acc)
  in implode (revAux 0 (length s) [])


-- Helpers

data Maybe a = Nothing | Just a

