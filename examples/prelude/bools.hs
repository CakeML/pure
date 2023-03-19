main :: IO ()
main = Ret ()

not :: Bool -> Bool
not b = if b then False else True

equal :: Bool -> Bool -> Bool
equal b1 b2 = if b1 then b2 else not b2

and :: Bool -> Bool -> Bool
and b1 b2 = if b1 then b2 else False

or :: Bool -> Bool -> Bool
or b1 b2 = if b1 then True else b2

xor :: Bool -> Bool -> Bool
xor b1 b2 = not (equal b1 b2)

toString :: Bool -> String
toString b = if b then "True" else "False"

fromString :: String -> Maybe Bool
fromString s = if #(__StrEq) s "True" then Just True
               else if #(__StrEq) s "False" then Just False
               else Nothing


-- Helpers

data Maybe a = Nothing | Just a

