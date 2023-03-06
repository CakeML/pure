main :: IO ()
main = do
  Ret (compose, s, k, i, fix)
  Ret ()

f $ x = f x

f |> x = f x

compose :: (b -> c) -> (a -> b) -> a -> c
compose f g = \x -> f (g x)

s :: (a -> b -> c) -> (a -> b) -> a -> c
s x y z = x z (y z)

k :: a -> b -> a
k x y = x

i :: a -> a
i x = x

fix :: (a -> a) -> a
fix f = f (fix f)

