main :: IO ()
main = Ret ()

fst :: (a, b) -> a
fst p = case p of (a, b) -> a

snd :: (a, b) -> b
snd p = case p of (a, b) -> b

curry :: ((a, b) -> c) -> a -> b -> c
curry f a b = f (a, b)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f p = case p of (a, b) -> f a b

