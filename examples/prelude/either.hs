main :: IO ()
main = do
  Ret either
  Ret ()

data Either a b = Left a | Right b

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f g e = case e of Left a -> f a
                         Right b -> g b

