main :: IO ()
main = do
  Ret (maybe, fold, map, bind, toString)
  Ret ()

data Maybe a = Nothing | Just a

maybe :: a -> Maybe a
maybe a = Just a

fold :: (a -> b) -> b -> Maybe a -> b
fold f b m = case m of Nothing -> b
                       Just a -> f a

map :: (a -> b) -> Maybe a -> Maybe b
map f m = case m of Nothing -> Nothing
                    Just a -> Just (f a)

bind :: Maybe a -> (a -> Maybe b) -> Maybe b
bind m f = fold f Nothing m

toString :: (a -> String) -> Maybe a -> String
toString f m = case m of Nothing -> "Nothing"
                         Just a -> #(__Concat) "Just " (f a)

