main :: IO ()
main = Ret ()

alloc :: Integer -> a -> IO Array a
alloc len elem = Alloc len elem

length :: Array a -> IO Integer
length a = Length a

get :: Array a -> Integer -> IO a
get a idx = Deref a idx

getAndHandle :: Array a -> Integer -> (Exception -> Integer) -> IO Integer
getAndHandle a idx handler = Handle (get a idx) (\e -> Ret (handler e))

update :: Array a -> Integer -> a -> IO ()
update a idx a' = Update a idx a'

index :: Array a -> Integer -> IO (Maybe a)
index a idx =
  if idx < 0 then Ret Nothing else do
    len <- length a
    if len < idx + 1 then Ret Nothing else do
      elem <- get a idx
      Ret (Just elem)

toString :: (a -> String) -> Array String -> IO String
toString f a =
  let toStringAux i len =
        if i < len then do
          elem <- Deref a i
          rest <- toStringAux (i + 1) len
          Ret (#(__Concat) (f elem) (if i < len - 1 then ", " else "") rest)
        else Ret ""
  in do
    len <- Length a
    inner <- toStringAux 0 len
    Ret (#(__Concat) "[" inner "]")


-- Helpers
data Maybe a = Nothing | Just a

