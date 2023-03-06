main :: IO ()
main = do
  Ret (append, head, last, tail, singleton, null, length)
  Ret (map, reverse)
  Ret (foldr, foldl, unfoldr, concat, all, any)
  Ret (iterate, repeat, replicate)
  Ret (take, drop)
  Ret (filter, first, lookup, index)
  Ret (interleave, zipWith, unzip)
  Ret (toString)
  Ret ()


-- Basic operations

append :: [a] -> [a] -> [a]
append l1 l2 = case l1 of [] -> l2
                          h:t -> h : append t l2

head :: [a] -> Maybe a
head l = case l of [] -> Nothing
                   h:t -> Just h

last :: [a] -> Maybe a
last l = case l of [] -> Nothing
                   h:t -> if null t then Just h else last t

tail :: [a] -> [a]
tail l = case l of [] -> []
                   h:t -> t

singleton :: a -> [a]
singleton a = [a]

null :: [a] -> Bool
null l = case l of [] -> True
                   h:t -> False

length :: [a] -> Integer
length l = case l of [] -> 0
                     h:t -> 1 + length t


-- List transformations

map :: (a -> b) -> [a] -> [b]
map f l = case l of [] -> []
                    h:t -> f h : map f t

reverse :: [a] -> [a]
reverse l =
  let revA a l = case l of [] -> a
                           h:t -> revA (h:a) t
  in revA [] l


-- Folds / unfolds

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f acc l = case l of [] -> acc
                          h:t -> f h (foldr f acc t)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f acc l = case l of [] -> acc
                          h:t -> foldl f (f acc h) t

-- foldl' :: (b -> a -> b) -> b -> [a] -> b
-- foldl' f acc l = case l of [] -> acc
--                            h:t -> let acc' = f acc h in
--                                   seq acc' (foldl' f acc' t)

unfoldr :: (b -> Maybe (a, b)) -> b -> [a]
unfoldr f x =
  case f x of Nothing -> []
              Just p -> case p of (a,b) -> a : unfoldr f b

concat :: [[a]] -> [a]
concat ll = case ll of [] -> []
                       h:t -> append h (concat t)

all :: (a -> Bool) -> [a] -> Bool
all f l = case l of [] -> True
                    h:t -> if f h then all f t else False

any :: (a -> Bool) -> [a] -> Bool
any f l = case l of [] -> False
                    h:t -> if f h then True else any f t


-- Generating lists

iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

repeat :: a -> [a]
repeat x = x : repeat x

replicate :: Integer -> a -> [a]
replicate i x = if i < 1 then [] else x : replicate (i - 1) x


-- Sublists

take :: Integer -> [a] -> [a]
take n l = if n < 1 then []
           else case l of [] -> []
                          h:t -> h : (take (n - 1) t)

drop :: Integer -> [a] -> [a]
drop n l = if n < 1 then l
           else case l of [] -> []
                          h:t -> drop (n - 1) t


-- Searching / indexing

filter :: (a -> Bool) -> [a] -> [a]
filter f l = case l of [] -> []
                       h:t -> if f h then h : filter f t else filter f t

first :: (a -> Bool) -> [a] -> Maybe (Integer, a)
first f l =
  let firstAux i l =
        case l of [] -> Nothing
                  h:t -> if f h then Just (i, h) else firstAux (i + 1) t
  in firstAux 0 l

lookup :: (a -> Bool) -> [(a,b)] -> Maybe b
lookup eq l =
  case l of [] -> Nothing
            h:t -> case h of (k,v) -> if eq k then Just v else lookup eq t


index :: Integer -> [a] -> Maybe a
index n l = if n < 0 then Nothing else
            case l of [] -> Nothing
                      h:t -> if n == 0 then Just h else index (n - 1) l


-- Combining lists

interleave :: [a] -> [a] -> [a]
interleave l1 l2 = case l1 of [] -> l2
                              h:t -> h : interleave l2 t

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f as bs =
  case as of [] -> []
             a:ta -> case bs of [] -> []
                                b:tb -> f a b : zipWith f ta tb

unzip :: [(a,b)] -> ([a], [b])
unzip l =
  case l of
    [] -> ([], [])
    h:t -> let rest = unzip t
           in case h of (a,b) -> case rest of (as, bs) -> (a:as, b:bs)


-- Convert to string
toString :: (a -> String) -> [a] -> String
toString f l =
  let toStringAux l =
        case l of [] -> ""
                  h:t -> #(__Concat) (f h) (if null t then "" else ", ") (toStringAux t)
  in #(__Concat) "[" (toStringAux l) "]"


-- Helpers

data Maybe a = Nothing | Just a

