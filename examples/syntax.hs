-- ***** A near-exhaustive demonstration of PureLang syntax *****

-- NB all constructors and built-ins must be fully applied

-- ** Built-ins **

-- Unit and tuples, of types `()`, `(a,b,...)`
unit = ()
unitTriple = ( () , () , () )

-- Booleans, of type `Bool`
bools = (True, False)

-- Arbitrary-precision ("bignum") integers, of type `Integer`
zero = 0
minusOne = ~1
fortyTwo = 42

integerOperations i i' =
  ( i + i'   -- addition
  , i - i'   -- subtraction
  , i * i'   -- multiplication
  , div i i' -- integer division (round down, i.e. -3 / 2 == -2) - NB ∀i. i / 0 == 0
  , mod i i' -- modulus (e.g. mod 5 2 == 1) - NB negative when i' is negative, and ∀i. mod i 0 == 0
  )

integerComparisons i i' = -- return type `Bool`
  ( i == i'  -- equality
  , i < i'   -- less than
  , i > i'   -- greater than
--  , i <= i'  -- coming soon: less than or equal
--  , i >= i'  -- coming soon: greater than or equal to
  )

-- Strings, of type `String`
-- NB strings are *not* lists of characters, but packed-bytes (like Haskell's `Text`)
-- we use `Integer` for character-based operations
stringLiterals = ( "" , "Hello" , "World!" , "\n")

stringOperations s s' =
  ( #(__Len) s              -- length
  , #(__Elem) s 0           -- index a character (i.e. `Integer` - -1 if out of bounds)
  , #(__Concat) s s'        -- concatenation (multi-arity, i.e. #(__Concat) s1 s2 s3 ... is fine)
  , #(__Implode) 70 111 111 -- string from integers, i.e. "Foo" (multi-arity, considers input modulus 256)
  , #(__Substring) s 2      -- substring, removes first two characters
  , #(__Substring) s 2 5    -- substring, removes first two characters and takes next five
  )                         -- NB substring operations will adjust bounds to fall within the string

stringComparisons s s' = -- return type `Bool`
  ( #(__StrEq)  s s' -- equality
  , #(__StrLt)  s s' -- less than
  , #(__StrLeq) s s' -- less than or equal
  , #(__StrGt)  s s' -- greater than
  , #(__StrGeq) s s' -- greater than or equal to
  )

-- Lists, of type `[a]`
listLiterals = ( [] , [1,2,3] , 4:5:6:[] )


-- ** Monadic operations, returning type `IO a` **

-- Monadic sequencing
return x = Ret x
bind x f = Bind x f

doNotation f g input = do
  Ret ()      -- return value, do not bind result
  x <- input  -- bind value
  let y = f x -- pure assignment
  g y
-- can use indentation insenstive forms:
--   x <- input ; Ret x      { x <- input
--                         Ret x }

-- Arrays, of type `Array a`
arrayOperations a len elem idx =
  ( Alloc len elem -- allocate with length `len`, filled with `elem`
  , Length a -- length
  , Deref a idx -- index, throws `Subscript` on out-of-bounds
  , Update a idx elem -- update at index, throws `Subscript` on out-of-bounds
  )

-- Exceptions
-- coming soon: declarable exceptions, i.e. ML-style extensible exception type
-- e.g. exn MyException String
exceptions = [ Subscript ]

throwException = Raise Subscript
exceptionHandler e = Ret "oops!"
handleException = Handle throwException exceptionHandler


-- Foreign function interface
performFFI ffiAction = Act ffiAction

printAction string = #(stdout) string -- does not add line break
readArgumentAction = #(cline_arg) " "
-- TODO others?


-- ** Expressions and declarations **

-- Top-level declarations - mutually recursive, reorderable
myFunc arg1 arg2 = myVal arg2 arg1 -- function declaration
myVal = myFunc                     -- value declaration

f $ x = f x                        -- infix declaration
quotedInfix = 42 `mod` 6           -- back-quoted infix operations
compose f g = \x -> f (g x)        -- lambdas / anonymous functions

id :: a -> a                       -- with type signature (currently ignored)
id x = x

-- ($) : (a -> b) -> a -> b        -- coming soon: type signatures for infixes
-- myInfix = ($)                   -- coming soon: partially-applied infixes

data Tree a = Leaf                 -- data type declaration
            | Branch (Tree a) a (Tree a)

sequence a b = seq a b -- Haskell's `seq` statement

-- if-statements
myIf b e1 e2 = if b then e1 else e2
-- indentation sensitive, e.g.
-- if b then e1    if b then e1    if b then    if b then
-- else e2         else e2           e1           e1
--                                 else e2      else
--                                                e2

-- let-statements
-- can be (mutually) recursive, re-orderable
myLet = let f = id
            g = id
        in f g
-- indentation insenstive form:
--   let { f = id
--    ; g = id } in f g

-- case-statements
-- must be exhaustive - or last row can be wildcard (`_`) instead
-- no nested pattern-matches - can only match on constructors applied to variables
isEmptyList l = case l of [] -> True
                          _ -> False

isEmptyTree t =
  case t of
    Leaf -> True
    Branch l a r -> False -- `Branch Leaf a r` is illegal here

true = case bools of (b1, b2) -> b1

-- main :: IO () must be declared
main = do -- force type-checking + compilation of everything in this file
  Ret (
    unit, unitTriple, bools,
    zero, minusOne, fortyTwo, integerOperations, integerComparisons,
    stringLiterals, stringOperations, stringComparisons, listLiterals,
    return, bind, doNotation, arrayOperations,
    exceptions, throwException, exceptionHandler, handleException,
    performFFI, printAction, readArgumentAction,
    myFunc, myVal, quotedInfix, compose, id, sequence,
    myIf, myLet, isEmptyList, isEmptyTree, true
    )
  Ret ()

