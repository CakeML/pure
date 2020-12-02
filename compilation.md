
Sketch of how compilation might be done
=======================================

Language: pure_lang
-------------------

 - co-inductive value type
 - eval is limit at each path
 - `semantics` defined as intepreter for values

Language: pure_lang with alt. semantics
---------------------------------------

  - values of type:

```
Datatype:
 v = Closure string exp
   | Constructor string (exp list)
   | Atom atom
   | Error
   | Diverge
End
```

  - eval is "normal" clocked big-step semantics
  - semantics slightly simpler(?) interpreter

Language: thunk lang
--------------------

 - expressions:

```
Datatype:
 exp = ...
     | Defer exp
     | Force exp -- destroys one Thunk value
End
```

 - call-by-value

```
Datatype:
 v = Closure string exp
   | Constructor string (v list)
   | Thunk exp
   | Atom atom
   | Error
   | Diverge
End
```

 - semantics becomes a program (prog type, contains exp)

```
interp (Bind (print "hello")
     (Lam v (Bind (print " there")
            (Lam v (print "!")))))
-->
Seq (print "hello")
Seq (print " there")
    (print "!")
```

when compiling: standard calling convention: all arguments are thunks
but we can have special calling conventions per function

 - wrapper: all arguments must be thunks
 - worker: some arguments are assumed to not be thunks
   (motivation: workers can call other workers directly)

```
  foo n m = if m < n then bar_worker m else bar_worker n
  bar_worker (m:non-thunk) = m + 1
```

Language: pre-cake: a simplified version of CakeML
--------------------------------------------------

 - call by value
 - simple references, each thunk is compiled to ref ('a + (unit -> 'a))
       + (only support INL / INR references to keep options open for
         compilation to different representations in CakeML)

```
instead of:
  Refv [Block "INL" [val]]
  Refv [Block "INR" [clos]]
have:
  ValueArray [Boolv inl?; payload]
```

 - uses primitive config from pure_lang

Language CakeML source
----------------------

 - references, FFI
 - evaluate, semantics
