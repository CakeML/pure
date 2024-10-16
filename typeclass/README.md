# TypeclassLang

This is a language that support type classes. The file structure is similar to pure.
- compiler/parsing: contains the AST for typeclassLang and defines how the AST is translated to TypeclassLang. The lexer and parser is not done yet.
- typing: It contains all the typing related stuffs
  - `typeclass_types`: We update the datatype for types to allow types like `m a`.
  - `typeclass_kindCheck`: This defines the kinding rules.
  - `typeclass_typing`: This translates TypeclassLang to pureLang. It defines the type elaborating relation and the dictionary construction relation (We split the relation in the original paper into two relations). The ie parameter in the relations is generated from the `class_map` and `inst_list`. It also contains how types and environment is translated when typeclassLang is translated to pureLang.
  - `pure_tcexp_typing`: This defines the typing rules for tcexp. We need to change the typing rules because we need to allow constructors like `MonadDict (forall a. m a -> (a -> m a) -> m a)` to make the type translation proof work.
  - `typeclass_typingProof`: This proves the if the expression in typeclassLang is well-typed, and we can construct the dictionaries, then the translated expression in pureLang is well-typed.
  - `pure_tcexp_typingProof`: This proves the type soundness of the typing relation defined in `pure_tcexp_typing`. The `NestedCase` is still WIP.
  - `typeclass_env_map_impl`: This defines the concreate data structures for classes and instances. It defines some well-formedness conditions. It also defines `by_super`, `by_inst` and `entail` (an implementation of `has_dict`), which should be useful for inferencing.

TODO:
- type soundness proof (`NestedCase` case)
- parsing: lexer, parser and well-formedness check
- concrete implementation of dictionary construction
- type inferencing
- kind inferencing

