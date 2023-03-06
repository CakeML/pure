# Paper correspondences

--------------------------------------------------

## §3 - PureLang

### §3.1 - Features
- Example PureLang code - figure 1: `examples/factorials.hs`

### §3.2 - Formal syntax
- PureLang formal syntax - figure 2 (`op`, `ce`, and `e`)
  - `op` and `e`: `language/pure_expScript.sml`
    (*NB* `e` is `exp` in the formalisation)
  - `ce`: `compiler/backend/languages/pure_cexpScript.sml`
    (*NB* `ce` is `cexp` in the formalisation; the `cepat` type and `NestedCase` constructor in this file are unused currently)
- Desugaring - equation 1, `exp_of`: `exp_of_def` in `compiler/backend/languages/semantics/pureLangScript.sml`

### §3.3 - Semantics
- ITrees in HOL4: in the HOL4 repository, `hol/src/coalgebras/itreeScript.sml`
- Semantics machinery - figure 3 (`wh`, `E`, `A`, `R`)
  - `wh`: `language/pure_evalScript.sml`
  - `E`, `A`, `R`: `language/pure_semanticsScript.sml`
- Clocked evaluation to weak-head normal - `eval^n_wh`: `eval_wh_to_def` in `language/pure_evalScript.sml`
- *Un*clocked evaluation to weak-head normal - equation 2 (`eval_wh`): `eval_wh_def` in `language/pure_evalScript.sml`
- Stateful interpretation - middle of pg. 6 (`(|wh, k, st|)`): `semantics_def` in `language/pure_semanticsScript.sml`
- Final semantics function (`[|e|] : itree E A R`): `itree_of_def` in `language/pure_semanticsScript.sml`

### §3.4 - Equational reasoning
- Definitions of expression relations (*e.g.* applicative bisimulations): `meta-theory/pure_exp_relScript.sml`
- Howe's method: `meta-theory/pure_congruenceScript.sml`
- Alpha-equivalence: `meta-theory/pure_alpha_equivScript.sml`
- Beta-equivalence: `meta-theory/pure_beta_equivScript.sml`
- Expression equivalence coincides with contextual equivalence: `meta-theory/pure_ctxt_equivScript.sml` (using results from `meta-theory/pure_obs_sem_equalScript.sml`)

### §3.5 - Type system
- Typing expressions (including `safeproj`): `typing/pure_tcexpScript.sml`
- Typing rules: `typing/pure_typingScript.sml`
- Type soundness proof: `typing/pure_typingProofScript`

--------------------------------------------------

## §4 - Compiler front end

Many files are found in `compiler/backend` - elided with `...` below.

### §4.1 - Parsing expression grammar (PEG) parsing
- TODO Michael

### §4.2 - PureLang
- Binding group analysis: `.../passes/pure_letrec_cexpScript.sml`
  - Including pseudo-topological sort in the HOL4 repository: `hol/examples/algorithms/topological_sortScript.sml`
  - Core soundness proof `.../passes/proofs/pure_letrecProofScript.sml`

### §4.3 - Constraint-based type inference
- Inference algorithm: `typing/pure_inferenceScript.sml`
- Top declarative inference rules: `typing/pure_inference_modelScript.sml`
- Core soundness proof: `typing/pure_inferenceProofScript.sml`

### §4.4 - Demand analysis
- TODO Samuel
- Formalisation of demands: `meta-theory/pure_demandScript.sml`
- Demand analysis algorithm: `.../passes/pure_demands_analysisScript.sml`
- Core soundness proof: `.../passes/proofs/pure_demands_analysisProofScript.sml`

--------------------------------------------------

## §5 - Compiler back end

Most files are found in `compiler/backend` - elided with `...` below.

### §5.2 - ThunkLang
- Compiler expressions: `.../languages/thunk_cexpScript.sml`
- Semantics expressions: `.../languages/semantics/thunkLangScript.sml`
- Semantics: `.../languages/semantics/thunk_semanticsScript.sml`
- Compilation from PureLang to ThunkLang: `.../passes/pure_to_thunkScript.sml`
  - Core soundness proofs: `.../passes/proofs/{pure_to_thunk,thunk}*Script.sml`

### §5.2 - EnvLang
- Compiler expressions: `.../languages/envLang_cexpScript.sml`
- Semantics expressions: `.../languages/semantics/envLangScript.sml`
- Semantics: `.../languages/semantics/env_semanticsScript.sml`
- Compilation from ThunkLang to EnvLang: `.../passes/thunk_to_envScript.sml`
  - Core soundness proofs: `.../passes/proofs/thunk_to_env*Script.sml`

### §5.2 - StateLang
- Compiler expressions: `.../languages/state_cexpScript.sml`
- Semantics expressions + semantics: `.../languages/semantics/stateLangScript.sml`
- Compilation from EnvLang to StateLang: `.../passes/env_to_stateScript.sml`
  - Core soundness proofs: `.../passes/proofs/thunk_to_env*Script.sml`
- StateLang optimisation pass: `.../passes/state_app_unitScript.sml`
  - Core soundness proofs: `.../passes/proofs/state_app_unit*Script.sml`
- Compilation from StateLang to CakeML: `.../passes/state_to_cakeScript.sml` and `.../passes/state_app_unitScript.sml`
  - Core soundness proofs: `.../passes/proofs/state_to_cakeProofScript.sml` and `.../passes/proofs/state_app_unit*Script.sml`

--------------------------------------------------

## §6 - Targeting CakeML

Many files below are in the CakeML repository.

- CakeML CESK semantics: `cakeml/semantics/alt_semantics/smallStepScript.sml`
- CakeML ITree semantics: `cakeml/semantics/alt_semantics/itree_semanticsScript.sml`
- Equivalence proofs: `cakeml/semantics/alt_semantics/proofs`
  - Particularly `alt_semanticsScript.sml`, `itree_semantics*Script.sml`
- ITree machine semantics: `cakeml/compiler/backend/semantics/target_itreeSemScript.sml`
- ITree compiler correctness (middle of pg. 18): `cakeml/compiler/backend/proofs/backend_itreeProofScript.sml`

- Compiler correctness (theorem 1): `compiler/proofs/pure_compilerProofScript.sml`
  (*NB* in the PureCake repository)