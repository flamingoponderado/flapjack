/-
FINITE-SUPPORT CARRIER PROGRAM EVALUATION (flapjack-6yq / flapjack-qj5).

The exact `evaluate_def` evaluator `evalPanSemRecursiveCallContextHOLExact`
(`TotalEvalExact.lean`) quantifies over `PanSemStateExact`, whose
`locals`/`globals`/`code`/`eshapes` are unrestricted `MlS → Option _` functions.
HOL `panSem$state` instead keeps those fields as finite maps (`varname |-> 'a v`,
`|->`), so the evaluator is faithful only on the finite-support subcarrier.

`PanSemStateFiniteExact.evaluateHOLFinite` (in the carrier module
`StateExactFiniteMap.lean`) is the provisional state-level projection of the
direct, clause-for-clause finite context evaluator
`evalPanSemRecursiveCallFiniteContext`.  It currently keeps the outer `Option`
assembly marker (proved always `some` by `evaluateHOLFinite_ne_none`), so a clause returns `some (result, state)` rather than HOL
`evaluate_def`'s bare `result option × state` pair.  The finite
context threads `memaddrsDecidable`/`shMemaddrsDecidable` (bead `flapjack-6yq`)
so the recursive clauses typecheck over literal record updates.

This module exposes the clause surface of `evaluateHOLFinite`, clause by clause,
as the source evidence for the `evaluate_def` port.  Exposed so far:
`Skip` / `Break` / `Continue`, the `Seq` (three outcomes) and `If`
(then/else on a word condition) clauses, the `Dec` and `While` clauses, the
`Call` / `DecCall` argument-list and code-lookup short circuits plus the
clock-exhaustion (`TimeOut`, empty locals) branches, and the
`Return` / `Raise` / `ShMemLoad` / `ShMemStore` clauses.  The `Call` / `DecCall`
returned and exception outcome branches are exposed by the projection theorems
`evalPanSemRecursiveCallFiniteContext_call_projection` and
`..._decCall_projection`, which relate the finite context evaluator to the broad
exact one over `toExact`. The general `fun_induction` projection equivalence
over every constructor is now proved
(`evalPanSemRecursiveCallFiniteContext_projection`, commit de0d2ff1e,
`flapjack-6yq`). The 21-clause/carrier source-audit slice `flapjack-6yq.1` is
coordinator-reviewed and closed. Coordinator review identified that HOL's
`evaluate_def` at line 780 is a theorem containing the 21 clause equations,
not a function definition. The function-shaped `evaluateHOLFiniteState` tag
was withdrawn; `flapjack-qj5` tracks the faithful equation theorem. No HOL
claim is made by the evaluator infrastructure here.

The staged `evaluate_def` case proofs are reviewed against the source
`Definition evaluate_def` at `panSemScript.sml:556` when their equations retain
operations such as `fix_clock`; line 780 is the separate `REWRITE_RULE
[fix_clock_evaluate]` theorem restatement and may have a different equation
shape. The case theorems do not assemble the full conjunction: the faithful
21-clause theorem remains tracked by `flapjack-qj5.9`.

The older delegating adapter `evaluateHOLFiniteViaExact` (and its
`evalPanSemRecursiveCallHOLFinite_of_broad` / `evaluateHOLFiniteViaExact_of_broad`
translation lemmas) remains as untagged Flapjack-specific infrastructure.

Source audit (Luna A, 2026-09-27), compared against the complete HOL
`evaluate_def` block at `panSemScript.sml:556-761`:

* `Skip`, `Break`, `Continue`, and `Annot` preserve the state and return the
  corresponding HOL result; `Tick` distinguishes zero clock (`TimeOut` and
  empty locals) from decrement-and-`NONE`.
* `Dec` evaluates the initializer, checks `shape_of` equality, installs the
  value for the body, and restores the previous local with `res_var`.
  `Assign`, `Primitive`, `Store`, `Store32`, and `StoreByte` retain the source
  error branches and update only the HOL-selected variable or memory field.
* `ShMemLoad` and `ShMemStore` use the source helpers, including value-kind,
  lookup, and memory-domain failures. `Return` and `Raise` retain the shape
  size bound, exception-shape lookup, and empty-locals behavior.
* `Seq` fixes the first result's clock and evaluates the second command only
  for `NONE`; `If` uses the source zero/nonzero word split. `While` checks the
  zero clock before the body, decrements before body evaluation, fixes its
  result clock, and recurs only for `NONE`/`Continue`; `Break` becomes `NONE`.
* `Call` and `DecCall` preserve argument evaluation and exact code lookup,
  zero-clock timeout, callee-local entry, fixed-clock body outcome split,
  return-shape and validity checks, exception-handler lookup/validation, and
  local restoration. `DecCall` additionally checks both declared return
  shapes, runs its continuation with the result binding, then restores the
  prior result local. The focused Call/DecCall equations and projection proofs
  cover the outcome-specific branches.
* `ExtCall` retains all four expression checks, both byte-array reads, FFI
  final/return branches, and the source memory/FFI updates.

The exact data carriers are `ProgHOL`/`ExpHOL`/`ShapeHOL` and
`PanSemStateFiniteExact`: words retain the source width, identifiers use
`MlS`, and the four finite maps use the reviewed `HolFiniteMapExact`
representation recorded by the state's qualifier and roundtrip witness.
`shapeEqHOL_eq_true` establishes the Boolean shape comparison used by the
evaluator. The finite-to-broad theorem below is a kernel-checked projection
for every constructor; the state-level wrapper's `evaluateHOLFiniteState_eq_getD`
bridge removes the assembly marker without changing the result/state pair.
No clause or carrier mismatch was found. Coordinator review found a declaration
shape mismatch: HOL `evaluate_def` is the line-780 equation theorem, whereas
`evaluateHOLFiniteState` is a Lean function definition. Its HOL tag is
withdrawn; `flapjack-qj5` tracks the equation theorem. The source-audit
prerequisite `flapjack-6yq.1` is coordinator-reviewed and closed.

The module also carries the per-constructor projection equivalence to the broad
exact evaluator (`flapjack-6yq`): `..._skip_projection` / `_break_projection` /
`_continue_projection` / `_annot_projection` and the `assign` / `primitive` /
`store` / `store32` / `storeByte` / `extCall` / `tick` / `return` / `raise` /
`shMemLoad` / `shMemStore` projections show that mapping the finite evaluator's
result through `state.toExact` agrees with `...ContextHOLExact`. Recursive
`Dec`, `Seq`, `If`, and `While` have conditional projection lemmas using their
recursive hypotheses. `Call` and `DecCall` projection lemmas and the assembling
66-case induction `evalPanSemRecursiveCallFiniteContext_projection` (commit
de0d2ff1e) are all proved, so the finite-to-broad evaluator equality over every
constructor is complete; `flapjack-qj5` tracks the matching conjunction of
state-level equations and its source-reviewed HOL tag.
-/
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack

open Flapjack.Pancake.PanLang (ProgHOL ExpHOL MlS ShapeHOL)

namespace PanSemStateFiniteExact

/-- Generic translation: given the broad exact evaluator's result on `program`,
    the finite recursive evaluator returns the same result with the post-state
    rebuilt through the canonical finite-support carrier. -/
theorem evalPanSemRecursiveCallHOLFinite_of_broad {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
    (hb : evalPanSemRecursiveCallContextHOLExact program
        { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
      some output) :
    evalPanSemRecursiveCallHOLFinite state program =
      some (output.1, ofExact output.2.state
        (evalPanSemRecursiveCallContextHOLExact_finiteSupport program
          { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }
          state.toExact_finiteSupport output hb)) := by
  rw [evalPanSemRecursiveCallHOLFinite.eq_def]
  dsimp only
  split
  · rename_i hres
    rw [hb] at hres
    simp at hres
  · rename_i pair hres
    rw [hb] at hres
    simp only [Option.some.injEq] at hres
    subst hres
    rfl

/-- Generic translation for the finite adapter: given the broad exact
    evaluator's result on `program`, `evaluateHOLFiniteViaExact` returns the same
    (`result option × state`) pair with the post-state rebuilt through the
    canonical finite-support carrier. -/
theorem evaluateHOLFiniteViaExact_of_broad {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
    (hb : evalPanSemRecursiveCallContextHOLExact program
        { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
      some output) :
    evaluateHOLFiniteViaExact state program =
      (output.1, ofExact output.2.state
        (evalPanSemRecursiveCallContextHOLExact_finiteSupport program
          { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }
          state.toExact_finiteSupport output hb)) := by
  have hw := evalPanSemRecursiveCallHOLFinite_of_broad state program output hb
  unfold evaluateHOLFiniteViaExact
  dsimp only
  rw [hw]

/-- HOL `evaluate_def` `Skip` clause: `evaluate (Skip, s) = (NONE, s)`. -/
@[simp] theorem evaluateHOLFiniteViaExact_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFiniteViaExact state (.skip : ProgHOL width) = (none, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.skip : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (none, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFiniteViaExact_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Break` clause: `evaluate (Break, s) = (SOME Break, s)`. -/
@[simp] theorem evaluateHOLFiniteViaExact_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFiniteViaExact state (.break : ProgHOL width) = (some .break, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.break : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (some .break, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFiniteViaExact_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Continue` clause: `evaluate (Continue, s) = (SOME Continue, s)`. -/
@[simp] theorem evaluateHOLFiniteViaExact_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFiniteViaExact state (.continue : ProgHOL width) = (some .continue, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.continue : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (some .continue, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFiniteViaExact_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Skip` clause over the direct finite context evaluator. -/
@[simp] theorem evaluateHOLFinite_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.skip : ProgHOL width) = some (none, state) := by
  unfold evaluateHOLFinite
  simp [evalPanSemRecursiveCallFiniteContext]

/-- HOL `evaluate_def` `Break` clause over the direct finite context evaluator. -/
@[simp] theorem evaluateHOLFinite_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.break : ProgHOL width) = some (some .break, state) := by
  unfold evaluateHOLFinite
  simp [evalPanSemRecursiveCallFiniteContext]

/-- HOL `evaluate_def` `Continue` clause over the direct finite context evaluator. -/
@[simp] theorem evaluateHOLFinite_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.continue : ProgHOL width) = some (some .continue, state) := by
  unfold evaluateHOLFinite
  simp [evalPanSemRecursiveCallFiniteContext]

/-- HOL `evaluate_def` `Seq` clause: if the first command returns `NONE`
    (a short-circuit `Break`/`Continue`/`Return`-less normal prefix), the whole
    sequence has no result. -/
theorem evalPanSemRecursiveCallFiniteContext_seq_none {width : Nat} {σ : Type} [NeZero width]
    (first second : ProgHOL width) (context : FiniteEvalContext width σ)
    (hfirst : evalPanSemRecursiveCallFiniteContext first context = none) :
    evalPanSemRecursiveCallFiniteContext (.seq first second) context = none := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hfirst]

/-- HOL `evaluate_def` `Seq` clause: a normal (`NONE`) first result runs the
    second command from the clock-fixed continuation state. -/
theorem evalPanSemRecursiveCallFiniteContext_seq_some_none {width : Nat} {σ : Type}
    [NeZero width]
    (first second : ProgHOL width) (context : FiniteEvalContext width σ)
    (firstContext : FiniteEvalContext width σ)
    (hfirst : evalPanSemRecursiveCallFiniteContext first context = some (none, firstContext)) :
    evalPanSemRecursiveCallFiniteContext (.seq first second) context =
      evalPanSemRecursiveCallFiniteContext second
        (firstContext.withState
          (fixClockHOLFinite context.state
            ((none : Option (PanSemResultExact width)), firstContext.state)).2 rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hfirst]

/-- HOL `evaluate_def` `Seq` clause: a non-`NONE` first result short-circuits the
    sequence at the clock-fixed continuation state. -/
theorem evalPanSemRecursiveCallFiniteContext_seq_some_some {width : Nat} {σ : Type}
    [NeZero width]
    (first second : ProgHOL width) (context : FiniteEvalContext width σ)
    (firstContext : FiniteEvalContext width σ)
    (firstResult : PanSemResultExact width)
    (hfirst : evalPanSemRecursiveCallFiniteContext first context =
      some (some firstResult, firstContext)) :
    evalPanSemRecursiveCallFiniteContext (.seq first second) context =
      some (some firstResult,
        firstContext.withState
          (fixClockHOLFinite context.state (some firstResult, firstContext.state)).2 rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hfirst]

/-- HOL `evaluate_def` `If` clause, non-zero branch: a word-valued true condition
    selects the then-branch. -/
theorem evalPanSemRecursiveCallFiniteContext_ite_then {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (value : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word value)))
    (hne : (value != 0) = true) :
    evalPanSemRecursiveCallFiniteContext (.ite condition thenBranch elseBranch) context =
      evalPanSemRecursiveCallFiniteContext thenBranch context := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_pos hne]

/-- HOL `evaluate_def` `If` clause, zero branch: a word-valued false condition
    selects the else-branch. -/
theorem evalPanSemRecursiveCallFiniteContext_ite_else {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (value : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word value)))
    (hz : (value != 0) = false) :
    evalPanSemRecursiveCallFiniteContext (.ite condition thenBranch elseBranch) context =
      evalPanSemRecursiveCallFiniteContext elseBranch context := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_neg (by rw [hz]; decide)]

/-- HOL `evaluate_def` `Dec` clause: an initializer that fails to evaluate yields
    the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_dec_init_none {width : Nat} {σ : Type}
    [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (hinit : evalHOLFinite context.state (h := context.memaddrsDecidable) initializer = none) :
    evalPanSemRecursiveCallFiniteContext (.dec name shape initializer body) context =
      some (some .error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hinit]

/-- HOL `evaluate_def` `Dec` clause: an initializer whose value does not match the
    declared shape yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_dec_shape_false {width : Nat} {σ : Type}
    [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ) (value : ValueHOL width)
    (hinit : evalHOLFinite context.state (h := context.memaddrsDecidable) initializer =
      some value)
    (hshape : shapeEqHOL shape (shapeOfHOLExact value) = false) :
    evalPanSemRecursiveCallFiniteContext (.dec name shape initializer body) context =
      some (some .error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hinit]
  dsimp only
  rw [if_neg (by rw [hshape]; decide)]

/-- HOL `evaluate_def` `Dec` clause: once the initializer matches the shape, the
    recursive body result is restored by `res_var` on the local binding. -/
theorem evalPanSemRecursiveCallFiniteContext_dec_body_some {width : Nat} {σ : Type}
    [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ) (value : ValueHOL width)
    (result : Option (PanSemResultExact width)) (postContext : FiniteEvalContext width σ)
    (hinit : evalHOLFinite context.state (h := context.memaddrsDecidable) initializer =
      some value)
    (hshape : shapeEqHOL shape (shapeOfHOLExact value) = true)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (context.withState (setVarHOLFinite name value context.state) rfl rfl) =
        some (result, postContext)) :
    evalPanSemRecursiveCallFiniteContext (.dec name shape initializer body) context =
      some (result, postContext.withState
        { postContext.state with
          locals := HolFiniteMapExact.resVarEq postContext.state.locals
            (name, context.state.locals.lookup name) } rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hinit]
  dsimp only
  rw [if_pos hshape]
  rw [hbody]

/-- HOL `evaluate_def` `While` clause: a zero-valued condition exits the loop with
    the `NONE` result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_while_word_zero {width : Nat} {σ : Type}
    [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (word : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word word)))
    (hzero : ¬ word ≠ 0) :
    evalPanSemRecursiveCallFiniteContext (.while condition body) context =
      some (none, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_neg hzero]

/-- HOL `evaluate_def` `While` clause: on an exhausted clock the loop returns
    `TimeOut` with emptied locals. -/
theorem evalPanSemRecursiveCallFiniteContext_while_clock_zero {width : Nat} {σ : Type}
    [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (word : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word word)))
    (hw : word ≠ 0) (hclock : context.state.clock = 0) :
    evalPanSemRecursiveCallFiniteContext (.while condition body) context =
      some (some .timeOut,
        context.withState (emptyLocalsHOLFinite context.state) rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_pos hw]
  rw [if_pos hclock]

/-- HOL `evaluate_def` `While` clause: a `Continue` (or `NONE`) body result
    re-enters the loop at the clock-fixed continuation state. -/
theorem evalPanSemRecursiveCallFiniteContext_while_body_continue {width : Nat} {σ : Type}
    [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (word : BitVec width) (bodyContext : FiniteEvalContext width σ)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word word)))
    (hw : word ≠ 0) (hclock : ¬ context.state.clock = 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (context.withState (decClockHOLFinite (width := width) (σ := σ) context.state) rfl rfl) =
        some (some PanSemResultExact.continue, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext (.while condition body) context =
      evalPanSemRecursiveCallFiniteContext (.while condition body)
        (bodyContext.withState (fixClockHOLFinite (width := width) (σ := σ) (decClockHOLFinite (width := width) (σ := σ) context.state)
          ((some PanSemResultExact.continue, bodyContext.state) : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)).2 rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_pos hw]
  rw [if_neg hclock]
  rw [hbody]

/-- HOL `evaluate_def` `While` clause: a `Break` body result exits the loop with
    the `NONE` result at the clock-fixed continuation state. -/
theorem evalPanSemRecursiveCallFiniteContext_while_body_break {width : Nat} {σ : Type}
    [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (word : BitVec width) (bodyContext : FiniteEvalContext width σ)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word word)))
    (hw : word ≠ 0) (hclock : ¬ context.state.clock = 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (context.withState (decClockHOLFinite (width := width) (σ := σ) context.state) rfl rfl) =
        some (some PanSemResultExact.break, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext (.while condition body) context =
      some (none, bodyContext.withState (fixClockHOLFinite (width := width) (σ := σ) (decClockHOLFinite (width := width) (σ := σ) context.state)
        ((some PanSemResultExact.break, bodyContext.state) : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)).2 rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_pos hw]
  rw [if_neg hclock]
  rw [hbody]

/-- HOL `evaluate_def` `Call` clause short circuit: an argument list that fails
    to evaluate yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_call_args_none {width : Nat} {σ : Type}
    [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (context : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments = none) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some PanSemResultExact.error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]

/-- HOL `evaluate_def` `Call` clause short circuit: a function whose code lookup
    fails yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_call_lookup_none {width : Nat} {σ : Type}
    [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (context : FiniteEvalContext width σ)
    (values : List (ValueHOL width))
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments =
      some values)
    (hlookupNone : lookupCodeHOLFinite context.state.code.lookup function values = none) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some PanSemResultExact.error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [lookupCodeCanonicalHOL, hlookupNone]

/-- HOL `evaluate_def` `DecCall` clause short circuit: an argument list that fails
    to evaluate yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_args_none {width : Nat} {σ : Type}
    [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments = none) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some PanSemResultExact.error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]

/-- HOL `evaluate_def` `DecCall` clause short circuit: a function whose code
    lookup fails yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_lookup_none {width : Nat} {σ : Type}
    [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments =
      some values)
    (hlookupNone : lookupCodeHOLFinite context.state.code.lookup function values = none) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some PanSemResultExact.error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [lookupCodeCanonicalHOL, hlookupNone]

/-- HOL `evaluate_def` `Call` clause clock-exhaustion branch: when the caller's
    clock is exhausted the call returns `TimeOut` with empty locals. -/
theorem evalPanSemRecursiveCallFiniteContext_call_clock_zero {width : Nat} {σ : Type}
    [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (context : FiniteEvalContext width σ)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments =
      some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock = 0) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some .timeOut, FiniteEvalContext.emptyLocalsContextHOLFinite context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [lookupCodeCanonicalHOL, hlookup]
  dsimp only
  rw [if_pos hclock]

/-- HOL `evaluate_def` `DecCall` clause clock-exhaustion branch: when the caller's
    clock is exhausted the call returns `TimeOut` with empty locals. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_clock_zero {width : Nat} {σ : Type}
    [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments =
      some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock = 0) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some .timeOut, FiniteEvalContext.emptyLocalsContextHOLFinite context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [lookupCodeCanonicalHOL, hlookup]
  dsimp only
  rw [if_pos hclock]

/-- Source-reviewed HOL `Call` return side condition
    (`panSemScript.sml:657-693`): after successful argument evaluation and code
    lookup, a nonzero-clock body result is fixed against the decremented call
    entry state. If its returned value's shape differs from the looked-up
    `return_sh`, HOL returns `Error` with that fixed post-state before
    considering `caltyp`. It directly checks this clause side condition in the
    finite `Call` evaluator. The adjacent source audit compared both recursive
    clauses (`panSemScript.sml:657-729`): each evaluates `OPT_MMAP (eval s)`
    before `lookup_code`, returns `Error` on either failure at the caller
    state, returns `TimeOut` with `empty_locals s` at clock zero, and otherwise
    evaluates the callee from `dec_clock s` with `newlocals` before applying
    `fix_clock` to its result/state. `Call` maps body `NONE`/`Break`/`Continue`
    to `Error`; its return branches are `caltyp = NONE` (return with empty
    locals), `SOME (NONE, _)` (return `NONE` with caller locals), and
    `SOME (SOME (kind, name), _)` (validate against the caller state, then
    `set_kvar` on the fixed state with caller locals). Exceptions propagate
    with empty locals when unhandled or unmatched; a matching handler requires
    an `eshapes` lookup, shape equality, and local validity, then runs from the
    fixed state with caller locals. Failed handler checks return `Error` at the
    fixed state. The remaining `Call` body outcomes are preserved with empty
    locals. `DecCall` checks both declared `shape` and `return_sh` before its
    continuation; on success it starts that continuation with caller locals
    and the returned value bound, then restores the prior result-name binding
    with `res_var`. Its remaining body outcomes are preserved with empty
    locals. The finite
    code uses `callEntryStateHOLFinite`, `callFixedContextHOLFinite`,
    `handlerStateHOLFinite`, and `callContinuationContextHOLFinite` for the
    corresponding transitions. Existing full recursive projection theorems
    prove finite/broad exact evaluator correspondence. These focused clause
    facts are not separate HOL declarations and do not add a tag to the whole
    `evaluate_def` definition. The direct source rows are in
    `scripts/hol-probes/pan_sem_call_return_shape_probe.out`; the production
    regression is `Flapjack.Test.PanSemCallErrorExactParity`. -/
theorem evalPanSemRecursiveCallFiniteContext_call_return_shape_mismatch
    {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width)
    (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.returned value), bodyContext))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = false) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some (.returned value)) bodyContext) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs]
  rw [lookupCodeCanonicalHOL, hlookup]
  simp only [if_neg hclock, hbody]
  have hshapeNe : ¬ shapeEqHOL (shapeOfHOLExact value) returnShape = true := by
    rw [hshape]
    simp
  rw [if_neg hshapeNe]

/-- HOL `evaluate_def` Call body `NONE` branch (`panSemScript.sml:668`): a callee
    that falls through with no result maps to `Error` at the clock-fixed callee
    state. Untagged clause equation; it does not claim the whole evaluator. -/
theorem evalPanSemRecursiveCallFiniteContext_call_body_none
    {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (none, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          none bodyContext) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]

/-- HOL `evaluate_def` Call body `Break` branch (`panSemScript.sml:669`): a callee
    that breaks maps to `Error` at the clock-fixed callee state. Untagged clause
    equation; it does not claim the whole evaluator. -/
theorem evalPanSemRecursiveCallFiniteContext_call_body_break
    {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some .break, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some .break) bodyContext) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]

/-- HOL `evaluate_def` Call body `Continue` branch (`panSemScript.sml:670`): a
    callee that continues maps to `Error` at the clock-fixed callee state.
    Untagged clause equation; it does not claim the whole evaluator. -/
theorem evalPanSemRecursiveCallFiniteContext_call_body_continue
    {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some .continue, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some .continue) bodyContext) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]

/-- HOL `evaluate_def` Call matched-exception branch
    (`panSemScript.sml:682-688`): after the body yields an exception whose id
    matches the handler, the caller's finite `eshapes` lookup supplies its
    declared shape, and both the exception shape and local target are valid,
    the handler runs from the fixed callee state with the caller's locals and
    the exception value bound. These are exactly the branch selectors in HOL;
    this untagged clause equation does not claim the whole evaluator. -/
theorem evalPanSemRecursiveCallFiniteContext_call_matched_exception_handler
    {width : Nat} {σ : Type} [NeZero width]
    (returnInfo : Option (VarKind × MlS))
    (handlerId handlerVar function : MlS) (handlerProgram body : ProgHOL width)
    (arguments : List (ExpHOL width)) (context : FiniteEvalContext width σ)
    (values : List (ValueHOL width)) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width)
    (bodyContext : FiniteEvalContext width σ) (declaredShape : ShapeHOL)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
        some (some (.exception handlerId value), bodyContext))
    (hshape : context.state.eshapes.lookup handlerId = some declaredShape)
    (hshapeEq : shapeEqHOL (shapeOfHOLExact value) declaredShape = true)
    (hvalid : isValidValueHOLExact context.state.toExact VarKind.local handlerVar value = true) :
    evalPanSemRecursiveCallFiniteContext
        (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram)))
          function arguments) context =
      let fixedContext := callFixedContextHOLFinite
        (callEntryStateHOLFinite context.state callee)
        (some (.exception handlerId value)) bodyContext
    evalPanSemRecursiveCallFiniteContext handlerProgram
        (callContinuationContextHOLFinite context fixedContext handlerVar value) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs]
  rw [lookupCodeCanonicalHOL, hlookup]
  simp only [if_neg hclock]
  rw [hbody]
  simp [hshape, hshapeEq, hvalid]

/-- HOL `evaluate_def` Call returned-value branch with `caltyp = NONE`
    (`panSemScript.sml:673-674`): the returned value is preserved at empty
    locals of the clock-fixed callee state. Untagged clause equation. -/
theorem evalPanSemRecursiveCallFiniteContext_call_return_none
    {width : Nat} {σ : Type} [NeZero width]
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.returned value), bodyContext))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true) :
    evalPanSemRecursiveCallFiniteContext (.call none function arguments) context =
      some (some (.returned value),
        FiniteEvalContext.emptyLocalsContextHOLFinite
          (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
            (some (.returned value)) bodyContext)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]
  simp [hshape]

/-- HOL `evaluate_def` Call returned-value branch with `caltyp = SOME (NONE, _)`
    (`panSemScript.sml:675`): the call continues with the caller's locals.
    Untagged clause equation. -/
theorem evalPanSemRecursiveCallFiniteContext_call_return_caller_locals
    {width : Nat} {σ : Type} [NeZero width]
    (handler : Option (MlS × MlS × ProgHOL width))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.returned value), bodyContext))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true) :
    evalPanSemRecursiveCallFiniteContext
        (.call (some (none, handler)) function arguments) context =
      some (none,
        callRestoreLocalsContextHOLFinite context
          (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
            (some (.returned value)) bodyContext)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]
  simp [hshape]

/-- HOL `evaluate_def` Call returned-value branch with a wrapped result and a
    valid target (`panSemScript.sml:676-680`): `set_kvar` installs the returned
    value over the caller's locals. Untagged clause equation. -/
theorem evalPanSemRecursiveCallFiniteContext_call_return_set_kvar
    {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS)
    (handler : Option (MlS × MlS × ProgHOL width))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.returned value), bodyContext))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true)
    (hvalid : isValidValueHOLExact context.state.toExact kind name value = true) :
    evalPanSemRecursiveCallFiniteContext
        (.call (some (some (kind, name), handler)) function arguments) context =
      some (none,
        callSetKvarContextHOLFinite context
          (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
            (some (.returned value)) bodyContext) kind name value) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]
  simp [hshape, hvalid]

/-- HOL `evaluate_def` Call returned-value branch with a wrapped result whose
    target is invalid (`panSemScript.sml:680-681`): `Error` at the clock-fixed
    callee state. Untagged clause equation. -/
theorem evalPanSemRecursiveCallFiniteContext_call_return_kvar_invalid
    {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS)
    (handler : Option (MlS × MlS × ProgHOL width))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.returned value), bodyContext))
    (hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true)
    (hinvalid : isValidValueHOLExact context.state.toExact kind name value = false) :
    evalPanSemRecursiveCallFiniteContext
        (.call (some (some (kind, name), handler)) function arguments) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some (.returned value)) bodyContext) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]
  simp [hshape, hinvalid]
/-- HOL `evaluate_def` Call unhandled-exception branch with `caltyp = NONE`
    (`panSemScript.sml:683-684`): the exception propagates at empty locals.
    Untagged clause equation. -/
theorem evalPanSemRecursiveCallFiniteContext_call_exception_unhandled
    {width : Nat} {σ : Type} [NeZero width]
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (exceptionId : MlS) (value : ValueHOL width)
    (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.exception exceptionId value), bodyContext)) :
    evalPanSemRecursiveCallFiniteContext (.call none function arguments) context =
      some (some (.exception exceptionId value),
        FiniteEvalContext.emptyLocalsContextHOLFinite
          (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
            (some (.exception exceptionId value)) bodyContext)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]

/-- HOL `evaluate_def` Call unhandled-exception branch with
    `caltyp = SOME (_, NONE)` (`panSemScript.sml:685-686`): the exception
    propagates at empty locals. Untagged clause equation. -/
theorem evalPanSemRecursiveCallFiniteContext_call_exception_no_handler
    {width : Nat} {σ : Type} [NeZero width]
    (returnInfo : Option (VarKind × MlS))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (exceptionId : MlS) (value : ValueHOL width)
    (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.exception exceptionId value), bodyContext)) :
    evalPanSemRecursiveCallFiniteContext
        (.call (some (returnInfo, none)) function arguments) context =
      some (some (.exception exceptionId value),
        FiniteEvalContext.emptyLocalsContextHOLFinite
          (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
            (some (.exception exceptionId value)) bodyContext)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]

/-- HOL `evaluate_def` Call exception branch with a non-matching handler
    (`panSemScript.sml:689-690`): the exception propagates at empty locals.
    Untagged clause equation. -/
theorem evalPanSemRecursiveCallFiniteContext_call_exception_mismatch
    {width : Nat} {σ : Type} [NeZero width]
    (returnInfo : Option (VarKind × MlS)) (handlerId handlerVar : MlS)
    (handlerProgram : ProgHOL width)
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (exceptionId : MlS) (value : ValueHOL width)
    (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.exception exceptionId value), bodyContext))
    (hne : ¬ exceptionId = handlerId) :
    evalPanSemRecursiveCallFiniteContext
        (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram)))
          function arguments) context =
      some (some (.exception exceptionId value),
        FiniteEvalContext.emptyLocalsContextHOLFinite
          (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
            (some (.exception exceptionId value)) bodyContext)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]
  simp only [if_neg hne]

/-- HOL `evaluate_def` Call exception branch whose matching handler has no
    declared shape (`panSemScript.sml:690-691`): `Error` at the clock-fixed
    callee state. Untagged clause equation. -/
theorem evalPanSemRecursiveCallFiniteContext_call_exception_missing_shape
    {width : Nat} {σ : Type} [NeZero width]
    (returnInfo : Option (VarKind × MlS)) (handlerId handlerVar : MlS)
    (handlerProgram : ProgHOL width)
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (exceptionId : MlS) (value : ValueHOL width)
    (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.exception exceptionId value), bodyContext))
    (heq : exceptionId = handlerId)
    (hshapeNone : context.state.eshapes.lookup exceptionId = none) :
    evalPanSemRecursiveCallFiniteContext
        (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram)))
          function arguments) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some (.exception exceptionId value)) bodyContext) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]
  subst heq
  simp [hshapeNone]

/-- HOL `evaluate_def` Call exception branch whose matching handler fails the
    shape or local-validity check (`panSemScript.sml:691-692`): `Error` at the
    clock-fixed callee state. Untagged clause equation. -/
theorem evalPanSemRecursiveCallFiniteContext_call_exception_invalid
    {width : Nat} {σ : Type} [NeZero width]
    (returnInfo : Option (VarKind × MlS)) (handlerId handlerVar : MlS)
    (handlerProgram : ProgHOL width) (declaredShape : ShapeHOL)
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (exceptionId : MlS) (value : ValueHOL width)
    (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.exception exceptionId value), bodyContext))
    (heq : exceptionId = handlerId)
    (hshapeSome : context.state.eshapes.lookup exceptionId = some declaredShape)
    (hinvalid : (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
      isValidValueHOLExact context.state.toExact VarKind.local handlerVar value) = false) :
    evalPanSemRecursiveCallFiniteContext
        (.call (some (returnInfo, some (handlerId, handlerVar, handlerProgram)))
          function arguments) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some (.exception exceptionId value)) bodyContext) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [hargs, hlookup, if_neg hclock, hbody]
  subst heq
  simp [hshapeSome, hinvalid]
/-- Source-reviewed HOL `DecCall` return-shape side conditions
    (`panSemScript.sml:694-729`). Either mismatch (against the declaration's
    `shape` or the looked-up `return_sh`) returns `Error` at the clock-fixed
    callee state and skips the continuation. Direct original HOL rows are in
    `scripts/hol-probes/pan_sem_call_return_shape_probe.out`; the generic
    finite-context theorem pins both predicate checks without assuming a
    return value's invariant. This isolates one clause of `evaluate_def` and
    is not an independent HOL declaration, so it has no `@[hol]` tag. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_return_shape_mismatch
    {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width)
    (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (context.withState (callEntryStateHOLFinite context.state callee) rfl rfl) =
      some (some (.returned value), bodyContext))
    (hshape : shapeEqHOL (shapeOfHOLExact value) shape = false ∨
      shapeEqHOL (shapeOfHOLExact value) returnShape = false) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some (.returned value)) bodyContext) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_6]
  simp only [hargs]
  rw [lookupCodeCanonicalHOL, hlookup]
  simp only [if_neg hclock, hbody]
  rcases hshape with hdecl | hreturn
  · have hshapeNe : ¬ (shapeEqHOL (shapeOfHOLExact value) shape &&
        shapeEqHOL (shapeOfHOLExact value) returnShape) = true := by
      simp [hdecl]
    rw [if_neg hshapeNe]
  · have hshapeNe : ¬ (shapeEqHOL (shapeOfHOLExact value) shape &&
        shapeEqHOL (shapeOfHOLExact value) returnShape) = true := by
      simp [hreturn]
    rw [if_neg hshapeNe]

/-- FLAPJACK-SPECIFIC context normalizer (no standalone HOL declaration): a
    generated recursive-call context is interchangeable with the named
    DecCall entry context once their state projections agree. The proof
    arguments stored in the dependent address deciders are deliberately left
    opaque; `evalPanSemRecursiveCallFiniteContext_state_eq` only needs state
    equality. -/
theorem evalPanSemRecursiveCallFiniteContext_callEntryContext_state_normalize
    {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context generatedContext : FiniteEvalContext width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width))
    (hstate : generatedContext.state = callEntryStateHOLFinite context.state callee) :
    evalPanSemRecursiveCallFiniteContext program generatedContext =
      evalPanSemRecursiveCallFiniteContext program
        (callEntryContextHOLFinite context callee) := by
  apply evalPanSemRecursiveCallFiniteContext_state_eq
  simpa [callEntryContextHOLFinite, FiniteEvalContext.withState] using hstate

/-- FLAPJACK-SPECIFIC proof wrapper (no standalone HOL declaration): the
    DecCall body premise may be supplied at the canonical named entry context.
    The recursive equation creates an extensionally identical `withState`
    context with equation-compiler-generated domain proofs; evaluator
    state-independence bridges those contexts without exposing or rewriting
    their dependent proof arguments. This keeps the generated DecCall equation
    and existing projection interface unchanged. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_return_shape_mismatch_of_canonical_body
    {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width)
    (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.returned value), bodyContext))
    (hshape : shapeEqHOL (shapeOfHOLExact value) shape = false ∨
      shapeEqHOL (shapeOfHOLExact value) returnShape = false) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some (.returned value)) bodyContext) := by
  have hbodyGenerated : evalPanSemRecursiveCallFiniteContext body
      (context.withState (callEntryStateHOLFinite context.state callee) rfl rfl) =
      some (some (.returned value), bodyContext) := by
    calc
      _ = evalPanSemRecursiveCallFiniteContext body
          (callEntryContextHOLFinite context callee) := by
        apply evalPanSemRecursiveCallFiniteContext_callEntryContext_state_normalize
        rfl
      _ = _ := hbody
  exact evalPanSemRecursiveCallFiniteContext_decCall_return_shape_mismatch
    resultName shape function arguments continuation context values body callee
    returnShape value bodyContext hargs hlookup hclock hbodyGenerated hshape

/-- HOL `evaluate_def` `DecCall` return branch: when the body returns a value
    whose shape matches both the declaration and code entry, the continuation
    runs from `callContinuationContextHOLFinite` (caller locals plus the result
    binding), and its result state has the previous binding restored via
    `res_var`. This pins the recursive continuation and restoration side of
    `panSemScript.sml:694-729`; the surrounding source note records the exact
    argument, lookup, and fixed-clock branches. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_return_continuation
    {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (value : ValueHOL width)
    (bodyContext continuationPost : FiniteEvalContext width σ)
    (continuationResult : Option (PanSemResultExact width))
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some (.returned value), bodyContext))
    (hshape : shapeEqHOL (shapeOfHOLExact value) shape = true ∧
      shapeEqHOL (shapeOfHOLExact value) returnShape = true)
    (hcontinuation : evalPanSemRecursiveCallFiniteContext continuation
      (callContinuationContextHOLFinite context
        (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some (.returned value)) bodyContext) resultName value) =
      some (continuationResult, continuationPost)) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (continuationResult,
        continuationPost.withState
          { continuationPost.state with
            locals := HolFiniteMapExact.resVarEq continuationPost.state.locals
              (resultName, context.state.locals.lookup resultName) } rfl rfl) := by
  have hbodyGenerated : evalPanSemRecursiveCallFiniteContext body
      (context.withState (callEntryStateHOLFinite context.state callee) rfl rfl) =
      some (some (.returned value), bodyContext) := by
    calc
      _ = evalPanSemRecursiveCallFiniteContext body
          (callEntryContextHOLFinite context callee) := by
        apply evalPanSemRecursiveCallFiniteContext_callEntryContext_state_normalize
        rfl
      _ = _ := hbody
  rw [evalPanSemRecursiveCallFiniteContext.eq_6]
  simp only [hargs]
  rw [lookupCodeCanonicalHOL, hlookup]
  simp only [if_neg hclock, hbodyGenerated]
  rw [if_pos (by simp [hshape])]
  rw [hcontinuation]

/-- Projection equivalence on `Skip`: mapping the finite evaluator's result
    through the canonical carrier projection `state.toExact` agrees with the
    broad exact evaluator on its (forgetful) projection.  First of the
    per-constructor projection-equivalence lemmas for `flapjack-6yq`. -/
theorem evalPanSemRecursiveCallFiniteContext_skip_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (evalPanSemRecursiveCallFiniteContext (.skip : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.skip : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp

/-- Projection equivalence on `Break` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_break_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (evalPanSemRecursiveCallFiniteContext (.break : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.break : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp

/-- Projection equivalence on `Continue` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_continue_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (evalPanSemRecursiveCallFiniteContext (.continue : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.continue : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp

/-- Projection equivalence on `Annot` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_annot_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (tag text : MlS) :
    (evalPanSemRecursiveCallFiniteContext (.annot tag text : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.annot tag text : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp


/-- Projection equivalence on `Assign` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_assign_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (kind : VarKind) (name : MlS)
    (value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.assign kind name value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.assign kind name value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `Primitive` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_primitive_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (name : MlS) (operator : PrimOp)
    (args : List (ExpHOL width)) :
    (evalPanSemRecursiveCallFiniteContext (.primitive name operator args : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.primitive name operator args : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `Store` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_store_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (address value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.store address value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.store address value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `Store32` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_store32_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (address value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.store32 address value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.store32 address value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `StoreByte` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_storeByte_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (address value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.storeByte address value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.storeByte address value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `ExtCall` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_extCall_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (function : MlS)
    (configuration configurationLength array arrayLength : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.extCall function configuration configurationLength array arrayLength : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.extCall function configuration configurationLength array arrayLength : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `Tick` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_tick_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (evalPanSemRecursiveCallFiniteContext (.tick : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.tick : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  by_cases hclock : context.state.clock = 0
  · rw [if_pos hclock, if_pos hclock]
    rfl
  · rw [if_neg hclock, if_neg hclock]
    rfl

/-- Projection equivalence on `Return` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_return_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.return value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.return value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  letI : DecidablePred context.state.memaddrs := context.memaddrsDecidable
  rw [← evalHOLFinite_eq_toExact context.state value]
  generalize hval : context.state.evalHOLFinite value = result
  cases result with
  | none => simp only [Option.map_some]
  | some returned =>
      simp only []
      by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.state.structs
          (shapeOfHOLExact returned) ≤ 32
      · rw [if_pos hsize, if_pos hsize]
        rfl
      · rw [if_neg hsize, if_neg hsize]
        rfl

/-- Projection equivalence on `Raise` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_raise_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (exception : MlS)
    (value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.raise exception value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.raise exception value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  letI : DecidablePred context.state.memaddrs := context.memaddrsDecidable
  rw [← evalHOLFinite_eq_toExact context.state value]
  generalize hval : context.state.evalHOLFinite value = result
  cases result with
  | none => simp only [Option.map_some]
  | some raised =>
      simp only []
      cases hshape : context.state.eshapes.lookup exception with
      | none => simp only [Option.map_some]
      | some shape =>
          simp only []
          by_cases heq : shapeEqHOL (shapeOfHOLExact raised) shape
          · rw [if_pos heq, if_pos heq]
            by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.state.structs
                (shapeOfHOLExact raised) ≤ 32
            · rw [if_pos hsize, if_pos hsize]
              rfl
            · rw [if_neg hsize, if_neg hsize]
              rfl
          · rw [if_neg heq, if_neg heq]
            rfl

/-- Projection equivalence on `ShMemLoad` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_shMemLoad_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (size : OpSize)
    (kind : VarKind) (name : MlS) (address : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext
        (.shMemLoad size kind name address : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact
        (.shMemLoad size kind name address : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  rfl

/-- Projection equivalence on `ShMemStore` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_shMemStore_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (size : OpSize)
    (address value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext
        (.shMemStore size address value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact
        (.shMemStore size address value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  rfl

/-- Projection equivalence on `Seq`, stated with projection hypotheses for the
    two recursive sub-calls so that it composes into the general induction.
    This is Flapjack-specific infrastructure; it is not a HOL declaration. -/
theorem evalPanSemRecursiveCallFiniteContext_seq_projection {width : Nat} {σ : Type}
    [NeZero width] (first second : ProgHOL width) (context : FiniteEvalContext width σ)
    (ihFirst : ∀ (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext first context = o →
        evalPanSemRecursiveCallContextHOLExact first context.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o)
    (ihSecond : ∀ (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext second fc = o →
        evalPanSemRecursiveCallContextHOLExact second fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext (.seq first second) context) =
      evalPanSemRecursiveCallContextHOLExact (.seq first second) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_2,
    evalPanSemRecursiveCallContextHOLExact.eq_2]
  cases hfin : evalPanSemRecursiveCallFiniteContext first context with
  | none =>
      rw [ihFirst none hfin]
      simp only [Option.map_none]
  | some pair =>
      obtain ⟨firstResult, firstContext⟩ := pair
      rw [ihFirst (some (firstResult, firstContext)) hfin]
      simp only [Option.map_some]
      cases firstResult with
      | none =>
          simp only []
          rw [← ihSecond _ _ rfl]
          congr 1
      | some r =>
          simp only [Option.map_some]
          congr 1

/-- Alignment helper: `evalHOLExact` on `context.toExact` agrees with
    `evalHOLExact` on `context.state.toExact` (same instance).  Flapjack-specific. -/
theorem evalHOLExact_toExact_eq {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (expression : ExpHOL width) :
    @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable
        expression =
      @Flapjack.evalHOLExact width σ _ context.state.toExact context.memaddrsDecidable
        expression :=
  rfl

/-- Argument-list alignment helper: `evalListHOLExact` on `context.toExact` agrees
    with `evalListHOLExact` on `context.state.toExact` (same instance).  Flapjack-specific. -/
theorem evalListHOLExact_toExact_eq {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (expressions : List (ExpHOL width)) :
    @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable
        expressions =
      @Flapjack.evalListHOLExact width σ _ context.state.toExact context.memaddrsDecidable
        expressions :=
  rfl

/-- Projection-equivalence for the finite `Dec` clause against the broad exact
    evaluator, given the projection hypothesis for the recursive body.  Untagged
    Flapjack-specific support for the `evaluate_def` port. -/
theorem evalPanSemRecursiveCallFiniteContext_dec_projection {width : Nat} {σ : Type}
    [NeZero width] (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width)
    (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (ihBody : ∀ (bc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext body bc = o →
        evalPanSemRecursiveCallContextHOLExact body bc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext (.dec name shape initializer body) context) =
      evalPanSemRecursiveCallContextHOLExact (.dec name shape initializer body) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_1, evalPanSemRecursiveCallContextHOLExact.eq_1]
  rw [evalHOLFinite_eq_toExact context.state (h := context.memaddrsDecidable) initializer]
  rw [evalHOLExact_toExact_eq context initializer]
  generalize hval : @Flapjack.evalHOLExact width σ _ context.state.toExact
      context.memaddrsDecidable initializer = result
  cases result with
  | none => rfl
  | some value =>
      simp only []
      by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value) = true
      · rw [if_pos hshape, if_pos hshape]
        generalize hbc : context.withState (setVarHOLFinite name value context.state) rfl rfl = bc
        generalize hbcb : context.toExact.withState
            (setVarHOLExact name value context.toExact.state) rfl rfl = bbc
        have hbbc : bbc = bc.toExact := by
          rw [← hbcb, ← hbc]
          apply PanSemExactEvalContext.ext
          change setVarHOLExact name value context.state.toExact =
            (setVarHOLFinite name value context.state).toExact
          rw [toExact_setVarHOLFinite]
        cases hbody : evalPanSemRecursiveCallFiniteContext body bc with
        | none => rw [hbbc, ihBody bc none hbody]; simp only [Option.map_none]
        | some pair =>
            obtain ⟨result, postContext⟩ := pair
            rw [hbbc, ihBody bc (some (result, postContext)) hbody]
            simp only [Option.map_some, Option.some.injEq]
            refine congrArg (fun c => (result, c)) ?_
            apply PanSemExactEvalContext.ext
            simp only [FiniteEvalContext.toExact, PanSemExactEvalContext.withState_state,
              FiniteEvalContext.withState_state, toExact_resVarEq_locals]
      · rw [if_neg hshape, if_neg hshape]; rfl

/-- The `If` clause recurses on the same context, so its projection follows
    directly from the two branch IHs.  Flapjack-specific. -/
theorem evalPanSemRecursiveCallFiniteContext_ite_projection {width : Nat} {σ : Type}
    [NeZero width] (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (ihThen : ∀ (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext thenBranch context = o →
        evalPanSemRecursiveCallContextHOLExact thenBranch context.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o)
    (ihElse : ∀ (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext elseBranch context = o →
        evalPanSemRecursiveCallContextHOLExact elseBranch context.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext (.ite condition thenBranch elseBranch) context) =
      evalPanSemRecursiveCallContextHOLExact (.ite condition thenBranch elseBranch) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_3, evalPanSemRecursiveCallContextHOLExact.eq_3]
  rw [evalHOLFinite_eq_toExact context.state (h := context.memaddrsDecidable) condition]
  rw [evalHOLExact_toExact_eq context condition]
  generalize hcond : @Flapjack.evalHOLExact width σ _ context.state.toExact
      context.memaddrsDecidable condition = result
  cases result with
  | none => rfl
  | some v =>
      cases v with
      | val wordLab =>
          cases wordLab with
          | word value =>
              simp only []
              by_cases hz : (value != 0) = true
              · rw [if_pos hz, if_pos hz]
                exact (ihThen (evalPanSemRecursiveCallFiniteContext thenBranch context) rfl).symm
              · rw [if_neg hz, if_neg hz]
                exact (ihElse (evalPanSemRecursiveCallFiniteContext elseBranch context) rfl).symm
      | rStruct fields => rfl
      | nStruct name fields => rfl

/-- Projection equivalence for the `While` clause, using a body IH and a self IH. -/
theorem evalPanSemRecursiveCallFiniteContext_while_projection {width : Nat} {σ : Type}
    [NeZero width] (condition : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (ihBody : ∀ (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext body fc = o →
        evalPanSemRecursiveCallContextHOLExact body fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o)
    (ihSelf : ∀ (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext (.while condition body) fc = o →
        evalPanSemRecursiveCallContextHOLExact (.while condition body) fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext (.while condition body) context) =
      evalPanSemRecursiveCallContextHOLExact (.while condition body) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_4, evalPanSemRecursiveCallContextHOLExact.eq_4]
  rw [evalHOLFinite_eq_toExact context.state (h := context.memaddrsDecidable) condition]
  rw [evalHOLExact_toExact_eq context condition]
  generalize hcond : @Flapjack.evalHOLExact width σ _ context.state.toExact
      context.memaddrsDecidable condition = result
  cases result with
  | none => rfl
  | some v =>
      cases v with
      | val wordLab =>
          cases wordLab with
          | word word =>
              simp only []
              by_cases hw : word ≠ 0
              · rw [if_pos hw, if_pos hw]
                by_cases hclock : context.state.clock = 0
                · have hclock' : context.toExact.state.clock = 0 := hclock
                  rw [if_pos hclock, if_pos hclock']
                  simp only [Option.map_some, Option.some.injEq]
                  have hb : (context.withState (emptyLocalsHOLFinite context.state) rfl rfl).toExact =
                      context.toExact.withState (emptyLocalsHOLExact context.toExact.state) rfl rfl := by
                    apply PanSemExactEvalContext.ext
                    change emptyLocalsHOLExact context.state.toExact =
                      (emptyLocalsHOLFinite context.state).toExact
                    rw [toExact_emptyLocalsHOLFinite]
                  rw [hb]
                · have hclock' : ¬(context.toExact.state.clock = 0) := hclock
                  rw [if_neg hclock, if_neg hclock']
                  generalize hent : context.withState (decClockHOLFinite context.state) rfl rfl = ent
                  generalize hentb : context.toExact.withState
                      (decClockHOLExact context.toExact.state) rfl rfl = entb
                  have hentb_eq : entb = ent.toExact := by
                    rw [← hentb, ← hent]
                    apply PanSemExactEvalContext.ext
                    change decClockHOLExact context.state.toExact =
                      (decClockHOLFinite context.state).toExact
                    rw [toExact_decClockHOLFinite]
                  rw [hentb_eq]
                  cases hbody : evalPanSemRecursiveCallFiniteContext body ent with
                  | none => rw [ihBody ent none hbody]; simp only [Option.map_none]
                  | some pair =>
                      obtain ⟨bodyResult, bodyContext⟩ := pair
                      rw [ihBody ent (some (bodyResult, bodyContext)) hbody]
                      simp only [Option.map_some]
                      cases bodyResult with
                      | none => rw [← ihSelf _ _ rfl]; congr 1
                      | some r =>
                          cases r with
                          | «continue» => rw [← ihSelf _ _ rfl]; congr 1
                          | «break» => congr 1
                          | _ => congr 1
              · rw [if_neg hw, if_neg hw]; rfl
      | rStruct fields => rfl
      | nStruct name fields => rfl

macro "callProjectionCloser" : tactic =>
  `(tactic|
    first
    | (simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
       exact ⟨rfl, by apply PanSemExactEvalContext.ext; rfl⟩)
    | (apply PanSemExactEvalContext.ext; rfl)
    | (apply PanSemExactEvalContext.ext
       simp only [FiniteEvalContext.withState_state, toExact_setKvarHOLFinite,
         toExact_setLocals, FiniteEvalContext.toExact_emptyLocalsContextHOLFinite,
         toExact_callRestoreLocalsContextHOLFinite,
         toExact_callSetKvarContextHOLFinite])
    | rfl)

set_option maxHeartbeats 1000000 in
theorem evalPanSemRecursiveCallFiniteContext_call_projection {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (context : FiniteEvalContext width σ)
    (ihBody : ∀ (prog : ProgHOL width) (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext prog fc = o →
        evalPanSemRecursiveCallContextHOLExact prog fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o)
    (ihHandler : ∀ (prog : ProgHOL width) (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext prog fc = o →
        evalPanSemRecursiveCallContextHOLExact prog fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext (.call info function arguments) context) =
      evalPanSemRecursiveCallContextHOLExact (.call info function arguments) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_5, evalPanSemRecursiveCallContextHOLExact.eq_5]
  rw [evalListHOLFinite_eq_toExact context.state (h := context.memaddrsDecidable) arguments]
  rw [evalListHOLExact_toExact_eq context arguments]
  generalize hargs : @Flapjack.evalListHOLExact width σ _ context.state.toExact
      context.memaddrsDecidable arguments = result
  cases result with
  | none => rfl
  | some values =>
      simp only []
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      split
      · rename_i hnone
        rw [(lookupCodeHOLFinite_eq_none_iff (code := context.state.code.lookup)
          (fname := function) (values := values)).mp hnone]
        rfl
      · rename_i body callee returnShape hsome
        rw [lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee
          returnShape hsome]
        simp only []
        by_cases hclock : context.state.clock = 0
        · have hclock' : context.toExact.state.clock = 0 := hclock
          rw [if_pos hclock, if_pos hclock']
          simp only [Option.map_some, Option.some.injEq]
          have hb : (FiniteEvalContext.emptyLocalsContextHOLFinite context).toExact =
              context.toExact.withState (emptyLocalsHOLExact context.state.toExact) rfl rfl := by
            exact FiniteEvalContext.toExact_emptyLocalsContextHOLFinite context
          rw [hb]
          rfl
        · have hclock' : ¬(context.toExact.state.clock = 0) := hclock
          rw [if_neg hclock, if_neg hclock']
          generalize hent : callEntryContextHOLFinite context callee = ent
          generalize hentb : context.toExact.withState
            (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
          have hentb_eq : entb = ent.toExact := by
            rw [← hentb, ← hent]
            exact (FiniteEvalContext.toExact_callEntryContext context callee).symm
          rw [hentb_eq]
          cases hbody : evalPanSemRecursiveCallFiniteContext body ent with
          | none =>
              rw [ihBody body ent none hbody]
              simp only [Option.map_none]
          | some pair =>
              obtain ⟨bodyResult, bodyContext⟩ := pair
              rw [ihBody body ent (some (bodyResult, bodyContext)) hbody]
              simp only [Option.map_some]
              cases bodyResult with
              | none => callProjectionCloser
              | some r =>
                cases r with
                | «error» => callProjectionCloser
                | «timeOut» => callProjectionCloser
                | «break» => callProjectionCloser
                | «continue» => callProjectionCloser
                | returned value =>
                  simp only []
                  by_cases hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true
                  · simp only [if_pos hshape]
                    cases info with
                    | none => callProjectionCloser
                    | some istr =>
                      obtain ⟨returns, handler⟩ := istr
                      cases returns with
                      | none => callProjectionCloser
                      | some kn =>
                        obtain ⟨kind, name⟩ := kn
                        simp only []
                        by_cases hvalid : isValidValueHOLExact context.state.toExact kind name value = true
                        · have hvalid' : isValidValueHOLExact context.toExact.state kind name value = true := hvalid
                          rw [if_pos hvalid, if_pos hvalid']
                          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
                          refine ⟨trivial, ?_⟩
                          apply PanSemExactEvalContext.ext
                          rw [toExact_callSetKvarContextHOLFinite]
                          rfl
                        · have hvalid' : ¬(isValidValueHOLExact context.toExact.state kind name value = true) := hvalid
                          simp only [if_neg hvalid, if_neg hvalid']; callProjectionCloser
                  · simp only [if_neg hshape]; callProjectionCloser
                | exception eid value =>
                  simp only []
                  cases info with
                  | none => callProjectionCloser
                  | some istr =>
                    obtain ⟨returns, handler⟩ := istr
                    cases handler with
                    | none => callProjectionCloser
                    | some hkn =>
                      obtain ⟨handlerId, handlerVar, handlerProgram⟩ := hkn
                      simp only []
                      by_cases heq : eid = handlerId
                      · simp only [if_pos heq]
                        rw [show context.toExact.state.eshapes = context.state.eshapes.lookup from rfl]
                        cases hshapes : context.state.eshapes.lookup eid with
                        | none => simp only []; callProjectionCloser
                        | some shape =>
                          simp only []
                          by_cases hcond : (shapeEqHOL (shapeOfHOLExact value) shape &&
                            isValidValueHOLExact context.state.toExact VarKind.local handlerVar value) = true
                          · have hcond' : (shapeEqHOL (shapeOfHOLExact value) shape &&
                              isValidValueHOLExact context.toExact.state VarKind.local handlerVar value) = true := hcond
                            simp only [if_pos hcond, if_pos hcond']
                            rw [← ihHandler handlerProgram _ _ rfl]
                            congr 1
                            apply PanSemExactEvalContext.ext
                            simp only [FiniteEvalContext.toExact,
                              PanSemExactEvalContext.withState_state]
                            apply toExact_handlerStateHOLFinite
                            apply PanSemExactEvalContext.ext
                            change ((context.state.callEntryStateHOLFinite callee).fixClockHOLFinite
                                (some (PanSemResultExact.exception eid value), bodyContext.state)).snd.toExact =
                              (fixClockHOLExact
                                (callEntryStateHOLExact context.state.toExact callee.lookup)
                                (some (PanSemResultExact.exception eid value),
                                  bodyContext.state.toExact)).snd
                            rw [toExact_fixClockHOLFinite, toExact_callEntryStateHOLFinite]
                          · have hcond' : ¬((shapeEqHOL (shapeOfHOLExact value) shape &&
                              isValidValueHOLExact context.toExact.state VarKind.local handlerVar value) = true) := hcond
                            simp only [if_neg hcond, if_neg hcond']; callProjectionCloser
                      · simp only [if_neg heq]; callProjectionCloser
                | finalFfi e => callProjectionCloser

set_option maxHeartbeats 1000000 in
theorem evalPanSemRecursiveCallFiniteContext_decCall_projection {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL width))
    (continuation : ProgHOL width) (context : FiniteEvalContext width σ)
    (ihBody : ∀ (prog : ProgHOL width) (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext prog fc = o →
        evalPanSemRecursiveCallContextHOLExact prog fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o)
    (ihContinuation : ∀ (prog : ProgHOL width) (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext prog fc = o →
        evalPanSemRecursiveCallContextHOLExact prog fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext
          (.decCall resultName shape function arguments continuation) context) =
      evalPanSemRecursiveCallContextHOLExact
        (.decCall resultName shape function arguments continuation) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_6, evalPanSemRecursiveCallContextHOLExact.eq_6]
  rw [evalListHOLFinite_eq_toExact context.state (h := context.memaddrsDecidable) arguments]
  rw [evalListHOLExact_toExact_eq context arguments]
  generalize hargs : @Flapjack.evalListHOLExact width σ _ context.state.toExact
      context.memaddrsDecidable arguments = result
  cases result with
  | none => rfl
  | some values =>
      simp only []
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      split
      · rename_i hnone
        rw [(lookupCodeHOLFinite_eq_none_iff (code := context.state.code.lookup)
          (fname := function) (values := values)).mp hnone]
        rfl
      · rename_i body callee returnShape hsome
        rw [lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee
          returnShape hsome]
        simp only []
        by_cases hclock : context.state.clock = 0
        · have hclock' : context.toExact.state.clock = 0 := hclock
          rw [if_pos hclock, if_pos hclock']
          simp only [Option.map_some, Option.some.injEq]
          rw [FiniteEvalContext.toExact_emptyLocalsContextHOLFinite]
        · have hclock' : ¬(context.toExact.state.clock = 0) := hclock
          rw [if_neg hclock, if_neg hclock']
          generalize hent : context.withState
            (callEntryStateHOLFinite context.state callee) rfl rfl = ent
          generalize hentb : context.toExact.withState
            (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
          have hentb_eq : entb = ent.toExact := by
            rw [← hentb, ← hent]
            apply PanSemExactEvalContext.ext
            change (callEntryStateHOLFinite context.state callee).toExact =
              Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
            rw [toExact_callEntryStateHOLFinite]
            rfl
          rw [hentb_eq]
          cases hbody : evalPanSemRecursiveCallFiniteContext body ent with
          | none => rw [ihBody body ent none hbody]; simp only [Option.map_none]
          | some pair =>
              obtain ⟨bodyResult, bodyContext⟩ := pair
              rw [ihBody body ent (some (bodyResult, bodyContext)) hbody]
              simp only [Option.map_some]
              cases bodyResult with
              | none => callProjectionCloser
              | some r =>
                cases r with
                | «error» => callProjectionCloser
                | «timeOut» => callProjectionCloser
                | «break» => callProjectionCloser
                | «continue» => callProjectionCloser
                | returned value =>
                  simp only []
                  by_cases hshape : (shapeEqHOL (shapeOfHOLExact value) shape &&
                      shapeEqHOL (shapeOfHOLExact value) returnShape) = true
                  · simp only [if_pos hshape]
                    rw [← toExact_callContinuationContextHOLFinite context
                      (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
                        (some (PanSemResultExact.returned value)) bodyContext)
                      (Flapjack.callFixedContextHOLExact
                        (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup)
                        (some (PanSemResultExact.returned value)) bodyContext.toExact)
                      (toExact_callFixedContextHOLFinite
                        (callEntryStateHOLFinite context.state callee)
                        (some (PanSemResultExact.returned value)) bodyContext)
                      resultName value]
                    cases hcont : evalPanSemRecursiveCallFiniteContext continuation
                        (callContinuationContextHOLFinite context
                          (callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
                            (some (PanSemResultExact.returned value)) bodyContext)
                          resultName value) with
                    | none =>
                        rw [ihContinuation continuation _ none hcont]
                        simp only [Option.map_none]
                    | some cpair =>
                        obtain ⟨continuationResult, continuationPost⟩ := cpair
                        rw [ihContinuation continuation _
                          (some (continuationResult, continuationPost)) hcont]
                        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
                        refine ⟨trivial, ?_⟩
                        apply PanSemExactEvalContext.ext
                        simp only [FiniteEvalContext.toExact,
                          PanSemExactEvalContext.withState_state]
                        change ({ continuationPost.state with
                            locals := HolFiniteMapExact.resVarEq
                              continuationPost.state.locals
                              (resultName, context.state.locals.lookup resultName) } :
                            PanSemStateFiniteExact width σ).toExact =
                          { continuationPost.toExact.state with
                            locals := resVarHOLExact continuationPost.toExact.state.locals
                              (resultName, context.toExact.state.locals resultName) }
                        rw [toExact_resVarEq_locals]
                        congr 1
                  · simp only [if_neg hshape]; callProjectionCloser
                | exception eid value => callProjectionCloser
                | finalFfi e => callProjectionCloser


theorem callFixedContextHOLFinite_toExact {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (postContext : FiniteEvalContext width σ) (bodyResult : Option (PanSemResultExact width)) :
    ((context.state.callEntryStateHOLFinite callee).callFixedContextHOLFinite bodyResult
        postContext).toExact =
      Flapjack.callFixedContextHOLExact
        (Flapjack.callEntryStateHOLExact context.state.toExact callee.lookup)
        bodyResult postContext.toExact := by
  rw [toExact_callFixedContextHOLFinite]
  congr 1

/- Source-review note for HOL `evaluate_def` (`panSemScript.sml:556-761`):
    the 66-case induction below projects every finite-context branch to the
    broad evaluator. The finite clauses preserve HOL's evaluation/error
    splits for all 21 constructors; the detailed clause groups and carrier
    review are recorded at this module's header. In particular, the finite
    projection uses `evalHOLFinite`/`lookupCodeHOLFinite`, finite-map
    `resVarEq` restoration, and the named Call/DecCall entry/fixed/continuation
    bridges. This proves finite-to-broad agreement; it does not by itself
    establish the broad evaluator's HOL correspondence, so the
    `evaluate_def` tag remains withheld pending coordinator review. -/
set_option maxHeartbeats 2000000 in
theorem evalPanSemRecursiveCallFiniteContext_projection {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : FiniteEvalContext width σ) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext program context) =
      evalPanSemRecursiveCallContextHOLExact program context.toExact := by
  fun_induction evalPanSemRecursiveCallFiniteContext program context with
  | case1 =>
      rename_i inst context state name shape initializer body x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_1]
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable initializer = none := by
        rw [evalHOLExact_toExact_eq context initializer]
        exact x
      simp only [hx]
      rfl
  | case2 =>
      rename_i inst context state name shape initializer body value x1 h bodyState bodyContext x ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_1]
      have hx1 : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable initializer = some value := by
        rw [evalHOLExact_toExact_eq context initializer]
        exact x1
      simp only [hx1]
      simp only [h, if_true]
      generalize hbcb : context.toExact.withState (setVarHOLExact name value context.toExact.state) rfl rfl = bbc
      have hbbc : bbc = bodyContext.toExact := by
        rw [← hbcb]
        apply PanSemExactEvalContext.ext
        simp only [PanSemExactEvalContext.withState_state, FiniteEvalContext.toExact]
        change setVarHOLExact name value context.state.toExact =
          (setVarHOLFinite name value context.state).toExact
        rw [toExact_setVarHOLFinite]
      rw [hbbc]
      rw [← ih1, x]
      rfl
  | case3 =>
      rename_i inst context state name shape initializer body value x1 h bodyState bodyContext result postContext x restored ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_1]
      have hx1 : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable initializer = some value := by
        rw [evalHOLExact_toExact_eq context initializer]
        exact x1
      simp only [hx1]
      simp only [h, if_true]
      generalize hbcb : context.toExact.withState (setVarHOLExact name value context.toExact.state) rfl rfl = bbc
      have hbbc : bbc = bodyContext.toExact := by
        rw [← hbcb]
        apply PanSemExactEvalContext.ext
        simp only [PanSemExactEvalContext.withState_state, FiniteEvalContext.toExact]
        change setVarHOLExact name value context.state.toExact =
          (setVarHOLFinite name value context.state).toExact
        rw [toExact_setVarHOLFinite]
      rw [hbbc]
      rw [← ih1, x]
      simp only [Option.map_some, Option.some.injEq]
      refine congrArg (fun c => (result, c)) ?_
      apply PanSemExactEvalContext.ext
      change ({ postContext.state with locals := HolFiniteMapExact.resVarEq postContext.state.locals (name, state.locals.lookup name) } : PanSemStateFiniteExact width σ).toExact =
        { postContext.toExact.state with locals := resVarHOLExact postContext.toExact.state.locals (name, context.toExact.state.locals name) }
      rw [toExact_resVarEq_locals]
      congr 1
  | case4 =>
      rename_i inst context state name shape initializer body value x h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_1]
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable initializer = some value := by
        rw [evalHOLExact_toExact_eq context initializer]
        exact x
      simp only [hx]
      rw [if_neg h]
      rfl
  | case5 =>
      rename_i inst context first second x ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_2]
      rw [← ih1, x]
      rfl
  | case6 =>
      rename_i inst context state first second postContext x fixed fixedContext ih2 ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_2]
      rw [← ih2, x]
      simp only [Option.map_some]
      exact ih1
  | case7 =>
      rename_i inst context state first second postContext val x fixed fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_2]
      rw [← ih1, x]
      simp only [Option.map_some]
      rfl
  | case8 =>
      rename_i inst context state condition thenBranch elseBranch value x h ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_3]
      have hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) := by
        rw [evalHOLExact_toExact_eq context condition]
        exact x
      simp only [hc]
      simp only [h, if_true]
      exact ih1
  | case9 =>
      rename_i inst context state condition thenBranch elseBranch value x h ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_3]
      have hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) := by
        rw [evalHOLExact_toExact_eq context condition]
        exact x
      simp only [hc]
      rw [if_neg h]
      exact ih1
  | case10 =>
      rename_i inst context state condition thenBranch elseBranch x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_3]
      have hx : ∀ value, @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) → False := by
        intro value hv
        rw [evalHOLExact_toExact_eq context condition] at hv
        exact x value hv
      cases hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition with
      | none => rfl
      | some v =>
        cases v with
        | val wordLab => cases wordLab with | word value => exact (hx value hc).elim
        | rStruct fields => rfl
        | nStruct name fields => rfl
  | case11 =>
      rename_i inst context state condition body value x h1 h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_4]
      have hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) := by
        rw [evalHOLExact_toExact_eq context condition]
        exact x
      simp only [hc]
      rw [if_pos h1]
      have h' : context.toExact.state.clock = 0 := h
      rw [if_pos h']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      change emptyLocalsHOLExact context.state.toExact = (emptyLocalsHOLFinite context.state).toExact
      rw [toExact_emptyLocalsHOLFinite]
  | case12 =>
      rename_i inst context state condition body value x1 h1 hclock entry entryContext x ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_4]
      have hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) := by
        rw [evalHOLExact_toExact_eq context condition]
        exact x1
      simp only [hc]
      rw [if_pos h1]
      have hclock' : ¬(context.toExact.state.clock = 0) := hclock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (decClockHOLExact context.toExact.state) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change decClockHOLExact context.state.toExact = (decClockHOLFinite context.state).toExact
        rw [toExact_decClockHOLFinite]
      rw [hentb_eq]
      rw [← ih1, x]
      rfl
  | case13 =>
      rename_i inst context state condition body value x1 h1 hclock entry entryContext postContext x fixed fixedContext ih2 ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_4]
      have hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) := by
        rw [evalHOLExact_toExact_eq context condition]
        exact x1
      simp only [hc]
      rw [if_pos h1]
      have hclock' : ¬(context.toExact.state.clock = 0) := hclock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (decClockHOLExact context.toExact.state) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change decClockHOLExact context.state.toExact = (decClockHOLFinite context.state).toExact
        rw [toExact_decClockHOLFinite]
      rw [hentb_eq]
      rw [← ih2, x]
      simp only [Option.map_some]
      exact ih1
  | case14 =>
      rename_i inst context state condition body value x1 h1 hclock entry entryContext postContext x fixed fixedContext ih2 ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_4]
      have hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) := by
        rw [evalHOLExact_toExact_eq context condition]
        exact x1
      simp only [hc]
      rw [if_pos h1]
      have hclock' : ¬(context.toExact.state.clock = 0) := hclock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (decClockHOLExact context.toExact.state) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change decClockHOLExact context.state.toExact = (decClockHOLFinite context.state).toExact
        rw [toExact_decClockHOLFinite]
      rw [hentb_eq]
      rw [← ih2, x]
      simp only [Option.map_some]
      exact ih1
  | case15 =>
      rename_i inst context state condition body value x1 h1 hclock entry entryContext postContext x fixed fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_4]
      have hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) := by
        rw [evalHOLExact_toExact_eq context condition]
        exact x1
      simp only [hc]
      rw [if_pos h1]
      have hclock' : ¬(context.toExact.state.clock = 0) := hclock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (decClockHOLExact context.toExact.state) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change decClockHOLExact context.state.toExact = (decClockHOLFinite context.state).toExact
        rw [toExact_decClockHOLFinite]
      rw [hentb_eq]
      rw [← ih1, x]
      simp only [Option.map_some]
      rfl
  | case16 =>
      rename_i inst context state condition body value x4 h1 hclock entry entryContext result postContext x3 fixed fixedContext x2 x1 x0 ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_4]
      have hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) := by
        rw [evalHOLExact_toExact_eq context condition]
        exact x4
      simp only [hc]
      rw [if_pos h1]
      have hclock' : ¬(context.toExact.state.clock = 0) := hclock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (decClockHOLExact context.toExact.state) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change decClockHOLExact context.state.toExact = (decClockHOLFinite context.state).toExact
        rw [toExact_decClockHOLFinite]
      rw [hentb_eq]
      rw [← ih1, x3]
      simp only [Option.map_some]
      rfl
  | case17 =>
      rename_i inst context state condition body value x h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_4]
      have hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) := by
        rw [evalHOLExact_toExact_eq context condition]
        exact x
      simp only [hc]
      rw [if_neg h]
      simp only [Option.map_some]
  | case18 =>
      rename_i inst context state condition body x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_4]
      have hx : ∀ value, @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition = some (.val (.word value)) → False := by
        intro value hv
        rw [evalHOLExact_toExact_eq context condition] at hv
        exact x value hv
      cases hc : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable condition with
      | none => rfl
      | some v =>
        cases v with
        | val wordLab => cases wordLab with | word value => exact (hx value hc).elim
        | rStruct fields => rfl
        | nStruct name fields => rfl
  | case19 =>
      rename_i inst context state info function arguments x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      have hx : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = none := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x
      simp only [hx, Option.map_some]
  | case20 =>
      rename_i inst context state info function arguments values x1 x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x1
      have hl : lookupCodeHOLExact context.state.code.lookup function values = none :=
        (lookupCodeHOLFinite_eq_none_iff (code := context.state.code.lookup) (fname := function) (values := values)).mp x
      simp only [hargs, hl, Option.map_some]
  | case21 =>
      rename_i inst context state info function arguments values x1 body callee returnShape x h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x1
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x
      simp only [hargs, hl]
      have hclock' : context.toExact.state.clock = 0 := h
      rw [if_pos hclock']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      change emptyLocalsHOLExact context.state.toExact = (emptyLocalsHOLFinite context.state).toExact
      rw [toExact_emptyLocalsHOLFinite]
  | case22 =>
      rename_i inst context state info function arguments values x2 body callee returnShape x1 h entryContext x ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := h
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact =
          Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq]
      rw [← ih1, x]
      rfl
  | case23 =>
      rename_i inst context state info function arguments values x2 body callee returnShape x1 h entry entryContext postContext x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := h
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentry : callEntryContextHOLFinite context callee = entryContext := rfl
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        rw [← hentry]
        exact (FiniteEvalContext.toExact_callEntryContext context callee).symm
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some, Option.some.injEq]
      congr 1
  | case24 =>
      rename_i inst context state info function arguments values x2 body callee returnShape x1 h entry entryContext postContext x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := h
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentry : callEntryContextHOLFinite context callee = entryContext := rfl
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        rw [← hentry]
        exact (FiniteEvalContext.toExact_callEntryContext context callee).symm
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some, Option.some.injEq]
      congr 1
  | case25 =>
      rename_i inst context state info function arguments values x2 body callee returnShape x1 h entry entryContext postContext x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := h
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some, Option.some.injEq]
      congr 1
  | case26 =>
      rename_i inst context state function arguments values x2 body callee returnShape x1 hClock entry entryContext postContext value hshape x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      rw [if_pos hshape]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      simp only [FiniteEvalContext.toExact,
        PanSemExactEvalContext.withState_state]
      congr 1
  | case27 =>
      rename_i inst context state function arguments values x2 body callee returnShape x1 hClock entry entryContext postContext value hshape snd x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      rw [if_pos hshape]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      simp only [FiniteEvalContext.toExact,
        PanSemExactEvalContext.withState_state]
      congr 1
  | case28 =>
      rename_i inst context state function arguments values x2 body callee returnShape x1 hClock entry entryContext postContext value hshape kind name snd hvalid x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      rw [if_pos hshape]
      rw [if_pos (show isValidValueHOLExact context.toExact.state kind name value = true from hvalid)]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      simp only [FiniteEvalContext.toExact, PanSemExactEvalContext.withState_state,
        FiniteEvalContext.withState_state, callSetKvarContextHOLFinite]
      rw [toExact_setKvarHOLFinite]
      congr 1
  | case29 =>
      rename_i inst context state function arguments values x2 body callee returnShape x1 hClock entry entryContext postContext value hshape kind name snd hvalid x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      rw [if_pos hshape]
      rw [if_neg (show ¬(isValidValueHOLExact context.toExact.state kind name value = true) from hvalid)]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      have hfix := callFixedContextHOLFinite_toExact context callee postContext
        (some (PanSemResultExact.returned value))
      exact hfix
  | case30 =>
      rename_i inst context state info function arguments values x2 body callee returnShape x1 hClock entry entryContext postContext value hshape x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      rw [if_neg hshape]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      have hfix := callFixedContextHOLFinite_toExact context callee postContext
        (some (PanSemResultExact.returned value))
      exact hfix
  | case31 =>
      rename_i inst context state function arguments values x2 body callee returnShape x1 hClock entry entryContext postContext exceptionId value x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      simp only [FiniteEvalContext.toExact,
        PanSemExactEvalContext.withState_state]
      congr 1
  | case32 =>
      rename_i inst context state function arguments values x2 body callee returnShape x1 hClock entry entryContext postContext exceptionId value fst x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      simp only [FiniteEvalContext.toExact,
        PanSemExactEvalContext.withState_state]
      congr 1
  | case33 =>
      rename_i inst context state function arguments values x3 body callee returnShape x2 hClock entry entryContext postContext value fst handlerId handlerVar handlerProgram shape hcond x1 x fixedContext handlerContext ih2 ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x3
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x2
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih2, x]
      simp only [Option.map_some]
      simp only [if_true]
      rw [show context.toExact.state.eshapes = context.state.eshapes.lookup from rfl]
      rw [x1]
      simp only []
      rw [if_pos (show (shapeEqHOL (shapeOfHOLExact value) shape && isValidValueHOLExact context.toExact.state VarKind.local handlerVar value) = true from hcond)]
      have hfix := callFixedContextHOLFinite_toExact context callee postContext
        (some (PanSemResultExact.exception handlerId value))
      have hctx : (Flapjack.callFixedContextHOLExact (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup)
            (some (PanSemResultExact.exception handlerId value)) postContext.toExact).withState
          (Flapjack.handlerStateHOLExact context.toExact
            (Flapjack.callFixedContextHOLExact (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup)
              (some (PanSemResultExact.exception handlerId value)) postContext.toExact)
            handlerVar value) rfl rfl = handlerContext.toExact := by
        apply PanSemExactEvalContext.ext
        simp only [FiniteEvalContext.toExact, PanSemExactEvalContext.withState_state]
        exact (toExact_handlerStateHOLFinite context fixedContext _ hfix handlerVar value).symm
      rw [hctx]
      exact ih1
  | case34 =>
      rename_i inst context state function arguments values x3 body callee returnShape x2 hClock entry entryContext postContext value fst handlerId handlerVar handlerProgram shape hcond x1 x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x3
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x2
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      simp only [if_true]
      rw [show context.toExact.state.eshapes = context.state.eshapes.lookup from rfl]
      rw [x1]
      simp only []
      rw [if_neg (show ¬(shapeEqHOL (shapeOfHOLExact value) shape && isValidValueHOLExact context.toExact.state VarKind.local handlerVar value) = true from hcond)]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      have hfix := callFixedContextHOLFinite_toExact context callee postContext
        (some (PanSemResultExact.exception handlerId value))
      exact hfix
  | case35 =>
      rename_i inst context state function arguments values x3 body callee returnShape x2 hClock entry entryContext postContext value fst handlerId handlerVar handlerProgram x1 x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x3
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x2
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      simp only [if_true]
      rw [show context.toExact.state.eshapes = context.state.eshapes.lookup from rfl]
      rw [x1]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      have hfix := callFixedContextHOLFinite_toExact context callee postContext
        (some (PanSemResultExact.exception handlerId value))
      exact hfix
  | case36 =>
      rename_i inst context state function arguments values x2 body callee returnShape x1 hClock entry entryContext postContext exceptionId value fst handlerId handlerVar handlerProgram hne x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      rw [if_neg hne]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      simp only [FiniteEvalContext.toExact,
        PanSemExactEvalContext.withState_state]
      congr 1
  | case37 =>
      rename_i inst context state info function arguments values x6 body callee returnShape x5 hClock entry entryContext postContext other x4 x3 x2 x1 x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_5]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x6
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x5
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      simp only [FiniteEvalContext.toExact,
        PanSemExactEvalContext.withState_state]
      congr 1
  | case38 =>
      rename_i inst context state resultName shape function arguments continuation x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = none := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x
      simp only [hargs, Option.map_some]
  | case39 =>
      rename_i inst context state resultName shape function arguments continuation values x1 x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x1
      have hl : lookupCodeHOLExact context.state.code.lookup function values = none :=
        (lookupCodeHOLFinite_eq_none_iff (code := context.state.code.lookup) (fname := function) (values := values)).mp x
      simp only [hargs, hl, Option.map_some]
  | case40 =>
      rename_i inst context state resultName shape function arguments continuation values x1 body callee returnShape x h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x1
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x
      simp only [hargs, hl]
      have hclock' : context.toExact.state.clock = 0 := h
      rw [if_pos hclock']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      change emptyLocalsHOLExact context.state.toExact = (emptyLocalsHOLFinite context.state).toExact
      rw [toExact_emptyLocalsHOLFinite]
  | case41 =>
      rename_i inst context state resultName shape function arguments continuation values x2 body callee returnShape x1 hClock entry entryContext x ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_none]
  | case42 =>
      rename_i inst context state resultName shape function arguments continuation values x2 body callee returnShape x1 hClock entry entryContext postContext x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      have hfix := callFixedContextHOLFinite_toExact context callee postContext none
      exact hfix
  | case43 =>
      rename_i inst context state resultName shape function arguments continuation values x2 body callee returnShape x1 hClock entry entryContext postContext x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      have hfix := callFixedContextHOLFinite_toExact context callee postContext (some PanSemResultExact.break)
      exact hfix
  | case44 =>
      rename_i inst context state resultName shape function arguments continuation values x2 body callee returnShape x1 hClock entry entryContext postContext x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      have hfix := callFixedContextHOLFinite_toExact context callee postContext (some PanSemResultExact.continue)
      exact hfix
  | case45 =>
      rename_i inst context state resultName shape function arguments continuation values x3 body callee returnShape x2 hClock entry entryContext postContext value hshape x1 fixedContext continuationContext x ih2 ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x3
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x2
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih2, x1]
      simp only [Option.map_some]
      rw [if_pos hshape]
      rw [← toExact_callContinuationContextHOLFinite context fixedContext
        (Flapjack.callFixedContextHOLExact (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup)
          (some (PanSemResultExact.returned value)) postContext.toExact)
        (callFixedContextHOLFinite_toExact context callee postContext (some (PanSemResultExact.returned value)))
        resultName value]
      rw [← ih1, x]
      simp only [Option.map_none]
  | case46 =>
      rename_i inst context state resultName shape function arguments continuation values x3 body callee returnShape x2 hClock entry entryContext postContext1 value hshape result postContext restored x1 fixedContext continuationContext x ih2 ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x3
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x2
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih2, x1]
      simp only [Option.map_some]
      rw [if_pos hshape]
      rw [← toExact_callContinuationContextHOLFinite context fixedContext
        (Flapjack.callFixedContextHOLExact (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup)
          (some (PanSemResultExact.returned value)) postContext1.toExact)
        (callFixedContextHOLFinite_toExact context callee postContext1 (some (PanSemResultExact.returned value)))
        resultName value]
      rw [← ih1, x]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      simp only [FiniteEvalContext.toExact, PanSemExactEvalContext.withState_state]
      change ({ postContext.state with
          locals := HolFiniteMapExact.resVarEq postContext.state.locals
            (resultName, context.state.locals.lookup resultName) } :
          PanSemStateFiniteExact width σ).toExact =
        { postContext.toExact.state with
          locals := resVarHOLExact postContext.toExact.state.locals
            (resultName, context.toExact.state.locals resultName) }
      rw [toExact_resVarEq_locals]
      congr 1
  | case47 =>
      rename_i inst context state resultName shape function arguments continuation values x2 body callee returnShape x1 hClock entry entryContext postContext value hshape x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x2
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x1
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      rw [if_neg hshape]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      have hfix := callFixedContextHOLFinite_toExact context callee postContext (some (PanSemResultExact.returned value))
      exact hfix
  | case48 =>
      rename_i inst context state resultName shape function arguments continuation values x5 body callee returnShape x4 hClock entry entryContext postContext other x3 x2 x1 x fixedContext ih1
      rw [evalPanSemRecursiveCallContextHOLExact.eq_6]
      rw [show (FiniteEvalContext.toExact context).state.code = context.state.code.lookup from rfl]
      have hargs : @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable arguments = some values := by
        rw [evalListHOLExact_toExact_eq context arguments]; exact x5
      have hl : lookupCodeHOLExact context.state.code.lookup function values = some (body, callee.lookup, returnShape) :=
        lookupCodeHOLFinite_eq_some context.state.code.lookup function values body callee returnShape x4
      simp only [hargs, hl]
      have hclock' : ¬(context.toExact.state.clock = 0) := hClock
      rw [if_neg hclock']
      generalize hentb : context.toExact.withState (Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup) rfl rfl = entb
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
      rw [hentb_eq, ← ih1, x]
      simp only [Option.map_some]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      simp only [FiniteEvalContext.toExact, FiniteEvalContext.withState,
        PanSemExactEvalContext.withState_state, toExact_emptyLocalsHOLFinite]
      congr 1
  | case49 =>
      rename_i inst context
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      simp only [Option.map_some]
  | case50 =>
      rename_i inst context
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      simp only [Option.map_some]
  | case51 =>
      rename_i inst context
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      simp only [Option.map_some]
  | case52 =>
      rename_i inst context tag text
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      simp only [Option.map_some]
  | case53 =>
      rename_i inst context state h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have h' : context.toExact.state.clock = 0 := h
      rw [if_pos h']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      change emptyLocalsHOLExact context.state.toExact = (emptyLocalsHOLFinite context.state).toExact
      rw [toExact_emptyLocalsHOLFinite]
  | case54 =>
      rename_i inst context state h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have h' : ¬(context.toExact.state.clock = 0) := h
      rw [if_neg h']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      change decClockHOLExact context.state.toExact = (decClockHOLFinite context.state).toExact
      rw [toExact_decClockHOLFinite]
  | case55 =>
      rename_i inst context state value x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable value = none := by
        rw [evalHOLExact_toExact_eq context value]
        exact x
      simp only [hx]
      simp only [Option.map_some]
  | case56 =>
      rename_i inst context state value1 value x h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable value1 = some value := by
        rw [evalHOLExact_toExact_eq context value1]
        exact x
      simp only [hx]
      have h' : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.toExact.state.structs
          (shapeOfHOLExact value) ≤ 32 := h
      rw [if_pos h']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      change emptyLocalsHOLExact context.state.toExact = (emptyLocalsHOLFinite context.state).toExact
      rw [toExact_emptyLocalsHOLFinite]
  | case57 =>
      rename_i inst context state value1 value x h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable value1 = some value := by
        rw [evalHOLExact_toExact_eq context value1]
        exact x
      simp only [hx]
      have h' : ¬(Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.toExact.state.structs
          (shapeOfHOLExact value) ≤ 32) := h
      rw [if_neg h']
      simp only [Option.map_some]
  | case58 =>
      rename_i inst context state exception value x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable value = none := by
        rw [evalHOLExact_toExact_eq context value]
        exact x
      simp only [hx]
      simp only [Option.map_some]
  | case59 =>
      rename_i inst context state exception value1 value x1 x
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable value1 = some value := by
        rw [evalHOLExact_toExact_eq context value1]
        exact x1
      simp only [hx]
      rw [show context.toExact.state.eshapes = context.state.eshapes.lookup from rfl, x]
      simp only [Option.map_some]
  | case60 =>
      rename_i inst context state exception value1 value x1 shape x h1 h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable value1 = some value := by
        rw [evalHOLExact_toExact_eq context value1]
        exact x1
      simp only [hx]
      rw [show context.toExact.state.eshapes = context.state.eshapes.lookup from rfl, x]
      simp only []
      have h' : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.toExact.state.structs
          (shapeOfHOLExact value) ≤ 32 := h
      rw [if_pos h1, if_pos h']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      apply PanSemExactEvalContext.ext
      change emptyLocalsHOLExact context.state.toExact = (emptyLocalsHOLFinite context.state).toExact
      rw [toExact_emptyLocalsHOLFinite]
  | case61 =>
      rename_i inst context state exception value1 value x1 shape x h1 h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable value1 = some value := by
        rw [evalHOLExact_toExact_eq context value1]
        exact x1
      simp only [hx]
      rw [show context.toExact.state.eshapes = context.state.eshapes.lookup from rfl, x]
      simp only []
      have h' : ¬(Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.toExact.state.structs
          (shapeOfHOLExact value) ≤ 32) := h
      rw [if_pos h1, if_neg h']
      simp only [Option.map_some]
  | case62 =>
      rename_i inst context state exception value1 value x1 shape x h
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      have hx : @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable value1 = some value := by
        rw [evalHOLExact_toExact_eq context value1]
        exact x1
      simp only [hx]
      rw [show context.toExact.state.eshapes = context.state.eshapes.lookup from rfl, x]
      simp only []
      rw [if_neg h]
      simp only [Option.map_some]
  | case63 =>
      rename_i inst context state size kind name address evalExpression output
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      simp only [Option.map_some, Option.some.injEq]
      refine congrArg (fun c => (output.1, c)) ?_
      apply PanSemExactEvalContext.ext
      rfl
  | case64 =>
      rename_i inst context state size address value evalExpression output
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      simp only []
      simp only [Option.map_some, Option.some.injEq]
      refine congrArg (fun c => (output.1, c)) ?_
      apply PanSemExactEvalContext.ext
      rfl
  | case65 =>
      rename_i inst context state other x14 x13 x12 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 hres
      cases other <;> simp_all [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
      · exfalso; exact (x14 _ _ _ _ rfl rfl rfl) rfl
      · exfalso; exact (x9 _ _ _ _ _ rfl rfl rfl rfl) rfl
  | case66 =>
      rename_i inst context state other x14 x13 x12 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 pair hres
      rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
      cases other with
      | dec name shape initializer body => exact (x14 name shape initializer body rfl).elim
      | seq first second => exact (x13 first second rfl).elim
      | ite condition thenBranch elseBranch => exact (x12 condition thenBranch elseBranch rfl).elim
      | «while» condition body => exact (x11 condition body rfl).elim
      | call info function arguments => exact (x10 info function arguments rfl).elim
      | decCall resultName shape function arguments continuation =>
          exact (x9 resultName shape function arguments continuation rfl).elim
      | skip => exact (x8 rfl).elim
      | «break» => exact (x7 rfl).elim
      | «continue» => exact (x6 rfl).elim
      | annot tag text => exact (x5 tag text rfl).elim
      | tick => exact (x4 rfl).elim
      | «return» value => exact (x3 value rfl).elim
      | raise exception value => exact (x2 exception value rfl).elim
      | shMemLoad size kind name address => exact (x1 size kind name address rfl).elim
      | shMemStore size address value => exact (x0 size address value rfl).elim
      | assign kind name value =>
          simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact] at hres
          simp only [Option.some.injEq] at hres
          cases hres
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          refine ⟨rfl, ?_⟩
          apply PanSemExactEvalContext.ext
          simp only [FiniteEvalContext.toExact_withState,
            PanSemExactEvalContext.withState_state, toExact_ofExact]
          rfl
      | primitive name operator args =>
          simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact] at hres
          simp only [Option.some.injEq] at hres
          cases hres
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          refine ⟨rfl, ?_⟩
          apply PanSemExactEvalContext.ext
          simp only [FiniteEvalContext.toExact_withState,
            PanSemExactEvalContext.withState_state, toExact_ofExact]
          rfl
      | store address value =>
          simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact] at hres
          simp only [Option.some.injEq] at hres
          cases hres
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          refine ⟨rfl, ?_⟩
          apply PanSemExactEvalContext.ext
          simp only [FiniteEvalContext.toExact_withState,
            PanSemExactEvalContext.withState_state, toExact_ofExact]
          rfl
      | store32 address value =>
          simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact] at hres
          simp only [Option.some.injEq] at hres
          cases hres
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          refine ⟨rfl, ?_⟩
          apply PanSemExactEvalContext.ext
          simp only [FiniteEvalContext.toExact_withState,
            PanSemExactEvalContext.withState_state, toExact_ofExact]
          rfl
      | storeByte address value =>
          simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact] at hres
          simp only [Option.some.injEq] at hres
          cases hres
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          refine ⟨rfl, ?_⟩
          apply PanSemExactEvalContext.ext
          simp only [FiniteEvalContext.toExact_withState,
            PanSemExactEvalContext.withState_state, toExact_ofExact]
          rfl
      | extCall function configuration configurationLength array arrayLength =>
          simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact] at hres
          simp only [Option.some.injEq] at hres
          cases hres
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          refine ⟨rfl, ?_⟩
          apply PanSemExactEvalContext.ext
          simp only [FiniteEvalContext.toExact_withState,
            PanSemExactEvalContext.withState_state, toExact_ofExact]
          rfl

end PanSemStateFiniteExact

namespace PanSemStateFiniteExact

/-- The finite evaluator's state-level wrapper projects to the broad exact
    evaluator. This connects the public finite-support wrapper to the
    clause-level projection proved above; it is Flapjack-specific
    infrastructure, not a tagged port of `evaluate_def`. -/
theorem evaluateHOLFinite_toExact {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (program : ProgHOL width) :
    (@evaluateHOLFinite width σ _ context.state context.memaddrsDecidable
      context.shMemaddrsDecidable program).map
        (fun pair => (pair.1, pair.2.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact program context.toExact).map
        (fun pair => (pair.1, pair.2.state)) := by
  unfold evaluateHOLFinite
  simp only [Option.map_map]
  change Option.map (fun pair => (pair.1, pair.2.state.toExact))
      (evalPanSemRecursiveCallFiniteContext program context) =
    Option.map (fun pair => (pair.1, pair.2.state))
      (evalPanSemRecursiveCallContextHOLExact program context.toExact)
  have hproj := evalPanSemRecursiveCallFiniteContext_projection program context
  rw [← hproj]
  simp only [Option.map_map]
  rfl

/-- Flapjack-specific finite result-pair bridge: a successful broad recursive
    evaluator result is represented by the canonical finite context evaluator
    with the same result option and an exactly projecting post-state. The
    finite-to-broad recursive projection supplies the result equality; the
    state-level wrapper then returns that finite post-state. This helper has no
    standalone HOL declaration and adds no semantic premise. -/
theorem evaluateHOLFiniteState_of_broadContext {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ)
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
    (hb : evalPanSemRecursiveCallContextHOLExact program context.toExact = some output) :
    ∃ pair : Option (PanSemResultExact width) × FiniteEvalContext width σ,
      evalPanSemRecursiveCallFiniteContext program context = some pair ∧
      pair.1 = output.1 ∧ pair.2.state.toExact = output.2.state ∧
      evaluateHOLFiniteState context.state program = (pair.1, pair.2.state) := by
  have hprojection := evalPanSemRecursiveCallFiniteContext_projection program context
  rw [hb] at hprojection
  cases hfinite : evalPanSemRecursiveCallFiniteContext program context with
  | none => simp [hfinite] at hprojection
  | some pair =>
      have hpair : (pair.1, pair.2.toExact) = output := by
        simpa [hfinite] using hprojection
      refine ⟨pair, rfl, congrArg Prod.fst hpair,
        congrArg (fun result => result.2.state) hpair, ?_⟩
      exact evaluateHOLFiniteState_eq_of_recursiveContext context.state program
        context rfl pair hfinite

end PanSemStateFiniteExact

end Flapjack
