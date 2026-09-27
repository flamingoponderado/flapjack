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
exact one over `toExact`.  The general `fun_induction` projection equivalence
over every constructor is now proved (`evalPanSemRecursiveCallFiniteContext_projection`,
commit de0d2ff1e, `flapjack-6yq`); the exact
`@[hol ... "evaluate_def" ...]` tag stays withheld pending the coordinator's
source review of that theorem and its side conditions/carriers (`flapjack-qj5`,
`flapjack-6yq.1`).

The older delegating adapter `evaluateHOLFiniteViaExact` (and its
`evalPanSemRecursiveCallHOLFinite_of_broad` / `evaluateHOLFiniteViaExact_of_broad`
translation lemmas) remains as untagged Flapjack-specific infrastructure.

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
constructor is complete; only the coordinator's source review/`evaluate_def` tag
remain.
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
  rw [hlookupNone]

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
  rw [hlookupNone]

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
      some (some .timeOut, context.withState (emptyLocalsHOLFinite context.state) rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [hlookup]
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
      some (some .timeOut, context.withState (emptyLocalsHOLFinite context.state) rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  rw [if_pos hclock]

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
         toExact_setLocals])
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
          have hb : (context.withState (emptyLocalsHOLFinite context.state) rfl rfl).toExact =
              context.toExact.withState (emptyLocalsHOLExact context.state.toExact) rfl rfl := by
            apply PanSemExactEvalContext.ext
            change emptyLocalsHOLExact context.state.toExact =
              (emptyLocalsHOLFinite context.state).toExact
            rw [toExact_emptyLocalsHOLFinite]
          rw [hb]
          rfl
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
                          simp only [FiniteEvalContext.toExact,
                            PanSemExactEvalContext.withState_state,
                            FiniteEvalContext.withState_state]
                          rw [toExact_setKvarHOLFinite]
                          congr 1
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
          have hb : (context.withState (emptyLocalsHOLFinite context.state) rfl rfl).toExact =
              context.toExact.withState (emptyLocalsHOLExact context.state.toExact) rfl rfl := by
            apply PanSemExactEvalContext.ext
            change emptyLocalsHOLExact context.state.toExact =
              (emptyLocalsHOLFinite context.state).toExact
            rw [toExact_emptyLocalsHOLFinite]
          rw [hb]
          rfl
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
      rename_i inst context state info function arguments values x2 body callee returnShape x1 h entry entryContext x ih1
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
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
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
      have hentb_eq : entb = entryContext.toExact := by
        rw [← hentb]
        apply PanSemExactEvalContext.ext
        change (callEntryStateHOLFinite context.state callee).toExact = Flapjack.callEntryStateHOLExact context.toExact.state callee.lookup
        rw [toExact_callEntryStateHOLFinite]
        rfl
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
      simp only [FiniteEvalContext.toExact, FiniteEvalContext.withState,
        PanSemExactEvalContext.withState_state, toExact_emptyLocalsHOLFinite]
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
      simp only [FiniteEvalContext.toExact, FiniteEvalContext.withState,
        PanSemExactEvalContext.withState_state, toExact_setLocals]
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
        FiniteEvalContext.withState_state]
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
      simp only [FiniteEvalContext.toExact, FiniteEvalContext.withState,
        PanSemExactEvalContext.withState_state, toExact_emptyLocalsHOLFinite]
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
      simp only [FiniteEvalContext.toExact, FiniteEvalContext.withState,
        PanSemExactEvalContext.withState_state, toExact_emptyLocalsHOLFinite]
      congr 1
  | case33 =>
      rename_i inst context state function arguments values x3 body callee returnShape x2 hClock entry entryContext postContext value fst handlerId handlerVar handlerProgram shape hcond x1 x fixedContext handlerState handlerContext ih2 ih1
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
      simp only [FiniteEvalContext.toExact, FiniteEvalContext.withState,
        PanSemExactEvalContext.withState_state, toExact_emptyLocalsHOLFinite]
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
      simp only [FiniteEvalContext.toExact, FiniteEvalContext.withState,
        PanSemExactEvalContext.withState_state, toExact_emptyLocalsHOLFinite]
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

end PanSemStateFiniteExact

end Flapjack
