import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production Loop expression `eval` hook

The production `evaluateLoop` (`Flapjack/Pancake/Semantics/LoopSem.lean`) calls
its `LoopEvaluateHooks.eval` field from the `assign`, `store`, and `setGlobal`
branches.  That field is deliberately abstract, but the executed production path
must supply a faithful adapter over `LoopMachineState` that preserves the whole
`LoopValue` cell (a word or a location).  The word-only fixture `evalHook` in
`Flapjack/Test/LoopLiveEffectFreeParity.lean` drops `.loc` payloads outright and
is documented there as *not* that adapter; likewise the legacy word-valued
`Flapjack.evalLoopExpSource` (`Flapjack/LoopSemantics.lean`) cannot carry a
location in its `LoopState` locals/memory, so it is not a faithful `loopSem$eval`
adapter either.

This module defines the faithful production adapter `loopMachineEvalHook` and
proves that, under the exact/production state relation
`LoopSemStateFiniteExact.prodRel`, it agrees with the exact
`LoopSemStateFiniteExact.eval` on the `HolLoopExp.const` and `.var` expressions
carried across by `holLoopExpToExecutable`.  The `Var` statement covers a present
word-valued local, a present location-valued local, and an absent local, i.e. the
complete word/location payload, and it is derived from the `prodRel` local-lookup
conjunct rather than assumed as a hook equation.

These are Flapjack-specific cross-carrier bridge declarations relating the exact
finite-support HOL-shaped carrier to the production executable carrier; none of
them ports a HOL declaration, so they intentionally carry no `@[hol]` tag.
-/

namespace Flapjack

/-- Untagged bridge: a production `LoopValue` cell viewed as the exact `WordLocW`
    cell; the payload is carried unchanged. -/
def loopValueToWordLocW {width : Nat} [NeZero width] :
    LoopValue (BitVec width) → WordLocW width
  | .word value => .word value
  | .loc identifier offset => .loc identifier offset

/-- Faithful production adapter for the `LoopEvaluateHooks.eval` field, at the
    executed `LoopMachineState`/`LoopValue` carrier.  It is the executable
    counterpart of the exact `LoopSemStateFiniteExact.eval`: `Const` wraps the
    word, `Var` reads the local cell (word or location, or `none` when absent),
    `Lookup` reads globals, `Load` consults `mdomain`/`memory`, `Op`/`Shift`
    reuse the reviewed `wordOpHOL`/`wordShiftHOL`, and `BaseAddr`/`TopAddr`
    return the state's address bounds.

    Only the `crepOp`/`cmp` constructors, which the executable `LoopExp` adds but
    the faithful `HolLoopExp` does not contain, have no source counterpart and
    return `none`; they are never produced by `holLoopExpToExecutable`.  This is
    Flapjack-only carrier infrastructure, not a separate HOL definition. -/
def loopMachineEvalHook {width : Nat} [NeZero width] {F : Type}
    (state : LoopMachineState (BitVec width) F) :
    LoopExp (BitVec width) → Option (LoopValue (BitVec width))
  | .const value => some (.word value)
  | .var name => state.locals name
  | .lookup address => state.globals address
  | .load address =>
      match loopMachineEvalHook state address with
      | some (.word word) =>
          if state.mdomain word then state.memory word else none
      | _ => none
  | .op operator args =>
      match theWords (args.attach.map fun ⟨e, _⟩ =>
          (loopMachineEvalHook state e).map loopValueToWordLocW) with
      | some values => (wordOpHOL operator values).map LoopValue.word
      | none => none
  | .shift operator left right =>
      match loopMachineEvalHook state left, loopMachineEvalHook state right with
      | some (.word leftWord), some (.word rightWord) =>
          (wordShiftHOL operator leftWord rightWord.toNat).map LoopValue.word
      | _, _ => none
  | .crepOp _ _ => none
  | .cmp _ _ _ => none
  | .baseAddr => some (.word state.baseAddr)
  | .topAddr => some (.word state.topAddr)

/-- `Const`: the executed hook wraps the word, exactly as `loopSem$eval`. -/
@[simp] theorem loopMachineEvalHook_const {width : Nat} [NeZero width] {F : Type}
    (state : LoopMachineState (BitVec width) F) (value : BitVec width) :
    loopMachineEvalHook state (.const value) = some (.word value) := by
  simp [loopMachineEvalHook]

/-- `Var`: the executed hook returns the local cell verbatim, so a word or a
    location payload (and a missing local's `none`) are all preserved. -/
@[simp] theorem loopMachineEvalHook_var {width : Nat} [NeZero width] {F : Type}
    (state : LoopMachineState (BitVec width) F) (name : Nat) :
    loopMachineEvalHook state (.var name) = state.locals name := by
  simp [loopMachineEvalHook]

/-- The executed `hooks.eval` agrees with exact `eval` on `Const` through
    `holLoopExpToExecutable`, for every word payload.  The state relation is
    unused: `Const` is a constant on both carriers. -/
theorem loopMachineEvalHook_const_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (_hrel : state.prodRel machine) (value : BitVec width) :
    loopMachineEvalHook machine (holLoopExpToExecutable (.const value)) =
      (LoopSemStateFiniteExact.eval state (.const value)).map loopValueOfWordLocW := by
  simp [holLoopExpToExecutable, LoopSemStateFiniteExact.eval, loopValueOfWordLocW]

/-- The executed `hooks.eval` agrees with exact `eval` on `Var` through
    `holLoopExpToExecutable`, for every state satisfying `prodRel`.  The
    agreement is exactly the `locals` conjunct of `prodRel`: a present local (word
    or location) is returned unchanged and an absent local yields `none` on both
    sides. -/
theorem loopMachineEvalHook_var_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (name : Nat) :
    loopMachineEvalHook machine (holLoopExpToExecutable (.var name)) =
      (LoopSemStateFiniteExact.eval state (.var name)).map loopValueOfWordLocW := by
  have hlocal := hrel.1 name
  simpa [holLoopExpToExecutable, LoopSemStateFiniteExact.eval] using hlocal

/-- `Var` with a present word-valued local: the executed hook returns that word
    cell. -/
theorem loopMachineEvalHook_var_word_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) {name : Nat} {word : BitVec width}
    (hlookup : sptLookup name state.locals = some (.word word)) :
    loopMachineEvalHook machine (.var name) = some (.word word) := by
  have hlocal := hrel.1 name
  rw [hlookup] at hlocal
  simpa [loopMachineEvalHook, holLoopExpToExecutable, loopValueOfWordLocW] using hlocal

/-- `Var` with a present location-valued local: the executed hook returns that
    location cell unchanged (the `.loc` payload the word-only fixtures drop). -/
theorem loopMachineEvalHook_var_loc_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) {name identifier offset : Nat}
    (hlookup : sptLookup name state.locals = some (.loc identifier offset)) :
    loopMachineEvalHook machine (.var name) = some (.loc identifier offset) := by
  have hlocal := hrel.1 name
  rw [hlookup] at hlocal
  simpa [loopMachineEvalHook, holLoopExpToExecutable, loopValueOfWordLocW] using hlocal

/-- `Var` with an absent local: the executed hook returns `none`, matching the
    exact `sptree$lookup` miss. -/
theorem loopMachineEvalHook_var_none_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) {name : Nat}
    (hlookup : sptLookup name state.locals = none) :
    loopMachineEvalHook machine (.var name) = none := by
  have hlocal := hrel.1 name
  rw [hlookup] at hlocal
  simpa [holLoopExpToExecutable] using hlocal

end Flapjack
