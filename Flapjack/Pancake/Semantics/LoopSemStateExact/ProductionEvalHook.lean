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

This module defines a candidate production adapter `loopMachineEvalHook` and
proves that it agrees with exact `LoopSemStateFiniteExact.eval` for every
`HolLoopExp` under `LoopSemStateFiniteExact.prodRel`; the constructor cases are
assembled in
`Flapjack.LoopSemStateFiniteExact.EvaluateCases.loopMachineEvalHook_holLoopExp_prodRel`.
The `Var` case preserves present word and location payloads as well as absent
locals. `Load` uses a recursive address premise, `Op` uses recursive premises
for every operand, and `Shift` uses premises for both children. These are
Flapjack-specific cross-carrier bridges between the exact finite-support
carrier and production carrier; none ports a HOL declaration, so they
intentionally carry no `@[hol]` tag. The candidate adapter's wiring to an
executed caller remains open.
-/

namespace Flapjack

/-- Untagged bridge: a production `LoopValue` cell viewed as the exact `WordLocW`
    cell; the payload is carried unchanged. -/
def loopValueToWordLocW {width : Nat} [NeZero width] :
    LoopValue (BitVec width) → WordLocW width
  | .word value => .word value
  | .loc identifier offset => .loc identifier offset

/-- Candidate production adapter for the `LoopEvaluateHooks.eval` field, at the
    `LoopMachineState`/`LoopValue` carrier. It is the proposed executable
    counterpart of the exact `LoopSemStateFiniteExact.eval`: `Const` wraps the
    word, `Var` reads the local cell (word or location, or `none` when absent),
    `Lookup` reads globals, `Load` consults `mdomain`/`memory`, `Op`/`Shift`
    reuse the reviewed `wordOpHOL`/`wordShiftHOL`, and `BaseAddr`/`TopAddr`
    return the state's address bounds. The theorem
    `EvaluateCases.loopMachineEvalHook_holLoopExp_prodRel` proves the candidate
    agrees with exact `eval` for all faithful expression constructors under
    `prodRel`.

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

/-- The production `Lookup` hook agrees with exact `eval` for every result,
    including a missing global and either `WordLocW` payload. This is exactly
    the globals lookup conjunct of `prodRel`; no desired hook equation is
    assumed. Flapjack-only cross-carrier bridge, with no `@[hol]` tag. -/
theorem loopMachineEvalHook_lookup_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (name : BitVec 5) :
    loopMachineEvalHook machine (holLoopExpToExecutable (.lookup name)) =
      (LoopSemStateFiniteExact.eval state (.lookup name)).map loopValueOfWordLocW := by
  have hglobals := hrel.2.1 name
  simpa [holLoopExpToExecutable, LoopSemStateFiniteExact.eval, loopMachineEvalHook] using hglobals

/-- The production `Load` hook agrees with exact `eval` when the address
    expression agrees under the recursive premise. The proof derives its cases
    from that premise and `prodRel`: failure or a location-valued address gives
    `none`; a word address outside `mdomain` gives `none`; an in-domain word
    address returns the related memory cell, preserving either its word or
    location payload. The premise is the genuine strict-subexpression IH for
    `address`, not an assumed equation for the `Load` expression. Flapjack-only
    cross-carrier bridge, with no `@[hol]` tag. -/
theorem loopMachineEvalHook_load_prodRel_of_ih {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (address : HolLoopExp width)
    (haddress :
      loopMachineEvalHook machine (holLoopExpToExecutable address) =
        (LoopSemStateFiniteExact.eval state address).map loopValueOfWordLocW) :
    loopMachineEvalHook machine (holLoopExpToExecutable (.load address)) =
      (LoopSemStateFiniteExact.eval state (.load address)).map loopValueOfWordLocW := by
  cases heval : LoopSemStateFiniteExact.eval state address with
  | none =>
      have hhook : loopMachineEvalHook machine (holLoopExpToExecutable address) = none := by
        simpa [heval] using haddress
      simp [holLoopExpToExecutable, loopMachineEvalHook,
        LoopSemStateFiniteExact.eval, heval, hhook]
  | some value =>
      cases value with
      | loc identifier offset =>
          have hhook :
              loopMachineEvalHook machine (holLoopExpToExecutable address) =
                some (.loc identifier offset) := by
            simpa [heval, loopValueOfWordLocW] using haddress
          simp [holLoopExpToExecutable, loopMachineEvalHook,
            LoopSemStateFiniteExact.eval, heval, hhook]
      | word word =>
          have hhook :
              loopMachineEvalHook machine (holLoopExpToExecutable address) =
                some (.word word) := by
            simpa [heval, loopValueOfWordLocW] using haddress
          rcases hrel with
            ⟨_, _, hmemory, hmdomain, _, _, _, _, _, _, _, _⟩
          simp only [holLoopExpToExecutable, loopMachineEvalHook, hhook,
            LoopSemStateFiniteExact.eval, heval]
          rw [hmdomain]
          by_cases hdomain : state.mdomain word
          · cases hcell : state.memory word <;>
              simp [LoopSemStateFiniteExact.memLoad, hmemory word, hcell,
                loopValueOfWordLocW, hdomain]
          · simp [LoopSemStateFiniteExact.memLoad, hdomain]

/-- The production `BaseAddr` hook agrees with exact `eval` under `prodRel`.
    The equation follows from the base-address conjunct and preserves the
    width-indexed word payload. Flapjack-only cross-carrier bridge, with no
    `@[hol]` tag. -/
theorem loopMachineEvalHook_baseAddr_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) :
    loopMachineEvalHook machine (holLoopExpToExecutable (.baseAddr : HolLoopExp width)) =
      (LoopSemStateFiniteExact.eval state .baseAddr).map loopValueOfWordLocW := by
  rcases hrel with ⟨_, _, _, _, _, _, _, _, hbaseAddr, _, _, _⟩
  simp [holLoopExpToExecutable, loopMachineEvalHook,
    LoopSemStateFiniteExact.eval, loopValueOfWordLocW, hbaseAddr]

/-- The production `TopAddr` hook agrees with exact `eval` under `prodRel`.
    The equation follows from the top-address conjunct and preserves the
    width-indexed word payload. Flapjack-only cross-carrier bridge, with no
    `@[hol]` tag. -/
theorem loopMachineEvalHook_topAddr_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) :
    loopMachineEvalHook machine (holLoopExpToExecutable (.topAddr : HolLoopExp width)) =
      (LoopSemStateFiniteExact.eval state .topAddr).map loopValueOfWordLocW := by
  rcases hrel with ⟨_, _, _, _, _, _, _, _, _, htopAddr, _, _⟩
  simp [holLoopExpToExecutable, loopMachineEvalHook,
    LoopSemStateFiniteExact.eval, loopValueOfWordLocW, htopAddr]

end Flapjack
