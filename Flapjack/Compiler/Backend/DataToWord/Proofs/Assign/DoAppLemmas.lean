module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFields
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame

@[expose] public section

/-!
# Source `do_app` lemmas of `data_to_word_assignProofScript.sml`

Facts about the data semantics' primitive application used by the
assignment simulations. HOL `OPTION_MAP2` is `Option.map₂`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem

/-- Space accounting keeps the stack bound fields and the limits. Flapjack
infrastructure. -/
theorem doSpace_stackFields {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (run : doSpace op args state = some next) :
    next.stackMax = state.stackMax ∧ next.limits = state.limits ∧
      next.stack = state.stack ∧ next.localsSize = state.localsSize ∧
      next.stackFrameSizes = state.stackFrameSizes := by
  unfold doSpace at run
  split at run
  · simp only [Option.some.injEq] at run
    subst next
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only at run
    split at run
    · simp only [Option.some.injEq] at run
      subst next
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [consumeSpace] at run
      split at run
      · simp at run
      · simp only [Option.some.injEq] at run
        subst next
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The stack bound after a successful `FromList`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "do_app_FromList_stack_max"]
theorem doApp_fromList_stackMax {C F : Type} (tag : Nat) (vals : List Value) (s s' : State C F)
    (v : Value) (h : doApp (.blockOp (.fromList tag)) vals s = .val (v, s')) :
    s'.stackMax = Option.map₂ max s.stackMax
      (Option.map₂ (· + ·) (stackConsumed s.stackFrameSizes s.limits (.blockOp (.fromList tag)) vals)
        (Option.map₂ (· + ·) (sizeOfStack s.stack) s.localsSize)) := by
  simp only [doApp] at h
  cases hsp : doSpace (.blockOp (.fromList tag)) vals s with
  | none => simp [hsp] at h
  | some next =>
    simp only [hsp] at h
    obtain ⟨-, -, hmax, -⟩ := doAppAux_fieldFrame _ _ _ _ _ h
    obtain ⟨m, l, st, ls, fs⟩ := doSpace_stackFields _ _ _ _ hsp
    rw [hmax]
    simp [doStack, doLimSafe, m, l, st, ls, fs]

/-- A successful `FromList` on a decoded list builds that block and changes
only space, timestamps and the safety and stack observations. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "do_app_FromList_eq"]
theorem doApp_fromList_eq {C F : Type} (tag : Nat) (v2 v : Value) (ys : List Value)
    (s s' : State C F)
    (h : valueToList v2 = some ys ∧
      doApp (.blockOp (.fromList tag)) [.number (ys.length : Int), v2] s = .val (v, s')) :
    (∃ ts', v = .block ts' tag ys) ∧ s'.space = 0 ∧
      s'.refs = s.refs ∧ s'.code = s.code ∧ s'.ffi = s.ffi ∧ s'.handler = s.handler ∧
      s'.locals = s.locals ∧ s'.stack = s.stack ∧ s'.limits = s.limits ∧
      s'.stackFrameSizes = s.stackFrameSizes ∧ s'.localsSize = s.localsSize ∧
      s'.global = s.global ∧ s'.compile = s.compile ∧ s'.compileOracle = s.compileOracle ∧
      s'.clock = s.clock ∧
      s'.tstamps = (if ys = [] then s.tstamps else s.tstamps.map Nat.succ) := by
  obtain ⟨hv, h⟩ := h
  simp only [doApp] at h
  cases hsp : doSpace (.blockOp (.fromList tag)) [.number (ys.length : Int), v2] s with
  | none => simp [hsp] at h
  | some next =>
    simp only [hsp] at h
    simp [doSpace, DataLang.opSpaceReset] at hsp
    subst hsp
    simp [doAppAux, applyNonFfi, hv, doStack, doLimSafe] at h
    by_cases hy : ys = []
    · subst hy
      simp only [if_true] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · cases ht : s.tstamps <;>
        simp [hy, withFreshTimestamp, checkLim, ht] at h <;>
        obtain ⟨rfl, rfl⟩ := h <;> simp [hy]

open Classical in
/-- Applying `AllocThunk` consumes two words of space and allocates a thunk at
the least unused reference (`LEAST ptr. ptr ∉ domain s1.refs` is the data
semantics' `leastUnusedRef`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "do_app_AllocThunk"]
theorem doApp_allocThunk {C F : Type} (m : AstHOL.ThunkMode) (v : Value) (x : State C F) :
    doApp (.thunkOp (.allocThunk m)) [v] x =
      match consumeSpace (1 + 1) x with
      | none => .err (.abort .typeError)
      | some s1 =>
        if badThunkUpdate m v s1.refs then .err (.abort .typeError) else
        .val (.refPtr false (leastUnusedRef s1.refs),
          { s1 with
            refs := sptInsert (leastUnusedRef s1.refs) (.thunk m v) s1.refs,
            safeForSpace := (doStack (.thunkOp (.allocThunk m)) [v]
              (doLimSafe s1 (.thunkOp (.allocThunk m)) [v])).safeForSpace,
            stackMax := (doStack (.thunkOp (.allocThunk m)) [v]
              (doLimSafe s1 (.thunkOp (.allocThunk m)) [v])).stackMax }) := by
  simp only [doApp, doSpace, DataLang.opSpaceReset]
  cases hc : consumeSpace (1 + 1) x with
  | none =>
    have hc2 : consumeSpace 2 x = none := hc
    simp [DataSpace.opSpaceReq, hc2]
  | some s1 =>
    simp only [DataSpace.opSpaceReq, doAppAux, applyNonFfi]
    simp only [doStack, doLimSafe]
    have hc2 : consumeSpace 2 x = some s1 := hc
    by_cases hb : badThunkUpdate m v s1.refs <;> simp [hb, hc2]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
