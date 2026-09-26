import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# Executed Crep `word_lab` evaluator bridge

This module relates the executed production Crep expression evaluator
`evalCrepRuntimeExpWordLab` at the canonical BitVec evaluator state derived
from a `CrepSemHOLState` to the exact HOL-tagged evaluator
`evalCrepSemHOLExp` (`crepSemScript.sml` `eval_def`).

The canonical BitVec evaluator state is `state.toBitVecEvaluatorState.toRuntime`
(see `executedCrepState`): `toBitVecEvaluatorState` projects the finite-map
fields of the exact carrier into the production `CrepHolState`, and
`CrepHolState.toRuntime` fixes the RISC-V word model (`panRiscVMemoryModelForEndian`)
and byte width. Every lemma below is Flapjack-specific infrastructure (no
`@[hol]` tag): it does not port a HOL declaration but discharges the
representation gap recorded by bead `flapjack-pxn.18.4.3.48.1`.

The scope is the memory-independent constructor fragment plus the `Const`
list path exercised by `evaluate_replicate_const`
(`pan_to_crepProofScript.sml:3051`); memory-reading constructors
(`load`, `load32`, `loadByte`) need the `mem_load_32`/`mem_load_byte`
reassembly correspondence and are tracked separately.
-/

namespace Flapjack

/-- Executed production runtime state obtained from the canonical BitVec
evaluator state of a `CrepSemHOLState`. -/
noncomputable def executedCrepState {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) : CrepRuntimeState (RiscV.Word width) Unit :=
  state.toBitVecEvaluatorState.toRuntime

/-- Bare-word projection of the exact `word_lab` cell. -/
def holWordLabToWord {width : Nat} [NeZero width] : HolWordLab width → BitVec width
  | .word value => value

/-- `Const`: the executed `word_lab` evaluator returns the exact `word_lab` cell. -/
theorem evalCrepRuntimeExpWordLab_executed_const {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs] (value : BitVec width) :
    evalCrepRuntimeExpWordLab (executedCrepState state) (CrepExp.const value) =
      (evalCrepSemHOLExp state (CrepExpHOL.const value)).map HolWordLab.toPanWordLab := by
  simp [evalCrepRuntimeExpWordLab, evalCrepSemHOLExp]

/-- `Var`: local lookup preserves the exact `word_lab` cell. -/
theorem evalCrepRuntimeExpWordLab_executed_var {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs] (name : Nat) :
    evalCrepRuntimeExpWordLab (executedCrepState state) (CrepExp.var name) =
      (evalCrepSemHOLExp state (CrepExpHOL.var name)).map HolWordLab.toPanWordLab := by
  simp [executedCrepState, CrepSemHOLState.toBitVecEvaluatorState, CrepHolState.toRuntime,
    evalCrepRuntimeExpWordLab, evalCrepSemHOLExp]

/-- `LoadGlob`: global lookup preserves the exact `word_lab` cell. -/
theorem evalCrepRuntimeExpWordLab_executed_loadGlob {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs] (address : BitVec 5) :
    evalCrepRuntimeExpWordLab (executedCrepState state) (CrepExp.loadGlob address) =
      (evalCrepSemHOLExp state (CrepExpHOL.loadGlob address)).map HolWordLab.toPanWordLab := by
  simp [executedCrepState, CrepSemHOLState.toBitVecEvaluatorState, CrepHolState.toRuntime,
    evalCrepRuntimeExpWordLab, evalCrepSemHOLExp]

/-- `BaseAddr`: the base address is carried unchanged into the `word_lab` cell. -/
theorem evalCrepRuntimeExpWordLab_executed_baseAddr {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs] :
    evalCrepRuntimeExpWordLab (executedCrepState state) CrepExp.baseAddr =
      (evalCrepSemHOLExp state CrepExpHOL.baseAddr).map HolWordLab.toPanWordLab := by
  simp [executedCrepState, CrepSemHOLState.toBitVecEvaluatorState, CrepHolState.toRuntime,
    evalCrepRuntimeExpWordLab, evalCrepSemHOLExp]

/-- `TopAddr`: the top address is carried unchanged into the `word_lab` cell. -/
theorem evalCrepRuntimeExpWordLab_executed_topAddr {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs] :
    evalCrepRuntimeExpWordLab (executedCrepState state) CrepExp.topAddr =
      (evalCrepSemHOLExp state CrepExpHOL.topAddr).map HolWordLab.toPanWordLab := by
  simp [executedCrepState, CrepSemHOLState.toBitVecEvaluatorState, CrepHolState.toRuntime,
    evalCrepRuntimeExpWordLab, evalCrepSemHOLExp]

/-- The `Const` list path used by `evaluate_replicate_const`: the executed
production `word_lab` list evaluator at the canonical BitVec evaluator state
returns the same replicated `word_lab` list that the tagged exact
`evalCrepSemHOLExp` produces. -/
theorem evalCrepRuntimeExpsWordLab_replicate_const_executed {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (n : Nat) (value : BitVec width) :
    evalCrepRuntimeExpsWordLab (executedCrepState state)
        (List.replicate n (CrepExp.const value)) =
      some (List.replicate n (PanWordLab.word value)) := by
  induction n with
  | zero => simp [evalCrepRuntimeExpsWordLab]
  | succ n ih =>
      simp only [List.replicate_succ, evalCrepRuntimeExpsWordLab]
      rw [ih]
      simp [evalCrepRuntimeExpWordLab]

end Flapjack
