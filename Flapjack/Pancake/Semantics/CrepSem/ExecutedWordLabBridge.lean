import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.FiniteMap

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

The scope is the memory-free fragment (`crepExpNoMemLoad` excludes only
`load`/`load32`/`loadByte`): `const`/`var`/`loadGlob`/`baseAddr`/`topAddr`,
the arithmetic hooks `op`/`crepOp`, and the comparisons `cmp`/`shift` all read
only their operands. This also covers the `Const` list path exercised by
`evaluate_replicate_const` (`pan_to_crepProofScript.sml:3051`).
`evalCrepRuntimeExp_executed_of_noMemLoad` proves the pointwise agreement for
that fragment. The memory-reading constructors (`load`, `load32`, `loadByte`)
still need the `mem_load_32`/`mem_load_byte` reassembly correspondence, tracked
separately under bead `flapjack-pxn.18.4.3.48.1.21`.
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

/-- Memory-independent Crep expressions: no `load`/`load32`/`loadByte`. The
arithmetic hooks `op`/`crepOp` and the value comparisons `cmp`/`shift` read
only their operands, so they are included whenever all subterms are
memory-independent. This is the fragment on which the executed production
evaluator and the exact `evalCrepSemHOLExp` are proved to agree below. -/
def crepExpNoMemLoad {width : Nat} [NeZero width] : CrepExp (BitVec width) → Prop
  | .const _ => True
  | .var _ => True
  | .load _ => False
  | .load32 _ => False
  | .loadByte _ => False
  | .loadGlob _ => True
  | .op _ args => ∀ a ∈ args, crepExpNoMemLoad a
  | .crepOp _ args => ∀ a ∈ args, crepExpNoMemLoad a
  | .cmp _ left right => crepExpNoMemLoad left ∧ crepExpNoMemLoad right
  | .shift _ left right => crepExpNoMemLoad left ∧ crepExpNoMemLoad right
  | .baseAddr => True
  | .topAddr => True

/-- Distribution of `Option.map` over `List.mapM`. -/
theorem list_mapM_mapOption {α β γ : Type} (f : α → Option β) (g : β → γ) :
    ∀ (xs : List α), xs.mapM (fun x => (f x).map g) = (xs.mapM f).map (List.map g) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, ih]
      cases h : f x with
      | none => simp
      | some y =>
          simp only [Option.map_some]
          cases hxs : List.mapM f xs <;> simp

/-- Reading a `HolWordLab` through the wrapper then the exact projection. -/
@[simp] theorem panTheWord_toPanWordLab {width : Nat} [NeZero width] (hw : HolWordLab width) :
    panTheWord hw.toPanWordLab = holWordLabToWord hw := by
  cases hw
  rfl

/-- `holWordLabToWord` is the underlying bit-vector projection. -/
@[simp] theorem holWordLabToWord_eq {width : Nat} [NeZero width] (hw : HolWordLab width) :
    holWordLabToWord hw = hw.1 := by
  cases hw
  rfl

/-- `holWordLabToWord` undoes `HolWordLab.word`, so the composite is the
identity on bare words. -/
@[simp] theorem option_map_holWordLabToWord_comp_word {width : Nat} [NeZero width]
    (o : Option (BitVec width)) :
    Option.map (holWordLabToWord ∘ HolWordLab.word) o = o := by
  cases o <;> rfl

/-- The executed production Crep evaluator at the canonical BitVec evaluator
state agrees with the tagged exact `evalCrepSemHOLExp`, for the memory-free
fragment (`const`/`var`/`loadGlob`/`baseAddr`/`topAddr`, `op`, `crepOp`,
`cmp`, `shift`). The exact value is read through the bare-word projection
`holWordLabToWord`, which is what the executed production evaluator returns. -/
theorem evalCrepRuntimeExp_executed_of_noMemLoad {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (e : CrepExp (BitVec width)) (hm : crepExpNoMemLoad e) :
    evalCrepRuntimeExp (executedCrepState state) e =
      (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord := by
  induction e using (CrepExp.rec (motive_2 := fun args =>
      ∀ e ∈ args, crepExpNoMemLoad e →
        evalCrepRuntimeExp (executedCrepState state) e =
          (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord))
  case nil e he hm =>
      exact absurd he (by simp)
  case cons head tail head_ih tail_ih e he hm =>
      rcases List.mem_cons.mp he with rfl | he
      · exact head_ih hm
      · exact tail_ih e he hm
  case const value =>
      simp [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL, holWordLabToWord]
  case var name =>
      simp only [executedCrepState, CrepSemHOLState.toBitVecEvaluatorState,
        CrepHolState.toRuntime, evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
      simp only [Option.map_map, Function.comp_def, panTheWord_toPanWordLab]
  case loadGlob address =>
      simp only [executedCrepState, CrepSemHOLState.toBitVecEvaluatorState,
        CrepHolState.toRuntime, evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
      simp only [Option.map_map, Function.comp_def, panTheWord_toPanWordLab]
  case baseAddr =>
      simp [executedCrepState, CrepSemHOLState.toBitVecEvaluatorState, CrepHolState.toRuntime,
        evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL, holWordLabToWord]
  case topAddr =>
      simp [executedCrepState, CrepSemHOLState.toBitVecEvaluatorState, CrepHolState.toRuntime,
        evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL, holWordLabToWord]
  case load address ih => simp only [crepExpNoMemLoad] at hm
  case load32 address ih => simp only [crepExpNoMemLoad] at hm
  case loadByte address ih => simp only [crepExpNoMemLoad] at hm
  case crepOp operator args ih =>
      simp only [crepExpNoMemLoad] at hm
      have hpoint : ∀ e ∈ args,
          evalCrepRuntimeExp (executedCrepState state) e =
            (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord :=
        fun e he => ih e he (hm e he)
      cases operator with
      | mul =>
          cases args with
          | nil => simp [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL, crepOpCrepWord]
          | cons a rest =>
              cases rest with
              | nil =>
                  simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
                  cases ha : evalCrepSemHOLExp state (crepExpToHOL a) with
                  | none => simp [ha, crepOpCrepWord]
                  | some hwa =>
                      cases hwa with
                      | word va => simp [ha, crepOpCrepWord]
              | cons b rest2 =>
                  cases rest2 with
                  | nil =>
                      simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
                      rw [hpoint a (by simp), hpoint b (by simp)]
                      cases ha : evalCrepSemHOLExp state (crepExpToHOL a) with
                      | none => simp [ha, crepOpCrepWord]
                      | some hwa =>
                          cases hwa with
                          | word l =>
                              cases hb : evalCrepSemHOLExp state (crepExpToHOL b) with
                              | none => simp [hb, crepOpCrepWord]
                              | some hwb =>
                                  cases hwb with
                                  | word r =>
                                      simp [ha, hb, crepOpCrep, crepOpCrepWord, holWordLabToWord]
                  | cons c rest3 =>
                      simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL,
                        List.mapM_map, Function.comp_def]
                      cases ha : evalCrepSemHOLExp state (crepExpToHOL a) with
                      | none => simp [ha, crepOpCrepWord]
                      | some hwa =>
                          cases hwa with
                          | word va =>
                              cases hb : evalCrepSemHOLExp state (crepExpToHOL b) with
                              | none => simp [hb, crepOpCrepWord]
                              | some hwb =>
                                  cases hwb with
                                  | word vb =>
                                      cases hc : evalCrepSemHOLExp state (crepExpToHOL c) with
                                      | none => simp [hc, crepOpCrepWord]
                                      | some hwc =>
                                          cases hwc with
                                          | word vc =>
                                              cases hr : List.mapM
                                                  (fun x => evalCrepSemHOLExp state (crepExpToHOL x))
                                                  rest3 with
                                              | none => simp [hr]
                                              | some vr => simp [ha, hb, hc, hr, crepOpCrepWord]
  case cmp operator left right ihleft ihright =>
      simp only [crepExpNoMemLoad] at hm
      obtain ⟨hml, hmr⟩ := hm
      simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
      rw [ihleft hml, ihright hmr]
      cases hl : evalCrepSemHOLExp state (crepExpToHOL left) with
      | none => rfl
      | some hwl =>
          cases hwl with
          | word l =>
              cases hr : evalCrepSemHOLExp state (crepExpToHOL right) with
              | none => rfl
              | some hwr =>
                  cases hwr with
                  | word r =>
                      simp only [Option.map_some]
                      simp [executedCrepState, CrepHolState.toRuntime,
                        RiscV.panRiscVMemoryModelForEndian, panRiscVCmp_eq_wordCmpResultHOL,
                        holWordLabToWord]
  case shift operator left right ihleft ihright =>
      simp only [crepExpNoMemLoad] at hm
      obtain ⟨hml, hmr⟩ := hm
      simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
      rw [ihleft hml, ihright hmr]
      cases hl : evalCrepSemHOLExp state (crepExpToHOL left) with
      | none => rfl
      | some hwl =>
          cases hwl with
          | word l =>
              cases hr : evalCrepSemHOLExp state (crepExpToHOL right) with
              | none => rfl
              | some hwr =>
                  cases hwr with
                  | word r =>
                      simp only [Option.map_some]
                      simp [executedCrepState, CrepHolState.toRuntime,
                        RiscV.panRiscVMemoryModelForEndian, panRiscVShift_eq_wordShiftHOL,
                        Option.map_map, Function.comp_def]
  case op operator args ih =>
      simp only [crepExpNoMemLoad] at hm
      have hpoint : ∀ e ∈ args,
          evalCrepRuntimeExp (executedCrepState state) e =
            (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord :=
        fun e he => ih e he (hm e he)
      have hf : args.mapM (evalCrepRuntimeExp (executedCrepState state)) =
          (args.mapM (fun a => evalCrepSemHOLExp state (crepExpToHOL a))).map
            (List.map holWordLabToWord) := by
        rw [show args.mapM (evalCrepRuntimeExp (executedCrepState state)) =
              args.mapM (fun a => (evalCrepSemHOLExp state (crepExpToHOL a)).map holWordLabToWord)
            from Flapjack.list_mapM_congr _ _ _ hpoint]
        exact list_mapM_mapOption _ _ args
      simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL, List.mapM_map,
        Function.comp_def]
      rw [hf]
      cases hargs : args.mapM (fun a => evalCrepSemHOLExp state (crepExpToHOL a)) with
      | none => simp
      | some values =>
          simp only [Option.map_some]
          simp [executedCrepState, CrepHolState.toRuntime, RiscV.panRiscVMemoryModelForEndian,
            RiscV.panRiscVWordOp, wordOpHOL, option_map_holWordLabToWord_comp_word]
          apply congrArg (wordOp operator)
          exact List.map_congr_left (fun v _ => holWordLabToWord_eq v)

end Flapjack
