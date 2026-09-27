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

The scope is the fragment that does not read the byte/endian memory model
(`crepExpNoByteMemoryLoad` excludes only `load32`/`loadByte`):
`const`/`var`/`loadGlob`/`baseAddr`/`topAddr`, the plain single-cell `load`,
the arithmetic hooks `op`/`crepOp`, and the comparisons `cmp`/`shift`. This
also covers the `Const` list path exercised by `evaluate_replicate_const`
(`pan_to_crepProofScript.sml:3051`). `evalCrepRuntimeExp_executed_of_noByteMemoryLoad`
proves the pointwise agreement for that fragment. The byte-reading constructors
(`load32`/`loadByte`) still need the `mem_load_32`/`mem_load_byte` reassembly
correspondence, tracked separately under bead `flapjack-pxn.18.4.3.48.1.21`.
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

/-- Crep expressions that do not read the byte/endian memory model, i.e. no
`load32`/`loadByte`. A plain `load` reads a single memory cell and does not
consult the byte/endian model, so it is admitted whenever its address is. The
arithmetic hooks `op`/`crepOp` and the value comparisons `cmp`/`shift` read
only their operands, so they are included whenever all subterms are. This is
the fragment on which the executed production evaluator and the exact
`evalCrepSemHOLExp` are proved to agree below. -/
def crepExpNoByteMemoryLoad {width : Nat} [NeZero width] : CrepExp (BitVec width) → Prop
  | .const _ => True
  | .var _ => True
  | .load address => crepExpNoByteMemoryLoad address
  | .load32 _ => False
  | .loadByte _ => False
  | .loadGlob _ => True
  | .op _ args => ∀ a ∈ args, crepExpNoByteMemoryLoad a
  | .crepOp _ args => ∀ a ∈ args, crepExpNoByteMemoryLoad a
  | .cmp _ left right => crepExpNoByteMemoryLoad left ∧ crepExpNoByteMemoryLoad right
  | .shift _ left right => crepExpNoByteMemoryLoad left ∧ crepExpNoByteMemoryLoad right
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
state agrees with the tagged exact `evalCrepSemHOLExp`, for the fragment that
does not read the byte/endian memory model
(`const`/`var`/`loadGlob`/`baseAddr`/`topAddr`, plain `load`, `op`, `crepOp`,
`cmp`, `shift`). The exact value is read through the bare-word projection
`holWordLabToWord`, which is what the executed production evaluator returns. -/
theorem evalCrepRuntimeExp_executed_of_noByteMemoryLoad {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (e : CrepExp (BitVec width)) (hm : crepExpNoByteMemoryLoad e) :
    evalCrepRuntimeExp (executedCrepState state) e =
      (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord := by
  induction e using (CrepExp.rec (motive_2 := fun args =>
      ∀ e ∈ args, crepExpNoByteMemoryLoad e →
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
  case load address ih =>
      simp only [crepExpNoByteMemoryLoad] at hm
      simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
      rw [ih hm]
      cases ha : evalCrepSemHOLExp state (crepExpToHOL address) with
      | none => rfl
      | some hwa =>
          cases hwa with
          | word w =>
              simp only [Option.map_some]
              simp [crepRuntimeLoad, executedCrepState, CrepSemHOLState.toBitVecEvaluatorState,
                CrepHolState.toRuntime, holWordLabToWord]
  case load32 address ih => simp only [crepExpNoByteMemoryLoad] at hm
  case loadByte address ih => simp only [crepExpNoByteMemoryLoad] at hm
  case crepOp operator args ih =>
      simp only [crepExpNoByteMemoryLoad] at hm
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
      simp only [crepExpNoByteMemoryLoad] at hm
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
      simp only [crepExpNoByteMemoryLoad] at hm
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
      simp only [crepExpNoByteMemoryLoad] at hm
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

/-! ## Byte-reading arms at RV64

The plain `load32`/`loadByte` arms consult the runtime byte/endian memory model, while the
exact `evalCrepSemHOLExp` reads through `panMemLoad32HOL`/`panMemLoadByteHOL`. The two agree
at width 64 by `crepRuntimeLoad32_riscv64_eq_panMemLoad32HOL` and
`crepRuntimeLoadByte_riscv64_eq_panMemLoadByteHOL`, so the theorems below take the
address-subterm correspondence as a hypothesis. -/

theorem evalCrepRuntimeExp_executed_load32 {σ : Type}
    (state : CrepSemHOLState 64 σ) [DecidablePred state.memaddrs]
    (address : CrepExp (BitVec 64))
    (haddr : evalCrepRuntimeExp (executedCrepState state) address =
      (evalCrepSemHOLExp state (crepExpToHOL address)).map holWordLabToWord) :
    evalCrepRuntimeExp (executedCrepState state) (.load32 address) =
      (evalCrepSemHOLExp state (crepExpToHOL (.load32 address))).map holWordLabToWord := by
  simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
  rw [haddr]
  cases ha : evalCrepSemHOLExp state (crepExpToHOL address) with
  | none => simp
  | some hwa =>
      cases hwa with
      | word w =>
          have hload : crepRuntimeLoad32 (executedCrepState state) w =
              (panMemLoad32HOL state.memory state.memaddrs state.be w).map
                (fun value => BitVec.ofNat 64 value.toNat) := by
            have h := crepRuntimeLoad32_riscv64_eq_panMemLoad32HOL
              (state.toBitVecEvaluatorState) w
            rw [show riscvCrepWordTarget (state.toBitVecEvaluatorState).toRuntime =
                executedCrepState state from rfl] at h
            simp only [CrepSemHOLState.toBitVecEvaluatorState, decide_eq_true_eq] at h
            have hmem : (fun current => (state.memory current).toPanWordLab.toHolWordLab)
                = state.memory := by
              funext c
              exact HolWordLab.toPanWordLab_toHolWordLab (state.memory c)
            rw [hmem] at h
            exact h
          show crepRuntimeLoad32 (executedCrepState state) w =
            (Option.map (fun v => HolWordLab.word (BitVec.ofNat 64 v.toNat))
              (panMemLoad32HOL state.memory state.memaddrs state.be w)).map
                holWordLabToWord
          rw [hload]
          simp only [Option.map_map, Function.comp_def, holWordLabToWord_eq]

theorem evalCrepRuntimeExp_executed_loadByte {σ : Type}
    (state : CrepSemHOLState 64 σ) [DecidablePred state.memaddrs]
    (address : CrepExp (BitVec 64))
    (haddr : evalCrepRuntimeExp (executedCrepState state) address =
      (evalCrepSemHOLExp state (crepExpToHOL address)).map holWordLabToWord) :
    evalCrepRuntimeExp (executedCrepState state) (.loadByte address) =
      (evalCrepSemHOLExp state (crepExpToHOL (.loadByte address))).map holWordLabToWord := by
  simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
  rw [haddr]
  cases ha : evalCrepSemHOLExp state (crepExpToHOL address) with
  | none => simp
  | some hwa =>
      cases hwa with
      | word w =>
          have hload : crepRuntimeLoadByte (executedCrepState state) w =
              (panMemLoadByteHOL state.memory state.memaddrs state.be w).map
                (fun value => BitVec.ofNat 64 value.toNat) := by
            have h := crepRuntimeLoadByte_riscv64_eq_panMemLoadByteHOL
              (state.toBitVecEvaluatorState) w
            rw [show riscvCrepWordTarget (state.toBitVecEvaluatorState).toRuntime =
                executedCrepState state from rfl] at h
            simp only [CrepSemHOLState.toBitVecEvaluatorState, decide_eq_true_eq] at h
            have hmem : (fun current => (state.memory current).toPanWordLab.toHolWordLab)
                = state.memory := by
              funext c
              exact HolWordLab.toPanWordLab_toHolWordLab (state.memory c)
            rw [hmem] at h
            exact h
          show crepRuntimeLoadByte (executedCrepState state) w =
            (Option.map (fun v => HolWordLab.word (BitVec.ofNat 64 v.toNat))
              (panMemLoadByteHOL state.memory state.memaddrs state.be w)).map
                holWordLabToWord
          rw [hload]
          simp only [Option.map_map, Function.comp_def, holWordLabToWord_eq]

/-! ## Production `word_lab` result shape

The bare theorems above return bit vectors; the executed production evaluator
`evalCrepRuntimeExpWordLab` returns `word_lab` cells. Reading the bare result
through `PanWordLab.word` and then composing with `holWordLabToWord` recovers
the exact `HolWordLab.toPanWordLab` projection, so the executed production
`word_lab` evaluator's result equals the tagged exact `evalCrepSemHOLExp`
result. This is the production result shape of bead `flapjack-pxn.18.4.3.48.1`.
No `@[hol]` tag: Flapjack-specific representation bridge. -/

/-- Composing the bare-word projection with the `word_lab` wrapper recovers the
exact `word_lab` projection. -/
@[simp] theorem option_map_holWordLabToWord_map_word {width : Nat} [NeZero width]
    (cell : Option (HolWordLab width)) :
    (cell.map holWordLabToWord).map PanWordLab.word = cell.map HolWordLab.toPanWordLab := by
  cases cell <;> rfl

/-- The executed production `word_lab` evaluator at the canonical BitVec
evaluator state returns exactly the tagged exact `evalCrepSemHOLExp` result for
the fragment that does not read the byte/endian memory model. -/
theorem evalCrepRuntimeExpWordLab_executed_of_noByteMemoryLoad
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (e : CrepExp (BitVec width)) (hm : crepExpNoByteMemoryLoad e) :
    evalCrepRuntimeExpWordLab (executedCrepState state) e =
      (evalCrepSemHOLExp state (crepExpToHOL e)).map HolWordLab.toPanWordLab := by
  rw [← evalCrepRuntimeExp_wordLab_projection (executedCrepState state) e]
  rw [evalCrepRuntimeExp_executed_of_noByteMemoryLoad state e hm]
  exact option_map_holWordLabToWord_map_word _

/-- RV64 production `word_lab` result shape for the byte-reading 32-bit load. -/
theorem evalCrepRuntimeExpWordLab_executed_load32 {σ : Type}
    (state : CrepSemHOLState 64 σ) [DecidablePred state.memaddrs]
    (address : CrepExp (BitVec 64))
    (haddr : evalCrepRuntimeExp (executedCrepState state) address =
      (evalCrepSemHOLExp state (crepExpToHOL address)).map holWordLabToWord) :
    evalCrepRuntimeExpWordLab (executedCrepState state) (.load32 address) =
      (evalCrepSemHOLExp state (crepExpToHOL (.load32 address))).map HolWordLab.toPanWordLab := by
  rw [← evalCrepRuntimeExp_wordLab_projection (executedCrepState state) (.load32 address)]
  rw [evalCrepRuntimeExp_executed_load32 state address haddr]
  exact option_map_holWordLabToWord_map_word _

/-- RV64 production `word_lab` result shape for the byte-reading load. -/
theorem evalCrepRuntimeExpWordLab_executed_loadByte {σ : Type}
    (state : CrepSemHOLState 64 σ) [DecidablePred state.memaddrs]
    (address : CrepExp (BitVec 64))
    (haddr : evalCrepRuntimeExp (executedCrepState state) address =
      (evalCrepSemHOLExp state (crepExpToHOL address)).map holWordLabToWord) :
    evalCrepRuntimeExpWordLab (executedCrepState state) (.loadByte address) =
      (evalCrepSemHOLExp state (crepExpToHOL (.loadByte address))).map HolWordLab.toPanWordLab := by
  rw [← evalCrepRuntimeExp_wordLab_projection (executedCrepState state) (.loadByte address)]
  rw [evalCrepRuntimeExp_executed_loadByte state address haddr]
  exact option_map_holWordLabToWord_map_word _

/-! ## List-level production `word_lab` result shape

The production list evaluator `evalCrepRuntimeExpsWordLab` is a `mapM` of the
single-expression `word_lab` evaluator. Lifting the pointwise bridge to lists
lets the whole executed production route return the exact `evalCrepSemHOLExp`
result (mapped through `HolWordLab.toPanWordLab`). This is a Flapjack-specific
representation bridge: it carries no `@[hol]` tag (and, not being under
`Proofs/`, needs no theorem-map entry). -/

private theorem option_map_list_map_cons {α γ : Type} (g : α → γ)
    (A : Option α) (B : Option (List α)) :
    (do let a ← A; let b ← B; pure (a :: b)).map (List.map g) =
      (do let a ← A.map g; let b ← B.map (List.map g); pure (a :: b)) := by
  cases A <;> cases B <;> rfl

/-- Executed production list `word_lab` evaluator equals the exact
`evalCrepSemHOLExp` result (mapped to `PanWordLab`) on any list of expressions
that does not read the byte/endian memory model. -/
theorem evalCrepRuntimeExpsWordLab_executed_of_noByteMemoryLoad
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (es : List (CrepExp (BitVec width)))
    (hm : ∀ e ∈ es, crepExpNoByteMemoryLoad e) :
    evalCrepRuntimeExpsWordLab (executedCrepState state) es =
      (es.mapM (fun e => evalCrepSemHOLExp state (crepExpToHOL e))).map
        (List.map HolWordLab.toPanWordLab) := by
  induction es with
  | nil => simp [evalCrepRuntimeExpsWordLab]
  | cons e rest ih =>
      rw [List.mapM_cons]
      rw [evalCrepRuntimeExpsWordLab]
      rw [evalCrepRuntimeExpWordLab_executed_of_noByteMemoryLoad state e (hm e (by simp))]
      rw [ih (fun x hx => hm x (by simp [hx]))]
      exact (option_map_list_map_cons _ _ _).symm

/-- Executed-route `replicate (Const v)` corollary of the list-level bridge. -/
theorem evalCrepRuntimeExpsWordLab_replicate_const_matches_exact
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (n : Nat) (v : BitVec width) :
    evalCrepRuntimeExpsWordLab (executedCrepState state) (List.replicate n (.const v)) =
      ((List.replicate n (.const v)).mapM
        (fun e => evalCrepSemHOLExp state (crepExpToHOL e))).map
        (List.map HolWordLab.toPanWordLab) :=
  evalCrepRuntimeExpsWordLab_executed_of_noByteMemoryLoad state _
    (by
      intro e he
      rw [List.mem_replicate] at he
      obtain ⟨_, rfl⟩ := he
      simp [crepExpNoByteMemoryLoad])

/-! ## Full width-64 projection bridge

At width 64 every expression arm is bridged, so the executed production
evaluator at the canonical BitVec evaluator state agrees with the tagged exact
`evalCrepSemHOLExp` on all Crep expressions (no hypothesis). The byte-reading
`load32`/`loadByte` arms reuse the width-64 theorems above; all other arms are
memory-free or recurse. This is a Flapjack-specific representation bridge: it
carries no `@[hol]` tag (and, not being under `Proofs/`, needs no theorem-map
entry). -/

set_option maxHeartbeats 2000000 in
/-- Executed production Crep evaluator at the canonical BitVec evaluator state
agrees with the tagged exact `evalCrepSemHOLExp` for every expression at width
64. -/
theorem evalCrepRuntimeExp_executed {σ : Type} (state : CrepSemHOLState 64 σ)
    [DecidablePred state.memaddrs] (e : CrepExp (BitVec 64)) :
    evalCrepRuntimeExp (executedCrepState state) e =
      (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord := by
  induction e using (CrepExp.rec (motive_2 := fun args =>
      ∀ e ∈ args,
        evalCrepRuntimeExp (executedCrepState state) e =
          (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord))
  case nil e he => simp at he
  case cons head tail head_ih tail_ih e he =>
      rcases List.mem_cons.mp he with rfl | he
      · exact head_ih
      · exact tail_ih e he
  case const value =>
      exact evalCrepRuntimeExp_executed_of_noByteMemoryLoad state _
        (by simp [crepExpNoByteMemoryLoad])
  case var name =>
      exact evalCrepRuntimeExp_executed_of_noByteMemoryLoad state _
        (by simp [crepExpNoByteMemoryLoad])
  case loadGlob address =>
      exact evalCrepRuntimeExp_executed_of_noByteMemoryLoad state _
        (by simp [crepExpNoByteMemoryLoad])
  case baseAddr =>
      exact evalCrepRuntimeExp_executed_of_noByteMemoryLoad state _
        (by simp [crepExpNoByteMemoryLoad])
  case topAddr =>
      exact evalCrepRuntimeExp_executed_of_noByteMemoryLoad state _
        (by simp [crepExpNoByteMemoryLoad])
  case load address ih =>
      simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
      rw [ih]
      cases ha : evalCrepSemHOLExp state (crepExpToHOL address) with
      | none => rfl
      | some hwa =>
          cases hwa with
          | word w =>
              simp only [Option.map_some]
              simp [crepRuntimeLoad, executedCrepState, CrepSemHOLState.toBitVecEvaluatorState,
                CrepHolState.toRuntime, holWordLabToWord]
  case load32 address ih => exact evalCrepRuntimeExp_executed_load32 state address ih
  case loadByte address ih => exact evalCrepRuntimeExp_executed_loadByte state address ih
  case crepOp operator args ih =>
      have hpoint : ∀ e ∈ args,
          evalCrepRuntimeExp (executedCrepState state) e =
            (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord :=
        fun e he => ih e he
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
      simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
      rw [ihleft, ihright]
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
      simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
      rw [ihleft, ihright]
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
      have hpoint : ∀ e ∈ args,
          evalCrepRuntimeExp (executedCrepState state) e =
            (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord :=
        fun e he => ih e he
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

/-- Executed production `word_lab` Crep evaluator at the canonical BitVec
evaluator state returns the exact `evalCrepSemHOLExp` result (mapped through
`HolWordLab.toPanWordLab`) for every expression at width 64. -/
theorem evalCrepRuntimeExpWordLab_executed {σ : Type} (state : CrepSemHOLState 64 σ)
    [DecidablePred state.memaddrs] (e : CrepExp (BitVec 64)) :
    evalCrepRuntimeExpWordLab (executedCrepState state) e =
      (evalCrepSemHOLExp state (crepExpToHOL e)).map HolWordLab.toPanWordLab := by
  rw [← evalCrepRuntimeExp_wordLab_projection (executedCrepState state) e]
  rw [evalCrepRuntimeExp_executed state e]
  exact option_map_holWordLabToWord_map_word _

@[simp] theorem list_holWordLabToWord_map_word {width : Nat} [NeZero width]
    (l : List (HolWordLab width)) :
    (l.map holWordLabToWord).map PanWordLab.word = l.map HolWordLab.toPanWordLab := by
  induction l with
  | nil => rfl
  | cons h t ih => cases h with | word v => simp [ih]

@[simp] theorem option_map_list_holWordLabToWord_map_word {width : Nat} [NeZero width]
    (o : Option (List (HolWordLab width))) :
    (o.map (List.map holWordLabToWord)).map (List.map PanWordLab.word) =
      o.map (List.map HolWordLab.toPanWordLab) := by
  cases o with
  | none => rfl
  | some l => simpa only [Option.map_some] using congrArg some (list_holWordLabToWord_map_word l)

section

set_option maxHeartbeats 1000000

/-- Unconditional width-64 list-level executed bridge: the shipped bare list
evaluator `evalCrepRuntimeExps` at the canonical BitVec evaluator state returns
the exact `evalCrepSemHOLExp` result (mapped through `holWordLabToWord`) for
every list of expressions.  This lifts `evalCrepRuntimeExp_executed` from a
single expression to the list evaluator. -/
theorem evalCrepRuntimeExps_executed {σ : Type} (state : CrepSemHOLState 64 σ)
    [DecidablePred state.memaddrs] (es : List (CrepExp (BitVec 64))) :
    evalCrepRuntimeExps (executedCrepState state) es =
      (es.mapM (fun e => evalCrepSemHOLExp state (crepExpToHOL e))).map
        (List.map holWordLabToWord) := by
  induction es with
  | nil => simp [evalCrepRuntimeExps]
  | cons e rest ih =>
      rw [List.mapM_cons]
      simp only [evalCrepRuntimeExps]
      rw [evalCrepRuntimeExp_executed state e]
      rw [ih]
      exact (option_map_list_map_cons _ _ _).symm

end

/-- Unconditional width-64 list-level executed production `word_lab` bridge: the
shipped `word_lab` list evaluator returns the exact `evalCrepSemHOLExp` result
(mapped through `HolWordLab.toPanWordLab`). -/
theorem evalCrepRuntimeExpsWordLab_executed {σ : Type} (state : CrepSemHOLState 64 σ)
    [DecidablePred state.memaddrs] (es : List (CrepExp (BitVec 64))) :
    evalCrepRuntimeExpsWordLab (executedCrepState state) es =
      (es.mapM (fun e => evalCrepSemHOLExp state (crepExpToHOL e))).map
        (List.map HolWordLab.toPanWordLab) := by
  rw [← evalCrepRuntimeExps_wordLab_projection (executedCrepState state) es]
  rw [evalCrepRuntimeExps_executed state es]
  exact option_map_list_holWordLabToWord_map_word (width := 64) _

end Flapjack
