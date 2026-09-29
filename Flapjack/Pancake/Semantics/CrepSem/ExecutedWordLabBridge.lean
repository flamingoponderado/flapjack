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

At every positive width, `evalCrepRuntimeExp_executed_allWidth` proves the
pointwise agreement for every Crep expression, with no hypothesis. Its
constructors are `const`/`var`/`loadGlob`/`baseAddr`/`topAddr`, the plain
`load`, the byte-reading `loadByte`/`load32`, `op`/`crepOp`, and `cmp`/`shift`.
The byte-reading arms rely on the production alignment, byte index and
`word32`-then-`w2w` assembly agreeing with HOL's `byte_align`/`byte_index`/
`mem_load_32` at every width (beads `flapjack-pxn.18.5.4.3.4`/`.5`/`.6`).  The
fragment forms `evalCrepRuntimeExp_executed_of_noLoad32` and
`evalCrepRuntimeExp_executed_of_noByteMemoryLoad` are corollaries; the latter
covers the `Const` list path of `evaluate_replicate_const`
(`pan_to_crepProofScript.sml:3051`).
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

/-- Crep expressions without a `load32`: every other constructor, including the
byte-reading `loadByte`, is admitted whenever its subterms are.  This is the
all-width fragment of `evalCrepRuntimeExp_executed_of_noLoad32`. -/
def crepExpNoLoad32 {width : Nat} [NeZero width] : CrepExp (BitVec width) → Prop
  | .const _ => True
  | .var _ => True
  | .load address => crepExpNoLoad32 address
  | .load32 _ => False
  | .loadByte address => crepExpNoLoad32 address
  | .loadGlob _ => True
  | .op _ args => ∀ a ∈ args, crepExpNoLoad32 a
  | .crepOp _ args => ∀ a ∈ args, crepExpNoLoad32 a
  | .cmp _ left right => crepExpNoLoad32 left ∧ crepExpNoLoad32 right
  | .shift _ left right => crepExpNoLoad32 left ∧ crepExpNoLoad32 right
  | .baseAddr => True
  | .topAddr => True

/-- Excluding both byte-reading loads excludes `load32`. -/
theorem crepExpNoLoad32_of_noByteMemoryLoad {width : Nat} [NeZero width] :
    ∀ e : CrepExp (BitVec width), crepExpNoByteMemoryLoad e → crepExpNoLoad32 e := by
  intro e
  induction e using (CrepExp.rec (motive_2 := fun (args : List (CrepExp (BitVec width))) =>
      ∀ e ∈ args, crepExpNoByteMemoryLoad e → crepExpNoLoad32 e))
  case nil e he _ => exact absurd he (by simp)
  case cons head tail head_ih tail_ih e he hm =>
      rcases List.mem_cons.mp he with rfl | he
      · exact head_ih hm
      · exact tail_ih e he hm
  all_goals intro hm; simp only [crepExpNoByteMemoryLoad, crepExpNoLoad32] at hm ⊢
  case load address ih => exact ih hm
  case op _ args ih => exact fun a ha => ih a ha (hm a ha)
  case crepOp _ args ih => exact fun a ha => ih a ha (hm a ha)
  case cmp _ _ _ ihl ihr => exact ⟨ihl hm.1, ihr hm.2⟩
  case shift _ _ _ ihl ihr => exact ⟨ihl hm.1, ihr hm.2⟩

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

/-! ## Byte-reading arms

The plain `load32`/`loadByte` arms consult the runtime byte/endian memory model, while the
exact `evalCrepSemHOLExp` reads through `panMemLoad32HOL`/`panMemLoadByteHOL`.  `loadByte`
agrees at every positive width by `crepRuntimeLoadByte_riscv_eq_panMemLoadByteHOL` (bead
`flapjack-pxn.18.5.4.3.5`), and `load32` by `crepRuntimeLoad32_riscv_eq_panMemLoad32HOL`
(bead `flapjack-pxn.18.5.4.3.6`).  The theorems below take the address-subterm
correspondence as a hypothesis. -/

theorem evalCrepRuntimeExp_executed_load32 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (address : CrepExp (BitVec width))
    (haddr : evalCrepRuntimeExp (executedCrepState state) address =
      (evalCrepSemHOLExp state (crepExpToHOL address)).map holWordLabToWord) :
    evalCrepRuntimeExp (executedCrepState state) (.load32 address) =
      (evalCrepSemHOLExp state (crepExpToHOL (.load32 address))).map holWordLabToWord := by
  classical
  simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
  rw [haddr]
  cases ha : evalCrepSemHOLExp state (crepExpToHOL address) with
  | none => simp
  | some hwa =>
      cases hwa with
      | word w =>
          have hload : crepRuntimeLoad32 (executedCrepState state) w =
              (panMemLoad32HOL state.memory state.memaddrs state.be w).map
                (fun value => BitVec.ofNat width value.toNat) := by
            have h := crepRuntimeLoad32_riscv_eq_panMemLoad32HOL
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
          simp [hload, Option.bind, Function.comp_def, holWordLabToWord_eq]

theorem evalCrepRuntimeExp_executed_loadByte {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (address : CrepExp (BitVec width))
    (haddr : evalCrepRuntimeExp (executedCrepState state) address =
      (evalCrepSemHOLExp state (crepExpToHOL address)).map holWordLabToWord) :
    evalCrepRuntimeExp (executedCrepState state) (.loadByte address) =
      (evalCrepSemHOLExp state (crepExpToHOL (.loadByte address))).map holWordLabToWord := by
  classical
  simp only [evalCrepRuntimeExp, evalCrepSemHOLExp, crepExpToHOL]
  rw [haddr]
  cases ha : evalCrepSemHOLExp state (crepExpToHOL address) with
  | none => simp
  | some hwa =>
      cases hwa with
      | word w =>
          have hload : crepRuntimeLoadByte (executedCrepState state) w =
              (panMemLoadByteHOL state.memory state.memaddrs state.be w).map
                (fun value => BitVec.ofNat width value.toNat) := by
            have h := crepRuntimeLoadByte_riscv_eq_panMemLoadByteHOL
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
          simp [hload, Option.bind, Function.comp_def, holWordLabToWord_eq]

/-- The executed production Crep evaluator at the canonical BitVec evaluator
state agrees with the tagged exact `evalCrepSemHOLExp`, at every positive
width, for every Crep expression, with no hypothesis: all constructors,
including the byte-reading `loadByte` and `load32`, whose production alignment,
byte index and 32-bit assembly are HOL's `byte_align`/`byte_index`/`mem_load_32`
at every width (beads `flapjack-pxn.18.5.4.3.4`/`.5`/`.6`). The exact value is read through the bare-word projection
`holWordLabToWord`, which is what the executed production evaluator returns. -/
theorem evalCrepRuntimeExp_executed_allWidth {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (e : CrepExp (BitVec width)) :
    evalCrepRuntimeExp (executedCrepState state) e =
      (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord := by
  induction e using (CrepExp.rec (motive_2 := fun args =>
      ∀ e ∈ args,
        evalCrepRuntimeExp (executedCrepState state) e =
          (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord))
  case nil e he =>
      exact absurd he (by simp)
  case cons head tail head_ih tail_ih e he =>
      rcases List.mem_cons.mp he with rfl | he
      · exact head_ih
      · exact tail_ih e he
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
  case loadByte address ih =>
      exact evalCrepRuntimeExp_executed_loadByte state address ih
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

/-- Fragment form: expressions without `load32`. -/
theorem evalCrepRuntimeExp_executed_of_noLoad32 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (e : CrepExp (BitVec width)) (_hm : crepExpNoLoad32 e) :
    evalCrepRuntimeExp (executedCrepState state) e =
      (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord :=
  evalCrepRuntimeExp_executed_allWidth state e

/-- The earlier fragment without either byte-reading load is a special case of
    `evalCrepRuntimeExp_executed_of_noLoad32`. -/
theorem evalCrepRuntimeExp_executed_of_noByteMemoryLoad {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (e : CrepExp (BitVec width)) (hm : crepExpNoByteMemoryLoad e) :
    evalCrepRuntimeExp (executedCrepState state) e =
      (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord :=
  evalCrepRuntimeExp_executed_of_noLoad32 state e (crepExpNoLoad32_of_noByteMemoryLoad e hm)

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

/-- All-width production `word_lab` result shape for the byte-reading 32-bit load. -/
theorem evalCrepRuntimeExpWordLab_executed_load32 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (address : CrepExp (BitVec width))
    (haddr : evalCrepRuntimeExp (executedCrepState state) address =
      (evalCrepSemHOLExp state (crepExpToHOL address)).map holWordLabToWord) :
    evalCrepRuntimeExpWordLab (executedCrepState state) (.load32 address) =
      (evalCrepSemHOLExp state (crepExpToHOL (.load32 address))).map HolWordLab.toPanWordLab := by
  rw [← evalCrepRuntimeExp_wordLab_projection (executedCrepState state) (.load32 address)]
  rw [evalCrepRuntimeExp_executed_load32 state address haddr]
  exact option_map_holWordLabToWord_map_word _

/-- All-width production `word_lab` result shape for the byte-reading load. -/
theorem evalCrepRuntimeExpWordLab_executed_loadByte {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (address : CrepExp (BitVec width))
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

/-! ## Whole-evaluator projection bridge

At every positive width every expression arm is bridged
(`evalCrepRuntimeExp_executed_allWidth`), so the executed production evaluator
at the canonical BitVec evaluator state agrees with the tagged exact
`evalCrepSemHOLExp` on all Crep expressions (no hypothesis).  This is a
Flapjack-specific representation bridge: it carries no `@[hol]` tag (and, not
being under `Proofs/`, needs no theorem-map entry). -/

/-- Executed production Crep evaluator at the canonical BitVec evaluator state
agrees with the tagged exact `evalCrepSemHOLExp` for every expression, at every
positive width. -/
theorem evalCrepRuntimeExp_executed {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    [DecidablePred state.memaddrs] (e : CrepExp (BitVec width)) :
    evalCrepRuntimeExp (executedCrepState state) e =
      (evalCrepSemHOLExp state (crepExpToHOL e)).map holWordLabToWord :=
  evalCrepRuntimeExp_executed_allWidth state e

/-- Executed production `word_lab` Crep evaluator at the canonical BitVec
evaluator state returns the exact `evalCrepSemHOLExp` result (mapped through
`HolWordLab.toPanWordLab`) for every expression, at every positive width. -/
theorem evalCrepRuntimeExpWordLab_executed {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    [DecidablePred state.memaddrs] (e : CrepExp (BitVec width)) :
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

/-- Unconditional all-width list-level executed bridge: the shipped bare list
evaluator `evalCrepRuntimeExps` at the canonical BitVec evaluator state returns
the exact `evalCrepSemHOLExp` result (mapped through `holWordLabToWord`) for
every list of expressions.  This lifts `evalCrepRuntimeExp_executed` from a
single expression to the list evaluator. -/
theorem evalCrepRuntimeExps_executed {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    [DecidablePred state.memaddrs] (es : List (CrepExp (BitVec width))) :
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

/-- Unconditional all-width list-level executed production `word_lab` bridge: the
shipped `word_lab` list evaluator returns the exact `evalCrepSemHOLExp` result
(mapped through `HolWordLab.toPanWordLab`). -/
theorem evalCrepRuntimeExpsWordLab_executed {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    [DecidablePred state.memaddrs] (es : List (CrepExp (BitVec width))) :
    evalCrepRuntimeExpsWordLab (executedCrepState state) es =
      (es.mapM (fun e => evalCrepSemHOLExp state (crepExpToHOL e))).map
        (List.map HolWordLab.toPanWordLab) := by
  rw [← evalCrepRuntimeExps_wordLab_projection (executedCrepState state) es]
  rw [evalCrepRuntimeExps_executed state es]
  exact option_map_list_holWordLabToWord_map_word (width := width) _

end Flapjack
