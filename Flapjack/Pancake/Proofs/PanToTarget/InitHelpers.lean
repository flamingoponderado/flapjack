import Flapjack.Pancake.Proofs.PanToTarget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
import Flapjack.Compiler.Backend.StackProps.EvaluateConsts
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.Alignment
import Flapjack.Pancake.CrepToLoop
import Flapjack.Compiler.Backend.BvlToBvi

/-!
# `pan_to_targetProof`: arithmetic and initialization helpers

Helper theorems of `cakeml/pancake/proofs/pan_to_targetProofScript.sml` used by
`pan_to_target_compile_semantics`: `word_to_stack_compile_FST` (79-87),
`good_dimindex_0w_8w` (249-256), `full_make_init_be` (277-288), `n2w_sub_alt`
(1193-1201), `aligned_n2w_IMP` (1203-1209), `good_dimindex_div_mul` (1242-1248) and
`InitGlobals_location_eq_first_name` (1250-1254). HOL's `≤` on words is the signed
`word_le`, rendered by `BitVec.sle`.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm

namespace InitHelpersCarrier

/-- Same-module canonical finite-support witness for the `regs`/`fpRegs`/`store`
    fields named by `full_make_init_be`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

end InitHelpersCarrier

/-- HOL `word_to_stack_compile_FST` (`pan_to_targetProofScript.sml:79-87`); `word_to_stack_compile`
    is the script's overload of the tagged `word_to_stack$compile` (`compileNative`), and HOL's free
    `mc wprog bitmaps c'' fs p` are explicit. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_to_stack_compile_FST"
  (words_as_type_indexed_bitvec)]
theorem word_to_stack_compile_FST {width : Nat} [NeZero width] {State Projection : Type}
    (mc : MachineConfig width State Projection)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : Compiler.Backend.WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × Compiler.Backend.StackLang.HolProg width)) :
    Compiler.Backend.WordToStack.Native.compileNative mc.target.config false wprog =
        (bitmaps, c'', fs, p) →
      p.map Prod.fst = raiseStubLocation :: storeConstsStubLocation :: wprog.map Prod.fst := by
  intro h
  simp only [Compiler.Backend.WordToStack.Native.compileNative, Bool.false_eq_true,
    ↓reduceIte] at h
  rcases hc : Compiler.Backend.WordToStack.Native.compileWordToStackNative mc.target.config false
    (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) wprog (.list [4], 1) with
    ⟨bodies, frames, bm⟩
  rw [hc] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, -, -, rfl⟩ := h
  simp only [List.map_cons]
  rw [WordToStackProofs.mapFstCompileWordToStack _ _ _ _ _ _ _ hc]

/-- HOL `good_dimindex_0w_8w` (`pan_to_targetProofScript.sml:249-256`): HOL's signed word `≤`
    is `BitVec.sle`; `good_dimindex (:α)` is the tagged `goodDimindex width`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "good_dimindex_0w_8w"
  (words_as_type_indexed_bitvec)]
theorem good_dimindex_0w_8w {width : Nat} [NeZero width] :
    goodDimindex width →
      (0 : BitVec width).sle 8 = true ∧ (-8 : BitVec width).sle 0 = true := by
  rintro (rfl | rfl) <;> decide

/-- stack_remove's total initializer keeps the endianness flag (Flapjack infrastructure for
    `full_make_init_be`; HOL unfolds `make_init_any_def`/`make_init_opt_def` and uses
    `stackProps$evaluate_consts`). -/
theorem makeInitAny_be {width : Nat} [NeZero width] {C F : Type}
    (ggc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × Compiler.Backend.StackLang.HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (Compiler.Backend.StackLang.HolProg width)) (s : StackSemStateFiniteExact width C F) :
    (Compiler.Backend.StackRemove.Proofs.InitMake.makeInitAny ggc maxHeap bitmaps dataSpace oracle
      jump bounds pointer code s).be = s.be := by
  unfold Compiler.Backend.StackRemove.Proofs.InitMake.makeInitAny
  cases h : Compiler.Backend.StackRemove.Proofs.InitMake.makeInitOpt ggc maxHeap bitmaps dataSpace
    oracle jump bounds pointer code s with
  | none => rfl
  | some t =>
    simp only
    unfold Compiler.Backend.StackRemove.Proofs.InitMake.makeInitOpt at h
    rcases run : StackSemEvaluate.evaluate
      (Compiler.Backend.StackRemove.initCode ggc maxHeap pointer, s) with ⟨r, post⟩
    rw [run] at h
    rcases r with _ | r
    · simp only at h
      split at h
      · simp only [Option.some.injEq] at h
        rw [← h]
        have := (Compiler.Backend.StackProps.evaluateConsts _ _ _ _ run).2.2.2.1
        simp [Compiler.Backend.StackRemove.Proofs.InitReduce.initReduce, this]
      · cases h
    · cases h

/-- HOL `full_make_init_be` (`pan_to_targetProofScript.sml:277-288`): the initial StackSem state
    keeps the LabSem endianness flag. HOL's free `a … k` are explicit, as in the tagged
    `full_make_init_ffi`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "full_make_init_be"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem full_make_init_be {width : Nat} [NeZero width] {C F : Type}
    (a : Compiler.Backend.StackToLab.Config) (b : Compiler.Backend.DataToWord.Config) (c d : Nat)
    (e : BitVec width × BitVec width) (f : List (BitVec width))
    (g : List (Nat × Compiler.Backend.StackLang.HolProg width))
    (h : Flapjack.Compiler.Backend.LabSem.State width C F) (i : Nat → Bool) (j : Nat)
    (k : Nat → C × List (Nat × Compiler.Backend.StackLang.HolProg width) × List (BitVec width)) :
    ((Compiler.Backend.StackToLab.Proofs.FullMakeInit.fullMakeInit a b c d e f g h i j k).1 :
      StackSemStateFiniteExact width C F).be = h.be := by
  simp only [Compiler.Backend.StackToLab.Proofs.FullMakeInit.fullMakeInit, Compiler.Backend.StackAlloc.makeInit,
    makeInitAny_be, Compiler.Backend.StackNames.makeInit, Compiler.Backend.StackToLab.Proofs.MakeInit.makeInit]

/-- HOL `n2w_sub_alt` (`pan_to_targetProofScript.sml:1193-1201`, `[local]`). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "n2w_sub_alt"
  (words_as_type_indexed_bitvec)]
theorem n2w_sub_alt {width : Nat} [NeZero width] :
    ∀ a b : Nat, b ≤ a →
      (BitVec.ofNat width (a - b) : BitVec width) =
        BitVec.ofNat width a + -1 * BitVec.ofNat width b := by
  intro a b h
  have ha : BitVec.ofNat width a = BitVec.ofNat width (a - b) + BitVec.ofNat width b := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h]
  rw [ha]
  simp [BitVec.add_assoc, BitVec.add_right_neg]

/-- HOL `aligned_n2w_IMP` (`pan_to_targetProofScript.sml:1203-1209`, `[local]`); HOL's free
    `k n` are explicit, `aligned` is the tagged `holAligned`, `dimword (:α)` is `2 ^ width` and
    `divides` is `∣`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "aligned_n2w_IMP"
  (words_as_type_indexed_bitvec)]
theorem aligned_n2w_IMP {width : Nat} [NeZero width] (k n : Nat) :
    holAligned k (BitVec.ofNat width n : BitVec width) = true ∧ n < 2 ^ width → 2 ^ k ∣ n := by
  rintro ⟨ha, hn⟩
  simp only [holAligned, decide_eq_true_eq, holAlign_eq_div] at ha
  have h := congrArg BitVec.toNat ha
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h
  have hle : n / 2 ^ k * 2 ^ k ≤ n := Nat.div_mul_le_self n (2 ^ k)
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hn)] at h
  exact ⟨n / 2 ^ k, by rw [Nat.mul_comm]; exact h.symm⟩

/-- HOL `good_dimindex_div_mul` (`pan_to_targetProofScript.sml:1242-1248`); HOL's free `a` is
    explicit and `dimindex (:α)` is the word width. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "good_dimindex_div_mul"
  (word_dimension_as_width := width)]
theorem good_dimindex_div_mul (width : Nat) [NeZero width] (a : Nat) :
    goodDimindex width → a * width / 8 = a * (width / 8) := by
  rintro (rfl | rfl) <;> omega

/-- HOL `InitGlobals_location_eq_first_name` (`pan_to_targetProofScript.sml:1250-1254`). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "InitGlobals_location_eq_first_name"]
theorem InitGlobals_location_eq_first_name :
    Compiler.Backend.BvlToBvi.initGlobalsLocation = firstLoopName := by
  decide

end Flapjack.Pancake.Proofs.PanToTarget
