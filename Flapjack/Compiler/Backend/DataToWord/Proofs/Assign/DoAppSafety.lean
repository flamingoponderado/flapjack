module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataProps.NonFfiResources
public import Flapjack.Compiler.Backend.DataToWord.Locations
public import Flapjack.Misc.MiscThe

@[expose] public section

/-!
# Space-safety `do_app` lemmas of `data_to_word_assignProofScript.sml`
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem

/-- A successful auxiliary application never turns space safety on. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "do_app_aux_safe_for_space_mono"]
theorem doAppAux_safeForSpace_mono {C F : Type} (op : ClosLang.Op) (xs : List Value)
    (s s1 : State C F) (r : Value)
    (h : doAppAux op xs s = .val (r, s1) ∧ s1.safeForSpace = true) : s.safeForSpace = true := by
  obtain ⟨run, safe⟩ := h
  unfold doAppAux at run
  split at run
  · split at run
    · split at run
      · simp only [SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
        obtain ⟨-, rfl⟩ := run
        simpa using safe
      · simp at run
    · simp at run
  · simp at run
  · split at run
    · rename_i pair app
      simp only [SemanticPrimitivesHOL.Result.val.injEq] at run
      subst run
      exact (applyNonFfi_successFields op xs s s1 r s.safeForSpace app).2.2 safe
    · simp at run

/-- Space safety after a successful `FromList` on a decoded list. HOL's
`$> s.limits.stack_limit` is the section `fun n => s.limits.stackLimit > n`, and
`the F` is `miscThe false`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "do_app_FromList_safe"]
theorem doApp_fromList_safe {C F : Type} (v2 : Value) (ys : List Value) (tag : Nat)
    (s : State C F) (v : Value) (s' : State C F)
    (h : valueToList v2 = some ys ∧
      doApp (.blockOp (.fromList tag)) [.number (ys.length : Int), v2] s = .val (v, s')) :
    (s'.safeForSpace = true ↔
      ((smallNum s.limits.arch64Bit (ys.length : Int) ∧ ys.length < 2 ^ s.limits.lengthLimit ∧
          ys.length < archSize s.limits / 16 ∧
          4 * tag < 2 ^ (archSize s.limits - (s.limits.lengthLimit + 2)) ∧
          4 * tag < 2 ^ archSize s.limits / 16) ∧
        (s.safeForSpace = true ∧ noThunksInRefs s.refs ∧
          sizeOfHeapArgs [.number (ys.length : Int), v2] s + (ys.length + 1) ≤ s.limits.heapLimit)) ∧
      miscThe false ((Option.map₂ (· + ·)
          (Option.map₂ max (sptLookup fromListLocation s.stackFrameSizes)
            (sptLookup fromList1Location s.stackFrameSizes))
          (Option.map₂ (· + ·) (sizeOfStack s.stack) s.localsSize)).map
            (fun n => decide (s.limits.stackLimit > n))) = true) := by
  obtain ⟨hv, h⟩ := h
  simp only [doApp] at h
  simp [doSpace, DataLang.opSpaceReset, doAppAux, applyNonFfi, hv, doStack, doLimSafe] at h
  have theGetD : ∀ o : Option Bool, miscThe false o = o.getD false := by
    intro o
    cases o <;> rfl
  have lim : limSafe s.limits (.blockOp (.fromList tag)) [.number (ys.length : Int), v2] ↔
      (smallNum s.limits.arch64Bit (ys.length : Int) ∧ ys.length < 2 ^ s.limits.lengthLimit ∧
        ys.length < archSize s.limits / 16 ∧
        4 * tag < 2 ^ (archSize s.limits - (s.limits.lengthLimit + 2)) ∧
        4 * tag < 2 ^ archSize s.limits / 16) := by
    simp only [limSafe]
    simp [hv, Nat.sub_sub]
  by_cases hy : ys = []
  · subst hy
    simp only [if_true] at h
    obtain ⟨rfl, rfl⟩ := h
    simp at lim
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    simp [lim, spaceConsumed, stackConsumed, theGetD]
  · cases ht : s.tstamps <;> simp [hy, withFreshTimestamp, checkLim, ht] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;>
      simp only [Bool.and_eq_true, decide_eq_true_eq] <;>
      simp [lim, spaceConsumed, stackConsumed, theGetD] <;>
      intros <;> assumption

open Classical in
/-- A successful `RefByte` allocates the filled byte array at the least unused
reference and fixes every changed state field. HOL's overloads
`add_space_safe_args k args s` and `heap_peak_args k args s` are expanded as
`s.safe_for_space ∧ size_of_heap_args args s + k ≤ s.limits.heap_limit` and
`MAX s.peak_heap_length (size_of_heap_args args s + k)`; `LEAST p. p ∉ domain
s.refs` is the data semantics' `leastUnusedRef`, `$> s.limits.stack_limit` is
`fun n => s.limits.stackLimit > n`, and `the F` is `miscThe false`. The Boolean
`safe_for_space` expression is rendered by one `decide`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "do_app_RefByte_eq"]
theorem doApp_refByte_eq {C F : Type} (fl : Bool) (i : Int) (w : BitVec 8) (s : State C F)
    (v : Value) (s' : State C F)
    (h : doApp (.memOp (.refByte fl)) [.number i, .number (w.toNat : Int)] s = .val (v, s')) :
    ∃ ptr, v = .refPtr true ptr ∧ ptr = leastUnusedRef s.refs ∧ 0 ≤ i ∧
      s' = { s with
        stackMax := Option.map₂ max s.stackMax
          (Option.map₂ (· + ·)
            (stackConsumed s.stackFrameSizes s.limits (.memOp (.refByte fl))
              [.number i, .number (w.toNat : Int)])
            (Option.map₂ (· + ·) (sizeOfStack s.stack) s.localsSize))
        refs := sptInsert ptr (.byteArray fl (List.replicate i.toNat w)) s.refs
        space := 0
        safeForSpace := decide
          (((i.toNat / (archSize s.limits / 8) < 2 ^ archSize s.limits / archSize s.limits ∧
              i.toNat / (archSize s.limits / 8) + 1 < 2 ^ s.limits.lengthLimit ∧
              smallNum s.limits.arch64Bit i) ∧
            noThunksInRefs s.refs ∧
            (s.safeForSpace = true ∧
              sizeOfHeapArgs [.number i, .number (w.toNat : Int)] s +
                spaceConsumed s (.memOp (.refByte fl)) [.number i, .number (w.toNat : Int)] ≤
                  s.limits.heapLimit)) ∧
          miscThe false ((Option.map₂ (· + ·)
            (stackConsumed s.stackFrameSizes s.limits (.memOp (.refByte fl))
              [.number i, .number (w.toNat : Int)])
            (Option.map₂ (· + ·) (sizeOfStack s.stack) s.localsSize)).map
              (fun n => decide (s.limits.stackLimit > n))) = true)
        peakHeapLength := max s.peakHeapLength
          (sizeOfHeapArgs [.number i, .number (w.toNat : Int)] s +
            spaceConsumed s (.memOp (.refByte fl)) [.number i, .number (w.toNat : Int)]) } := by
  have theGetD : ∀ o : Option Bool, miscThe false o = o.getD false := by
    intro o
    cases o <;> rfl
  simp only [doApp] at h
  simp [doSpace, DataLang.opSpaceReset, doAppAux, applyNonFfi, ClosSem.intToByte_toNat,
    doStack, doLimSafe] at h
  by_cases neg : i < 0
  · simp [neg] at h
  · simp [neg] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨_, rfl, rfl, by omega, ?_⟩
    simp only [State.mk.injEq, true_and, and_true]
    rw [Bool.eq_iff_iff]
    have lim : limSafe s.limits (.memOp (.refByte fl)) [.number i, .number (w.toNat : Int)] ↔
        (0 ≤ i ∧ i.toNat / (archSize s.limits / 8) < 2 ^ archSize s.limits / archSize s.limits ∧
          i.toNat / (archSize s.limits / 8) + 1 < 2 ^ s.limits.lengthLimit ∧
          smallNum s.limits.arch64Bit i) := by
      simp only [limSafe]
    simp only [Bool.and_eq_true, decide_eq_true_eq, theGetD, lim, gt_iff_lt]
    have nonneg : 0 ≤ i := by omega
    exact ⟨fun ⟨⟨⟨_, a⟩, sf, nt, hp⟩, st⟩ => ⟨⟨a, nt, sf, hp⟩, st⟩,
      fun ⟨⟨a, nt, sf, hp⟩, st⟩ => ⟨⟨⟨nonneg, a⟩, sf, nt, hp⟩, st⟩⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
