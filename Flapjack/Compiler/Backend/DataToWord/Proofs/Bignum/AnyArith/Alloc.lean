module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Prefix
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.Multiword
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.StateRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutLocals
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateInsert
public import Flapjack.Misc.Sptree.FromList.Domain
public import Flapjack.Misc.Sptree.MkWf
public import Flapjack.Misc.Sptree.Wf

@[expose] public section

/-! `AnyArith_thm`, the allocation step (Flapjack-only helpers following the
HOL proof). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.WordSemStateFiniteExact.BignumClauses

theorem getVars_three {α : Type} {l : Spt α} {a b c : α}
    (h : DataSem.getVars [0, 1, 2] l = some [a, b, c]) :
    DataSem.getVar 0 l = some a ∧ DataSem.getVar 1 l = some b ∧ DataSem.getVar 2 l = some c := by
  simp only [DataSem.getVars] at h
  cases h0 : DataSem.getVar 0 l <;> cases h1 : DataSem.getVar 1 l <;>
    cases h2 : DataSem.getVar 2 l <;> simp_all

theorem names_three : (sptListInsert [0, 1, 2] .ln : NumSet) = sptFromList [(), (), ()] := rfl

theorem cutEnv_three {α : Type} {l : Spt α} {a b c : α}
    (h : DataSem.getVars [0, 1, 2] l = some [a, b, c]) :
    DataSem.cutEnv (sptFromList [(), (), ()]) l = some (sptFromList [a, b, c]) := by
  obtain ⟨h0, h1, h2⟩ := getVars_three h
  simp only [DataSem.getVar] at h0 h1 h2
  unfold DataSem.cutEnv
  rw [if_pos]
  · congr 1
    apply (sptEqThm _ _ ⟨sptWf_mkWf _, by
      simp only [sptFromList, List.foldl]
      exact sptWfInsert _ _ _ (sptWfInsert _ _ _ (sptWfInsert _ _ _ rfl))⟩).2
    intro n
    rw [sptLookup_mkWf, sptLookup_sptInterCases, sptLookupFromList, sptLookupFromList]
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 2 < n by omega) with e | e | e | e
    · subst e; simp [h0]
    · subst e; simp [h1]
    · subst e; simp [h2]
    · have : ¬ n < 3 := by omega
      simp [this]
  · intro key hk
    rw [sptMem_iff_lookup, sptLookupFromList] at hk
    obtain ⟨_, hk⟩ := hk
    rw [sptMem_iff_lookup]
    split at hk
    · rename_i hb
      rcases (show key = 0 ∨ key = 1 ∨ key = 2 by simp at hb; omega) with e | e | e <;>
        subst e <;> simp_all
    · simp at hk


/-- Operand length bound from the state relation. -/
theorem lenSize_bound {width : Nat} [NeZero width] {C F : Type} {c : Config} {l1 l2 : Nat}
    {s : DataSem.State C F} {t : WordSemStateFiniteExact width C F} {locs : List (Nat × Nat)}
    (rel : stateRel c l1 l2 s t none locs) : c.lenSize + 7 < width := by
  obtain ⟨_, _, _, _, _, _, a, _, _⟩ := rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact a.2.2.2.2.1

/-- `bignum_size` is one more than the operand's word count (HOL: `bignum_size_def`,
`limits_inv_def`, `bignum_digits_LENGTH_n2mw`). -/
theorem bignumSize_eq {width : Nat} [NeZero width] {C F : Type} {c : Config} {l1 l2 : Nat}
    {s : DataSem.State C F} {t : WordSemStateFiniteExact width C F} {locs : List (Nat × Nat)}
    (rel : stateRel c l1 l2 s t none locs) (i : Int) :
    DataSem.bignumSize s.limits.arch64Bit i =
      (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length + 1 := by
  have good : goodDimindex width := rel.2.2.2.2.2.2.1
  have arch : s.limits.arch64Bit = decide (width = 64) :=
    rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  rw [DataSem.bignumSize, arch, bignumDigits_length_n2mw good]
  simp [Misc.Multiword.i2mw]
  omega

/-- The numeric value of the size word. -/
theorem sizeWord_toNat {width : Nat} [NeZero width] {C F : Type} {c : Config} {l1 l2 : Nat}
    {s : DataSem.State C F} {t : WordSemStateFiniteExact width C F} {locs : List (Nat × Nat)}
    {i j : Int} (rel : stateRel c l1 l2 s t none locs)
    (hi : DataSem.getVar 0 s.locals = some (.number i))
    (hj : DataSem.getVar 1 s.locals = some (.number j)) :
    (sizeWord width i j).toNat =
      4 + 4 * (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length +
        4 * (Misc.Multiword.i2mw j : Bool × List (BitVec width)).2.length ∧
    4 + 4 * (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length +
        4 * (Misc.Multiword.i2mw j : Bool × List (BitVec width)).2.length < 2 ^ width / 2 := by
  have good : goodDimindex width := rel.2.2.2.2.2.2.1
  have bi := stateRel_imp_numSizeLimit c l1 l2 s t locs 0 i ⟨rel, hi⟩
  have bj := stateRel_imp_numSizeLimit c l1 l2 s t locs 1 j ⟨rel, hj⟩
  simp only [sizeWord]
  generalize (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length = il at bi ⊢
  generalize (Misc.Multiword.i2mw j : Bool × List (BitVec width)).2.length = jl at bj ⊢
  have big : 64 ≤ 2 ^ width / 16 ∧ 2 ^ width / 16 * 16 = 2 ^ width := by
    rcases good with h | h <;> subst h <;> norm_num
  have lt : 4 + 4 * il + 4 * jl < 2 ^ width / 2 := by omega
  refine ⟨?_, lt⟩
  have h4 : (4 : BitVec width).toNat = 4 := by
    show (BitVec.ofNat width 4).toNat = 4
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h4]
  rw [Nat.mod_eq_of_lt (show 4 * il < 2 ^ width by omega),
    Nat.mod_eq_of_lt (show 4 * jl < 2 ^ width by omega),
    Nat.mod_eq_of_lt (show 4 + 4 * il < 2 ^ width by omega),
    Nat.mod_eq_of_lt (show 4 + 4 * il + 4 * jl < 2 ^ width by omega)]

/-- The `AllocVar` step of `AnyArith_code`. -/
theorem alloc_step {width : Nat} [NeZero width] {C F : Type} {c : Config} {l1 l2 : Nat}
    {s : DataSem.State C F} {t r : WordSemStateFiniteExact width C F} {locs : List (Nat × Nat)}
    {i j : Int} {opIndex : Nat} {q : Option (WordSemResult width)}
    (rel : stateRel c l1 l2 s t none locs)
    (gv : DataSem.getVars [0, 1, 2] s.locals =
      some [.number i, .number j, .number (opIndex : Int)])
    (run : WordSemStateFiniteExact.evaluate (allocVar c (2 ^ c.lenSize) (sptListInsert [0, 1, 2] .ln))
      ((t.setVar 1 (.word (sizeWord width i j))).setStore (.temp 29)
        (.word (sizeWord width i j))) = (q, r)) :
    (q = some .notEnoughSpace → r.ffi = t.ffi ∧
      (c.gcKind ≠ .none ∧ DataSem.noThunksInRefs s.refs →
        let il := DataSem.bignumSize s.limits.arch64Bit i
        let jl := DataSem.bignumSize s.limits.arch64Bit j
        il + jl ≤ 2 ^ c.lenSize →
          s.limits.heapLimit <
            il + jl + DataSem.sizeOfHeap (cutLocals (sptFromList [(), (), ()]) s))) ∧
    (q ≠ some .notEnoughSpace → q = none ∧
      stateRel c l1 l2
        { s with locals := sptFromList [.number i, .number j, .number (opIndex : Int)],
                 space := (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length +
                   (Misc.Multiword.i2mw j : Bool × List (BitVec width)).2.length + 2 }
        r none locs ∧
      r.store.lookup (.temp 29) = some (.word (sizeWord width i j)) ∧ r.code = t.code) := by
  obtain ⟨hi, hj, _⟩ := getVars_three gv
  obtain ⟨hw, _⟩ := sizeWord_toNat rel hi hj
  have lsz := lenSize_bound rel
  have rel4 : stateRel c l1 l2 s ((t.setVar 1 (.word (sizeWord width i j))).setStore (.temp 29)
      (.word (sizeWord width i j))) none locs := by
    rw [stateRel_setStore_temp]
    exact (stateRel_insert_1 c l1 l2 s t none locs _).symm ▸ rel
  have cut := cutEnv_three gv
  rw [← names_three] at cut
  have limLt : 2 ^ c.lenSize < 2 ^ width / 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.pow_div (by omega) (by norm_num)]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have read : ((t.setVar 1 (.word (sizeWord width i j))).setStore (.temp 29)
      (.word (sizeWord width i j))).getVar 1 = some (.word (sizeWord width i j)) := by
    simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  have av := allocVar_thm ⟨rel4, cut, read, run, limLt⟩
  have bsi := bignumSize_eq rel i
  have bsj := bignumSize_eq rel j
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · obtain ⟨ffi, _, bound⟩ := av.1 hq
    refine ⟨ffi.trans rel.1.symm, ?_⟩
    rintro ⟨gc, thunks⟩
    simp only [bsi, bsj]
    intro le
    rw [← names_three]
    have := bound ⟨gc, by rw [hw]; omega, thunks⟩
    rw [hw] at this
    omega
  · obtain ⟨_, rel1, t29, code, _, _, _, qn⟩ := av.2 hq
    refine ⟨qn, ?_, ?_, code⟩
    · have : (sizeWord width i j).toNat / 4 + 1 =
          (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length +
            (Misc.Multiword.i2mw j : Bool × List (BitVec width)).2.length + 2 := by
        rw [hw]; omega
      rw [← this]
      exact rel1
    · rw [t29]
      simp [WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar, FUPDATE_HOL]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
