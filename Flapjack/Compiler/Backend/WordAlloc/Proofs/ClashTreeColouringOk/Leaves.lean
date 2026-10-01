import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Motive
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ReadsLiveExpressions

/-!
# `clash_tree_colouring_ok` statement cases

The `Delta` statement cases of `word_allocProofScript.sml:2813-3309`
`clash_tree_colouring_ok`: `Skip`, `Move`, `Assign`, `Get`, `Set`, `Store`,
`Tick`, `Raise`, `Return`, `LocValue`, `OpCurrHeap`, `StoreConsts`,
`CodeBufferWrite` and `DataBufferWrite`. Each reduces to the common `Delta`
step (`deltaConcl`) with the statement's writes and its `get_live` equation.
-/

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc

/-- `numset_list_insert` of an expression's reads is the union with its live set
(HOL `numset_list_insert_eq_UNION` with `wf_get_live_exp` and
`get_reads_exp_get_live_exp`; Flapjack infrastructure). -/
theorem insertReadsEqUnion {width : Nat} [NeZero width] (e : WordLangExpHOL (BitVec width))
    (t : NumSet) (ht : sptWf t = true) :
    numsetListInsert (getReadsExpHOL e) t = sptUnion (getLiveExp e) t :=
  numsetListInsertEqUnion t (getLiveExp e) (getReadsExpHOL e)
    ⟨ht, wfGetLiveExp e, (getReadsExpGetLiveExp e).symm⟩

/-- The domain of a single write (Flapjack infrastructure). -/
theorem writesSingle (v k : Nat) : sptDomain (sptInsert v () (.ln : NumSet)) k ↔ k ∈ [v] := by
  show sptDomain (numsetListInsert [v] .ln) k ↔ _
  rw [domainNumsetListInsert]
  simp [sptDomain, sptLookup]


/-- HOL `clash_tree_colouring_ok`, `Skip` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Skip {width : Nat} [NeZero width] :
    clashTreeGoal (.skip : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f [] [] live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun _ => by rw [getLive]; rfl) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `Tick` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Tick {width : Nat} [NeZero width] :
    clashTreeGoal (.tick : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f [] [] live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun _ => by rw [getLive]; rfl) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `Move` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Move {width : Nat} [NeZero width]
    (pri : Nat) (moves : List (Nat × Nat)) :
    clashTreeGoal (.move pri moves : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by
      rw [getWrites, domainNumsetListInsert]
      simp [sptDomain, sptLookup])
    (fun hw => by rw [getLive, wfNumsetListDeleteEq _ live hw]) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `Assign` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Assign {width : Nat} [NeZero width]
    (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.assign v e : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => writesSingle _ k)
    (fun hw => by rw [getLive]; exact insertReadsEqUnion e _ (sptWfDelete live v hw)) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `Get` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Get {width : Nat} [NeZero width] (v : Nat) (name : WordStoreHOL) :
    clashTreeGoal (.get v name : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => writesSingle _ k)
    (fun _ => by rw [getLive]; rfl) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `Set` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Set {width : Nat} [NeZero width]
    (name : WordStoreHOL) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.set name e : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun hw => by rw [getLive]; exact insertReadsEqUnion e live hw) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `Store` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Store {width : Nat} [NeZero width]
    (e : WordLangExpHOL (BitVec width)) (v : Nat) :
    clashTreeGoal (.store e v : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun hw => by
      rw [getLive]
      show sptInsert v () (numsetListInsert _ live) = _
      rw [insertReadsEqUnion e live hw]) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `Raise` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Raise {width : Nat} [NeZero width] (n : Nat) :
    clashTreeGoal (.raise n : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun _ => by rw [getLive]; rfl) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `Return` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Return {width : Nat} [NeZero width] (n : Nat) (ns : List Nat) :
    clashTreeGoal (.return n ns : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun _ => by rw [getLive]; rfl) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `LocValue` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_LocValue {width : Nat} [NeZero width] (r l : Nat) :
    clashTreeGoal (.locValue r l : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => writesSingle _ k)
    (fun _ => by rw [getLive]; rfl) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `OpCurrHeap` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_OpCurrHeap {width : Nat} [NeZero width] (b : BinOp) (dst src : Nat) :
    clashTreeGoal (.opCurrHeap b dst src : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => writesSingle _ k)
    (fun _ => by rw [getLive]; rfl) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `CodeBufferWrite` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_CodeBufferWrite {width : Nat} [NeZero width] (r1 r2 : Nat) :
    clashTreeGoal (.codeBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun _ => by rw [getLive]; rfl) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `DataBufferWrite` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_DataBufferWrite {width : Nat} [NeZero width] (r1 r2 : Nat) :
    clashTreeGoal (.dataBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun _ => by rw [getLive]; rfl) Iff.rfl

/-- HOL `clash_tree_colouring_ok`, `StoreConsts` case: the deleted then reinserted
`c` and `d` give the same well-formed tree (HOL `spt_eq_thm`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_StoreConsts {width : Nat} [NeZero width]
    (a b c d : Nat) (ws : List (Bool × BitVec width)) :
    clashTreeGoal (.storeConsts a b c d ws : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by
      rw [getWrites]
      show sptDomain (numsetListInsert [a, b, c, d] .ln) k ↔ _
      rw [domainNumsetListInsert]
      simp [sptDomain, sptLookup])
    (fun hw => by
      rw [getLive]
      have hw1 : sptWf (sptDelete a (sptDelete b live)) = true :=
        sptWfDelete _ a (sptWfDelete live b hw)
      have hw2 : sptWf (numsetListDelete [a, b, c, d] live) = true :=
        (numsetListDeleteSwap [a, b, c, d] 0 live hw).1
      rw [sptEqThm _ _ ⟨sptWf_numsetListInsert _ hw2 [c, d],
        sptWfInsert c () _ (sptWfInsert d () _ hw1)⟩]
      intro k
      simp only [numsetListInsert, numsetListDelete]
      by_cases hc : k = c
      · subst hc; rw [sptLookup_sptInsert_same, sptLookup_sptInsert_same]
      rw [sptLookup_sptInsert_ne _ _ _ _ hc, sptLookup_sptInsert_ne _ _ _ _ hc]
      by_cases hd' : k = d
      · subst hd'; rw [sptLookup_sptInsert_same, sptLookup_sptInsert_same]
      rw [sptLookup_sptInsert_ne _ _ _ _ hd', sptLookup_sptInsert_ne _ _ _ _ hd']
      simp only [sptLookup_sptDelete, hc, hd', if_false]
      by_cases ha : k = a <;> by_cases hb : k = b <;> simp [ha, hb]) Iff.rfl


end Flapjack.WordAlloc
