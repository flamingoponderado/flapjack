import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Leaves

/-!
# `clash_tree_colouring_ok` `Inst` case

The `Inst` case of `word_allocProofScript.sml:2813-3309` `clash_tree_colouring_ok`
(proof `word_allocProofScript.sml:2840-2975`): every instruction's clash tree is
a single `get_delta_inst` `Delta`, whose writes are `get_writes_inst` and whose
`Delta` result is `get_live_inst` (HOL compares the trees with `spt_eq_thm`).
The untagged helpers are Flapjack proof infrastructure for the tagged case.
-/

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm

/-- Lookup through an insertion (Flapjack infrastructure). -/
theorem sptLookup_sptInsert_ite {α : Type} (k n : Nat) (v : α) (t : Spt α) :
    sptLookup k (sptInsert n v t) = if k = n then some v else sptLookup k t := by
  by_cases h : k = n
  · subst h; rw [sptLookup_sptInsert_same, if_pos rfl]
  · rw [sptLookup_sptInsert_ne n k v t h, if_neg h]

/-- Domain of an insertion (Flapjack infrastructure). -/
theorem sptDomain_sptInsert_iff {α : Type} (k n : Nat) (v : α) (t : Spt α) :
    sptDomain (sptInsert n v t) k ↔ k = n ∨ sptDomain t k := by
  unfold sptDomain
  rw [sptLookup_sptInsert_ite]
  by_cases h : k = n <;> simp [h]

theorem sptDomain_ln_iff {α : Type} (k : Nat) : sptDomain (Spt.ln : Spt α) k ↔ False := by
  simp [sptDomain, sptLookup]

/-- Every instruction's `get_delta_inst` is a `Delta` whose writes are
`get_writes_inst` and whose result is `get_live_inst` on a well-formed live set
(Flapjack infrastructure; HOL's per-instruction `Inst` sub-cases). -/
theorem instDelta {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (live : NumSet) (hw : sptWf live = true) :
    ∃ w r, getDeltaInst (HolInst.ofWordLangInst i) = .delta w r ∧
      (∀ k, sptDomain (getWritesInst i) k ↔ k ∈ w) ∧
      numsetListInsert r (numsetListDelete w live) = getLiveInst i live := by
  have hwD : ∀ w : List Nat, sptWf (numsetListDelete w live) = true :=
    fun w => (numsetListDeleteSwap w 0 live hw).1
  cases i with
  | skip => exact ⟨[], [], rfl, fun k => by simp [getWritesInst, sptDomain_ln_iff], rfl⟩
  | const r v =>
      refine ⟨[r], [], rfl, fun k => by simp [getWritesInst, sptDomain_sptInsert_iff,
        sptDomain_ln_iff], rfl⟩
  | arith a =>
      cases a with
      | binop op r1 r2 ri =>
          cases ri with
          | reg r3 =>
              refine ⟨[r1], [r2, r3], rfl, fun k => by simp [getWritesInst,
                sptDomain_sptInsert_iff, sptDomain_ln_iff], ?_⟩
              simp only [getLiveInst, getLiveInstCore]
              rw [sptEqThm _ _ ⟨sptWf_numsetListInsert _ (hwD _) _,
                sptWfInsert _ _ _ (sptWfInsert _ _ _ (sptWfDelete _ _ hw))⟩]
              intro k
              simp only [lookupNumsetListInsert, numsetListDelete,
                sptLookup_sptInsert_ite, sptLookup_sptDelete, List.mem_cons, List.mem_nil_iff,
                or_false]
              (repeat' split) <;> simp_all
          | imm c => exact ⟨[r1], [r2], rfl, fun k => by simp [getWritesInst,
                sptDomain_sptInsert_iff, sptDomain_ln_iff], rfl⟩
      | shift op r1 r2 ri =>
          cases ri with
          | reg r3 =>
              refine ⟨[r1], [r2, r3], rfl, fun k => by simp [getWritesInst,
                sptDomain_sptInsert_iff, sptDomain_ln_iff], ?_⟩
              simp only [getLiveInst, getLiveInstCore]
              rw [sptEqThm _ _ ⟨sptWf_numsetListInsert _ (hwD _) _,
                sptWfInsert _ _ _ (sptWfInsert _ _ _ (sptWfDelete _ _ hw))⟩]
              intro k
              simp only [lookupNumsetListInsert, numsetListDelete,
                sptLookup_sptInsert_ite, sptLookup_sptDelete, List.mem_cons, List.mem_nil_iff,
                or_false]
              (repeat' split) <;> simp_all
          | imm c => exact ⟨[r1], [r2], rfl, fun k => by simp [getWritesInst,
                sptDomain_sptInsert_iff, sptDomain_ln_iff], rfl⟩
      | div r1 r2 r3 =>
          refine ⟨[r1], [r3, r2], rfl, fun k => by simp [getWritesInst, sptDomain_sptInsert_iff,
            sptDomain_ln_iff], rfl⟩
      | addCarry r1 r2 r3 r4 =>
          refine ⟨[r1, r4], [r4, r3, r2], rfl, fun k => by simp [getWritesInst,
            sptDomain_sptInsert_iff, sptDomain_ln_iff, or_comm], ?_⟩
          simp only [getLiveInst, getLiveInstCore]
          rw [sptEqThm _ _ ⟨sptWf_numsetListInsert _ (hwD _) _,
            sptWfInsert _ _ _ (sptWfInsert _ _ _ (sptWfInsert _ _ _ (sptWfDelete _ _ hw)))⟩]
          intro k
          simp only [lookupNumsetListInsert, numsetListDelete,
            sptLookup_sptInsert_ite, sptLookup_sptDelete, List.mem_cons, List.mem_nil_iff,
            or_false]
          (repeat' split) <;> simp_all
      | addOverflow r1 r2 r3 r4 =>
          refine ⟨[r1, r4], [r3, r2], rfl, fun k => by simp [getWritesInst,
            sptDomain_sptInsert_iff, sptDomain_ln_iff, or_comm], ?_⟩
          simp only [getLiveInst, getLiveInstCore]
          rw [sptEqThm _ _ ⟨sptWf_numsetListInsert _ (hwD _) _,
            sptWfInsert _ _ _ (sptWfInsert _ _ _ (sptWfDelete _ _ (sptWfDelete _ _ hw)))⟩]
          intro k
          simp only [lookupNumsetListInsert, numsetListDelete,
            sptLookup_sptInsert_ite, sptLookup_sptDelete, List.mem_cons, List.mem_nil_iff,
            or_false]
          (repeat' split) <;> simp_all
      | subOverflow r1 r2 r3 r4 =>
          refine ⟨[r1, r4], [r3, r2], rfl, fun k => by simp [getWritesInst,
            sptDomain_sptInsert_iff, sptDomain_ln_iff, or_comm], ?_⟩
          simp only [getLiveInst, getLiveInstCore]
          rw [sptEqThm _ _ ⟨sptWf_numsetListInsert _ (hwD _) _,
            sptWfInsert _ _ _ (sptWfInsert _ _ _ (sptWfDelete _ _ (sptWfDelete _ _ hw)))⟩]
          intro k
          simp only [lookupNumsetListInsert, numsetListDelete,
            sptLookup_sptInsert_ite, sptLookup_sptDelete, List.mem_cons, List.mem_nil_iff,
            or_false]
          (repeat' split) <;> simp_all
      | longMul r1 r2 r3 r4 =>
          refine ⟨[r1, r2], [r4, r3], rfl, fun k => by simp [getWritesInst,
            sptDomain_sptInsert_iff, sptDomain_ln_iff, or_comm], rfl⟩
      | longDiv r1 r2 r3 r4 r5 =>
          refine ⟨[r1, r2], [r5, r4, r3], rfl, fun k => by simp [getWritesInst,
            sptDomain_sptInsert_iff, sptDomain_ln_iff, or_comm], rfl⟩
  | mem op r ad =>
      cases ad with
      | addr a off =>
      cases op
      all_goals first
        | exact ⟨[r], [a], rfl, fun k => by simp [getWritesInst, sptDomain_sptInsert_iff,
            sptDomain_ln_iff], rfl⟩
        | exact ⟨[], [r, a], rfl, fun k => by simp [getWritesInst, sptDomain_ln_iff],
            wfInsertSwap live r a hw⟩
        | exact ⟨[], [], rfl, fun k => by simp [getWritesInst, sptDomain_ln_iff], rfl⟩
/-- HOL `clash_tree_colouring_ok`, `Inst` case (`word_allocProofScript.sml:2840-2975`):
the HOL premises at `Inst i` and the five HOL conclusions; no sub-program, no
IH, no extra premise. -/
theorem clashTreeColouringOk_Inst {width : Nat} [NeZero width]
    (i : WordLangInst (BitVec width)) :
    clashTreeGoal (.inst i : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  obtain ⟨w, r, hdl, hW, hL⟩ := instDelta i live hw
  rw [hdl] at hc
  exact deltaConcl _ f w r live flive livein flivein lt hw hd hi hc hW
    (fun _ => by rw [getLive]; exact hL) Iff.rfl

end Flapjack.WordAlloc
