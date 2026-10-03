import Flapjack.Compiler.Backend.LabToTarget.CodeSafety
import Flapjack.Compiler.Backend.LabToTarget.Fetch
import Flapjack.Compiler.Backend.LabToTarget.PositionOrder
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
import Flapjack.Compiler.Backend.LabToTarget.MmioClassification
import Flapjack.Misc.FindIndex
import Flapjack.Misc.FindIndex.Membership
import Flapjack.Compiler.Backend.LabToTarget.Positions
import Flapjack.Compiler.Backend.Semantics.TargetSem.State

/-! Original shared-memory/Install exclusion facts used by `compile_correct`
(lab_to_targetProofScript.sml:7159-7438): append closure, the Install/MMIO
boundary, the absent shared-memory info and the FFI-entry PC exclusion. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps Flapjack.Misc

/-- A successful first-match search returns the position of its target;
Flapjack infrastructure for HOL's `find_index_INDEX_OF`/`INDEX_OF_eq_SOME`. -/
theorem findIndex_holEl {α : Type} [DecidableEq α] [Nonempty α] (x : α) (l : List α)
    (off i : Nat) (h : findIndex x l off = some i) : off ≤ i ∧ holEl (i - off) l = x := by
  induction l generalizing off with
  | nil => simp [findIndex] at h
  | cons y ys ih =>
    simp only [findIndex] at h
    split at h
    · next hy =>
      cases h
      simpa [holEl, holHd] using hy
    · obtain ⟨h1, h2⟩ := ih (off + 1) h
      refine ⟨by omega, ?_⟩
      have : i - off = (i - (off + 1)) + 1 := by omega
      rw [this]
      simpa [holEl] using h2

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "ffi_entry_pcs_NOT_ccache_OR_halt_pc" (words_as_type_indexed_bitvec)]
theorem ffiEntryPcs_not_ccache_or_halt {width : Nat} [NeZero width] {S Q : Type}
    (pc : BitVec width) (mc : MachineConfig width S Q) (index : Nat) :
    findIndex pc mc.ffiEntryPcs 0 = some index ∧
      mc.haltPc ≠ holEl index mc.ffiEntryPcs ∧
      mc.ccachePc ≠ holEl index mc.ffiEntryPcs →
    pc ≠ mc.ccachePc ∧ pc ≠ mc.haltPc := by
  rintro ⟨hf, hh, hc⟩
  have he := (findIndex_holEl pc mc.ffiEntryPcs 0 index hf).2
  rw [Nat.sub_zero] at he
  rw [he] at hh hc
  exact ⟨fun e => hc e.symm, fun e => hh e.symm⟩

/-- An in-range total element is a member; Flapjack infrastructure. -/
theorem holEl_mem {α : Type} [Nonempty α] (l : List α) (i : Nat) (h : i < l.length) :
    holEl i l ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons y ys ih =>
    cases i with
    | zero => simp [holEl, holHd]
    | succ i => simpa [holEl] using List.mem_cons_of_mem y (ih i (by simpa using h))

private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_share_mem_lemma"
  (words_as_type_indexed_bitvec)]
theorem noShareMem_lemma {width : Nat} [NeZero width] (ffiNames : List HolFfiName)
    (i pc : Nat) (code : LabProgHOL width) (c : BitVec width) (l : List (BitVec 8)) (n : Nat) :
    mmioPcsMinIndex ffiNames = some i ∧
      asmFetchAux pc code = some (.labAsm .install c l n) ∧
      noInstallOrNoShareMem code ffiNames →
    i = ffiNames.length := by
  rintro ⟨hm, hf, hn⟩
  obtain ⟨hle, -, hsh⟩ := mmioPcsMinIndex_isSome ffiNames i hm
  rcases Nat.lt_or_ge i ffiNames.length with hlt | hge
  case inr => omega
  exfalso
  obtain ⟨op, hop⟩ := hsh i ⟨Nat.le_refl i, hlt⟩
  rcases hn with ⟨-, hext⟩ | hni
  · obtain ⟨name, hname⟩ := hext _ (holEl_mem ffiNames i hlt)
    rw [hop] at hname
    cases hname
  · exact hni pc c l n hf

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EL_get_ffi_index_MEM"]
theorem el_getFfiIndex_mem {α : Type} [DecidableEq α] [Nonempty α] (s : α) (ls : List α) :
    s ∈ ls → holEl (getFfiIndex ls s) ls = s := by
  intro h
  obtain ⟨index, hf, -, -⟩ := findIndex_mem ls s 0 h
  rw [Nat.zero_add] at hf
  have := (findIndex_holEl s ls 0 index hf).2
  rw [Nat.sub_zero] at this
  simp [getFfiIndex, hf, this]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "ffi_name_NOT_Mapped"]
theorem ffiName_not_mapped (ffiNames : List HolFfiName) (i : Nat) (s : HolFfiName) :
    mmioPcsMinIndex ffiNames = some i ∧ (∃ str, s = .extCall str) ∧ s ∈ ffiNames →
    getFfiIndex ffiNames s < i := by
  rintro ⟨hm, ⟨str, rfl⟩, hmem⟩
  obtain ⟨index, hf, hlt, -⟩ := findIndex_mem ffiNames (HolFfiName.extCall str) 0 hmem
  rw [Nat.zero_add] at hf
  have hidx : getFfiIndex ffiNames (.extCall str) = index := by simp [getFfiIndex, hf]
  have hel := el_getFfiIndex_mem _ _ hmem
  rw [hidx] at hel ⊢
  obtain ⟨-, -, hsh⟩ := mmioPcsMinIndex_isSome ffiNames i hm
  rcases Nat.lt_or_ge index i with h | h
  · exact h
  · obtain ⟨op, hop⟩ := hsh index ⟨h, hlt⟩
    rw [hel] at hop
    cases hop

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_share_mem_APPEND"
  (words_as_type_indexed_bitvec)]
theorem noShareMem_append {width : Nat} [NeZero width] (code secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    noShareMemInst code ∧ noShareMemInst secs → noShareMemInst (code ++ secs) := by
  rintro ⟨hc, hs⟩ p op re a inst len hf
  by_cases hp : p < numPcs code
  · rw [asmFetchAux_append1 p code secs hp] at hf
    exact hc p op re a inst len hf
  · have : p = (p - numPcs code) + numPcs code := by omega
    rw [this, asmFetchAux_append2] at hf
    exact hs _ op re a inst len hf

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "no_install_APPEND_IMP"
  (words_as_type_indexed_bitvec)]
theorem noInstall_append_imp {width : Nat} [NeZero width] (code secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    noInstall (code ++ secs) → noInstall code ∧ noInstall secs := by
  intro h
  refine ⟨fun p w bytes l hf => ?_, fun p w bytes l hf => ?_⟩
  · have hp := asmFetchAux_some_ltNumPcs p code _ hf
    exact h p w bytes l (by rw [asmFetchAux_append1 p code secs hp]; exact hf)
  · exact h (p + numPcs code) w bytes l (by rw [asmFetchAux_append2]; exact hf)

/-- Fetch-based exclusions descend to the code after the first line; Flapjack
infrastructure for the original `get_shmem_info_ind` induction. -/
theorem noShareMemInst_tail {width : Nat} [NeZero width] (k : Nat) (x : LabLineHOL width)
    (xs : List (LabLineHOL width)) (rest : LabProgHOL width)
    (h : noShareMemInst (⟨k, x :: xs⟩ :: rest)) : noShareMemInst (⟨k, xs⟩ :: rest) := by
  intro p op re a inst len hf
  by_cases hl : isLabelHOL x = true
  · exact h p op re a inst len (by simpa [asmFetchAux, hl] using hf)
  · exact h (p + 1) op re a inst len (by simpa [asmFetchAux, hl] using hf)

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "no_share_mem_IMP_get_shmem_info" (words_as_type_indexed_bitvec)]
theorem noShareMem_getShmemInfo {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (p : Nat) (ffiNames : List HolFfiName) (shmemInfo : List ShmemInfoNum) :
    noShareMemInst code → getShmemInfo code p ffiNames shmemInfo = (ffiNames, shmemInfo) := by
  fun_induction getShmemInfo code p ffiNames shmemInfo with
  | case1 => intro _; rfl
  | case2 _ _ _ _ _ ih =>
    intro h
    exact ih (fun q op re a inst len hf => h q op re a inst len (by simpa [asmFetchAux] using hf))
  | case4 _ _ _ k m r base off bytes len xs rest _ _ _ _ =>
    intro h
    exact absurd (by simp [asmFetchAux, isLabelHOL]) (h 0 m r (.addr base off) bytes len)
  | case3 _ _ _ _ _ _ _ _ _ ih => exact fun h => ih (noShareMemInst_tail _ _ _ _ h)
  | case5 _ _ _ _ _ _ _ _ _ _ ih => exact fun h => ih (noShareMemInst_tail _ _ _ _ h)
  | case6 _ _ _ _ _ _ _ _ _ _ ih => exact fun h => ih (noShareMemInst_tail _ _ _ _ h)

end Flapjack.Compiler.Backend.LabToTarget
