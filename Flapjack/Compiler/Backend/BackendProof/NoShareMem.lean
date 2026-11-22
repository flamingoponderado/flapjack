module

public import Flapjack.Compiler.Backend.BackendProof.CompileLab
public import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.CodeSafety
public import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Padding
public import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Encoding
public import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelUpdates
public import Flapjack.Compiler.Backend.LabToTarget.CodeSafetyFacts

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 3419-3545: the label-removal passes preserve the
absence of shared-memory instructions, so `compile_lab` adds no MMIO FFI
names. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `pad_code_no_share_mem_inst` (`backendProofScript.sml:3419-3428`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "pad_code_no_share_mem_inst"
  (words_as_type_indexed_bitvec)]
theorem padCode_noShareMemInst {width : Nat} [NeZero width]
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (nop : List (BitVec 8)) :
    noShareMemInst secList → noShareMemInst (padCode nop secList) := fun h =>
  codeSimilar_noShareMem secList (padCode nop secList)
    ⟨codeSimilar_padCode secList secList nop (codeSimilar_refl secList), h⟩

/-- Exact HOL `enc_sec_list_no_share_mem_inst` (`backendProofScript.sml:3430-3439`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "enc_sec_list_no_share_mem_inst"
  (words_as_type_indexed_bitvec)]
theorem encSecList_noShareMemInst {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (enc : HolAsm width → List (BitVec 8)) :
    noShareMemInst code → noShareMemInst (encSecList enc code) := fun h =>
  codeSimilar_noShareMem code (encSecList enc code)
    ⟨codeSimilar_sym _ _ ((codeSimilar_encSecList code code enc).mpr (codeSimilar_refl code)), h⟩

/-- Exact HOL `enc_secs_again_no_share_mem_inst` (`backendProofScript.sml:3441-3451`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "enc_secs_again_no_share_mem_inst"
  (words_as_type_indexed_bitvec)]
theorem encSecsAgain_noShareMemInst {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffiNames : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (secList code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    ∀ done : Bool, encSecsAgain pos labs ffiNames enc secList = (code, done) ∧
      noShareMemInst secList → noShareMemInst code := fun done ⟨he, h⟩ =>
  codeSimilar_noShareMem secList code
    ⟨encSecsAgain_implies_similar pos labs ffiNames enc secList code done he, h⟩

/-- Exact HOL `upd_lab_len_no_share_mem_inst` (`backendProofScript.sml:3453-3463`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "upd_lab_len_no_share_mem_inst"
  (words_as_type_indexed_bitvec)]
theorem updLabLen_noShareMemInst {width : Nat} [NeZero width]
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    ∀ pos : Nat, noShareMemInst secList → noShareMemInst (updLabLen pos secList) :=
  fun pos h =>
    codeSimilar_noShareMem secList (updLabLen pos secList)
      ⟨codeSimilar_sym _ _ ((codeSimilar_updLabLen secList pos secList).mpr
        (codeSimilar_refl secList)), h⟩

/-- Exact HOL `remove_labels_loop_no_share_mem_inst`
(`backendProofScript.sml:3465-3498`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "remove_labels_loop_no_share_mem_inst" (words_as_type_indexed_bitvec)]
theorem removeLabelsLoop_noShareMemInst {width : Nat} [NeZero width] :
    ∀ (cl : Nat) (conf : AsmConfigExact width) (pos : Nat) (initLabs : Spt (Spt Nat))
      (ffiNames : List HolFfiName)
      (secList code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
      (labs : Spt (Spt Nat)),
      removeLabelsLoop cl conf pos initLabs ffiNames secList = some (code, labs) ∧
        noShareMemInst secList → noShareMemInst code := by
  intro cl
  induction cl with
  | zero =>
    intro conf pos initLabs ffiNames secList code labs ⟨h, hs⟩
    rw [removeLabelsLoop] at h
    obtain ⟨s1, d1, he1⟩ : ∃ s d, encSecsAgain pos (computeLabelsAlt pos secList initLabs)
        ffiNames conf.encode secList = (s, d) := ⟨_, _, rfl⟩
    have hs1 := encSecsAgain_noShareMemInst _ _ _ _ _ _ d1 ⟨he1, hs⟩
    obtain ⟨s2, d2, he2⟩ : ∃ s d, encSecsAgain pos (computeLabelsAlt pos (updLabLen pos s1) initLabs)
        ffiNames conf.encode (updLabLen pos s1) = (s, d) := ⟨_, _, rfl⟩
    have hs2 := encSecsAgain_noShareMemInst _ _ _ _ _ _ d2
      ⟨he2, updLabLen_noShareMemInst s1 pos hs1⟩
    simp only [he1, he2] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact padCode_noShareMemInst _ _ hs2
      · cases h
    · simp at h
  | succ n ih =>
    intro conf pos initLabs ffiNames secList code labs ⟨h, hs⟩
    rw [removeLabelsLoop] at h
    obtain ⟨s1, d1, he1⟩ : ∃ s d, encSecsAgain pos (computeLabelsAlt pos secList initLabs)
        ffiNames conf.encode secList = (s, d) := ⟨_, _, rfl⟩
    have hs1 := encSecsAgain_noShareMemInst _ _ _ _ _ _ d1 ⟨he1, hs⟩
    obtain ⟨s2, d2, he2⟩ : ∃ s d, encSecsAgain pos (computeLabelsAlt pos (updLabLen pos s1) initLabs)
        ffiNames conf.encode (updLabLen pos s1) = (s, d) := ⟨_, _, rfl⟩
    have hs2 := encSecsAgain_noShareMemInst _ _ _ _ _ _ d2
      ⟨he2, updLabLen_noShareMemInst s1 pos hs1⟩
    simp only [he1, he2] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact padCode_noShareMemInst _ _ hs2
      · cases h
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at h
      exact ih conf pos initLabs ffiNames s1 code labs ⟨h, hs1⟩

/-- Exact HOL `compile_lab_no_share_mem_IMP_mmio_pcs_min_index`
(`backendProofScript.sml:3520-3545`). HOL `OPTION_ALL P o` is the match
`none ↦ True`, `some l ↦ P l`; `EVERY` is list membership quantification. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "compile_lab_no_share_mem_IMP_mmio_pcs_min_index" (words_as_type_indexed_bitvec)]
theorem compileLab_noShareMem_mmioPcsMinIndex {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : LabToTarget.Config)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (bytes : List (BitVec 8)) (c' : LabToTarget.Config) :
    compileLab asmConf c secList = some (bytes, c') ∧ noShareMemInst secList ∧
      (match c.ffiNames with
        | none => True
        | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s) →
    ∃ ffiNames, c'.ffiNames = some ffiNames ∧
      mmioPcsMinIndex ffiNames = some ffiNames.length := by
  rintro ⟨h, hns, hall⟩
  obtain ⟨ffis, hnone, secs', l1, hsel, hr, -, rfl⟩ := compileLab_some secList h
  have hns' : noShareMemInst secs' :=
    removeLabelsLoop_noShareMemInst _ _ _ _ _ _ _ _
      ⟨hr, encSecList_noShareMemInst secList asmConf.encode hns⟩
  have hsh := noShareMem_getShmemInfo secs' c.pos [] [] hns'
  refine ⟨ffis ++ (getShmemInfo secs' c.pos [] []).1, rfl, ?_⟩
  rw [hsh]
  have hffis : ∀ x ∈ ffis, ∃ s, x = HolFfiName.extCall s := by
    rcases hsel with hc | hc
    · rw [hc] at hall
      exact hall
    · rw [hnone hc]
      exact findFfiNamesEvery secList _ rfl
  have := mmioPcsMinIndex_append [] ffis ⟨fun x hx => (nomatch hx), hffis⟩
  simpa only [List.append_nil] using this

end Flapjack.Compiler.Backend.BackendProof
