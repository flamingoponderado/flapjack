import Flapjack.HolRef
import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Backend.LabToTarget.FindFfiNamesEvery
import Flapjack.Compiler.Backend.LabToTarget.MmioShmem

/-! backendProofScript.sml: the two `lab_to_target$compile_lab` output facts
used by the Pancake top-level correctness theorem
(`pan_to_targetProof$pan_to_target_compile_semantics`). -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Basis.Pure.MlString

/-- Inversion of a successful `compile_lab` (Flapjack infrastructure): the
selected FFI list, the label-removed sections and the updated configuration. -/
theorem compileLab_some {width : Nat} [NeZero width] {asmConf : AsmConfigExact width}
    {c : LabToTarget.Config}
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    {bytes : List (BitVec 8)} {c' : LabToTarget.Config}
    (h : compileLab asmConf c secs = some (bytes, c')) :
    ∃ ffis : List HolFfiName, (c.ffiNames = none → ffis = findFfiNames secs) ∧
      ∃ secs' l1, (c.ffiNames = some ffis ∨ c.ffiNames = none) ∧
        removeLabels c.initClock asmConf c.pos c.labels ffis secs = some (secs', l1) ∧
        bytes = progToBytes secs' ∧
        c' = { c with
          labels := l1
          pos := (progToBytes secs').length + c.pos
          secPosLen := getSymbols c.pos secs'
          ffiNames := some (ffis ++ (getShmemInfo secs' c.pos [] []).1)
          shmemExtra := (getShmemInfo secs' c.pos [] []).2 } := by
  unfold compileLab at h
  cases hc : c.ffiNames with
  | none =>
    simp only [hc, if_true] at h
    split at h
    · rename_i secs' l1 _
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, (fun _ => rfl), secs', l1, Or.inr rfl, by assumption, rfl, rfl⟩
    · cases h
  | some ffis =>
    simp only [hc] at h
    split at h
    · split at h
      · rename_i secs' l1 _
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ffis, (fun h => nomatch h), secs', l1, Or.inl rfl, by assumption, rfl, rfl⟩
      · cases h
    · cases h

/-- Full original compile_lab_LENGTH (`backendProofScript.sml:1215-1221`):
`compile_lab asm_conf c secs = SOME (bytes, c') ⇒ c'.pos = LENGTH bytes + c.pos`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileLabLENGTH {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : LabToTarget.Config)
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (bytes : List (BitVec 8)) (c' : LabToTarget.Config) :
    compileLab asmConf c secs = some (bytes, c') → c'.pos = bytes.length + c.pos := by
  intro h
  obtain ⟨ffis, -, secs', l1, -, -, hb, rfl⟩ := compileLab_some secs h
  subst hb
  rfl

/-- Full original compile_lab_IMP_mmio_pcs_min_index
(`backendProofScript.sml:3500-3519`): when every configured FFI name is an
`ExtCall`, `compile_lab` returns FFI names whose MMIO minimum index exists.
HOL `OPTION_ALL P o` is the match `none ↦ True`, `some l ↦ P l`, and `EVERY` is
list membership quantification. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileLabIMPMmioPcsMinIndex {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : LabToTarget.Config)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (bytes : List (BitVec 8)) (c' : LabToTarget.Config) :
    compileLab asmConf c secList = some (bytes, c') ∧
      (match c.ffiNames with
        | none => True
        | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s) →
    ∃ ffiNames, c'.ffiNames = some ffiNames ∧
      ∃ x, mmioPcsMinIndex ffiNames = some x := by
  rintro ⟨h, hall⟩
  obtain ⟨ffis, hnone, secs', l1, hsel, -, -, rfl⟩ := compileLab_some secList h
  generalize hs : getShmemInfo secs' c.pos [] [] = sh
  obtain ⟨newFfis, infos⟩ := sh
  refine ⟨ffis ++ newFfis, rfl, ffis.length, ?_⟩
  obtain ⟨l, hl, hsh⟩ := getShmemInfo_mappedNames secs' c.pos [] [] newFfis infos hs
  simp only [List.nil_append] at hl
  subst hl
  apply mmioPcsMinIndex_append
  refine ⟨fun x hx s hxs => ?_, ?_⟩
  · obtain ⟨op, rfl⟩ := hsh x hx
    cases hxs
  · rcases hsel with hc | hc
    · rw [hc] at hall
      exact hall
    · rw [hnone hc]
      exact findFfiNamesEvery secList _ rfl

end Flapjack.Compiler.Backend.BackendProof
