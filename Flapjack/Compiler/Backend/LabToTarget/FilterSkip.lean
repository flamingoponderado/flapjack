import Flapjack.Compiler.Backend.LabToTarget.CodeAppend
import Flapjack.Compiler.Backend.LabFilter
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
import Flapjack.Compiler.Backend.LabProps.LabelSets
import Flapjack.Compiler.Backend.LabProps.CodeSafety

/-! Native skip-filter observations from the original lab-to-target proof.
The original full types use the single word-indexed labLang line/sec family;
only its positive word dimension is translated. Filtering is the operation
executed by the compiler, and preserves actual labels and fetched instructions.
-/
namespace Flapjack.Compiler.Backend.LabToTarget.FilterSkip
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabFilter Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabToTarget

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem notNotSkipImpSkip {width : Nat} [NeZero width] (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)) :
    notSkip line = false → ∃ bytes len, line = .asm (.asmi (.inst .skip)) bytes len := by
  cases line with
  | label => simp [notSkip]
  | labAsm => simp [notSkip]
  | asm instruction bytes len =>
    cases instruction with
    | cbw => simp [notSkip]
    | shareMem => simp [notSkip]
    | asmi instruction =>
      cases instruction
      case inst instruction => cases instruction <;> simp [notSkip]
      all_goals simp [notSkip]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem mapSectionNumFilterSkip {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)))) :
    (filterSkip code).map Section.sectionId = code.map Section.sectionId := by
  induction code with
  | nil => rfl
  | cons sect rest ih => cases sect; simp [filterSkip, ih]

private theorem extractLabels_filter {width : Nat} [NeZero width] (lines : List (LabLineHOL width)) :
    extractLabels (lines.filter notSkip) = extractLabels lines := by
  induction lines with
  | nil => rfl
  | cons line lines ih =>
    by_cases h : notSkip line = true
    · cases line <;> simp [h, extractLabels, ih]
    · have hn : notSkip line = false := Bool.eq_false_iff.mpr h
      obtain ⟨bytes, len, rfl⟩ := notNotSkipImpSkip line hn
      simp [notSkip, extractLabels, ih]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem filterSkipExtractLabels {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)))) :
    (filterSkip code).map (fun sect => extractLabels sect.lines) =
      code.map (fun sect => extractLabels sect.lines) := by
  induction code with
  | nil => rfl
  | cons sect rest ih => cases sect; simp [filterSkip, extractLabels_filter, ih]

private theorem lineLabels_notSkip {width : Nat} [NeZero width] (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width))
    (label : Nat × Nat) (h : label ∈ lineGetLabels line) : notSkip line = true := by
  cases line <;> simp_all [lineGetLabels, notSkip]

private theorem lineCodeLabels_notSkip {width : Nat} [NeZero width] (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width))
    (label : Nat) (h : label ∈ lineGetCodeLabels line) : notSkip line = true := by
  cases line <;> simp_all [lineGetCodeLabels, notSkip]

private theorem secLabels_filter {width : Nat} [NeZero width] (sect : Section (LabLineHOL width)) :
    secGetLabels ⟨sect.sectionId, sect.lines.filter notSkip⟩ = secGetLabels sect := by
  ext label
  simp only [secGetLabels, Set.mem_ofPred_eq, List.mem_filter]
  constructor
  · rintro ⟨line, ⟨hm, _⟩, hl⟩; exact ⟨line, hm, hl⟩
  · rintro ⟨line, hm, hl⟩; exact ⟨line, ⟨hm, lineLabels_notSkip line label hl⟩, hl⟩

private theorem secCodeLabels_filter {width : Nat} [NeZero width] (sect : Section (LabLineHOL width)) :
    secGetCodeLabels ⟨sect.sectionId, sect.lines.filter notSkip⟩ = secGetCodeLabels sect := by
  ext label
  simp only [secGetCodeLabels, Set.mem_union, Set.mem_ofPred_eq,
    List.mem_filter]
  constructor
  · rintro (h | ⟨n, ⟨line, ⟨hm, _⟩, hl⟩, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n, ⟨line, hm, hl⟩, he⟩
  · rintro (h | ⟨n, ⟨line, hm, hl⟩, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n, ⟨line, ⟨hm, lineCodeLabels_notSkip line n hl⟩, hl⟩, he⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getLabelsFilterSkip {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)))) :
    getLabels (filterSkip code) = getLabels code := by
  induction code with
  | nil => rfl
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    simp only [filterSkip, getLabels_cons, ih]
    rw [secLabels_filter ⟨k, lines⟩]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getCodeLabelsFilterSkip {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)))) :
    getCodeLabels (filterSkip code) = getCodeLabels code := by
  induction code with
  | nil => rfl
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    simp only [filterSkip, getCodeLabels_cons, ih]
    rw [secCodeLabels_filter ⟨k, lines⟩]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findFfiNamesFilterSkip {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)))) :
    findFfiNames (filterSkip code) = findFfiNames code := by
  fun_induction findFfiNames code <;> simp_all only [filterSkip]
  case case1 => simp [findFfiNames]
  case case2 => simp_all [List.filter_nil, findFfiNames]
  case case3 => simp_all [List.filter_cons, notSkip, findFfiNames]
  case case4 k line xs rest h ih =>
    by_cases hn : notSkip line = true
    · cases line with
      | label => simpa [List.filter_cons, hn, findFfiNames] using ih
      | asm => simpa [List.filter_cons, hn, findFfiNames] using ih
      | labAsm instruction position bytes len =>
        cases instruction <;> simp_all [findFfiNames]
        case callFFI name => exact False.elim (h name position bytes len rfl rfl rfl rfl)
    · have hf : notSkip line = false := Bool.eq_false_iff.mpr hn
      obtain ⟨bytes, len, rfl⟩ := notNotSkipImpSkip line hf
      simpa [List.filter_cons, notSkip, findFfiNames] using ih

/-- Flapjack list-navigation infrastructure: an instruction is fetchable exactly
when it occurs in a section and is not a label. The existential PC is produced
by the actual native fetch recursion; no separate HOL declaration. -/
private theorem fetchExists_head {width : Nat} [NeZero width] (k : Nat)
    (head : LabLineHOL width) (lines : List (LabLineHOL width))
    (rest : LabProgHOL width) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)) :
    (∃ p, asmFetchAux p (⟨k, head :: lines⟩ :: rest) = some line) ↔
      (isLabelHOL head = false ∧ head = line) ∨
        (∃ p, asmFetchAux p (⟨k, lines⟩ :: rest) = some line) := by
  by_cases h : isLabelHOL head = true
  · simp [asmFetchAux, h]
  · have hf : isLabelHOL head = false := Bool.eq_false_iff.mpr h
    constructor
    · rintro ⟨p, hp⟩
      cases p with
      | zero => exact Or.inl ⟨hf, by simpa [asmFetchAux, h] using hp⟩
      | succ p => exact Or.inr ⟨p, by simpa [asmFetchAux, h] using hp⟩
    · rintro (⟨_, rfl⟩ | ⟨p, hp⟩)
      · exact ⟨0, by simp [asmFetchAux, h]⟩
      · exact ⟨p + 1, by simpa [asmFetchAux, h] using hp⟩

private theorem fetchExists_iff {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)))) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)) :
    (∃ p, asmFetchAux p code = some line) ↔
      (∃ sect ∈ code, line ∈ sect.lines) ∧ isLabelHOL line = false := by
  induction code with
  | nil => simp [asmFetchAux]
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    induction lines with
    | nil => simpa [asmFetchAux] using ih
    | cons head lines ih =>
      rw [fetchExists_head, ih]
      simp only [List.mem_cons, exists_eq_or_imp, List.mem_cons]
      constructor
      · rintro (⟨hl, rfl⟩ | ⟨hm, hl⟩)
        · exact ⟨Or.inl (Or.inl rfl), hl⟩
        · exact ⟨by rcases hm with (hm | hm); exact Or.inl (Or.inr hm); exact Or.inr hm, hl⟩
      · rintro ⟨hm, hl⟩
        rcases hm with ((rfl | hm) | hm)
        · exact Or.inl ⟨hl, rfl⟩
        · exact Or.inr ⟨Or.inl hm, hl⟩
        · exact Or.inr ⟨Or.inr hm, hl⟩

private theorem memFilterSkip {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width))))
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)) :
    (∃ sect ∈ filterSkip code, line ∈ sect.lines) ↔
      (∃ sect ∈ code, line ∈ sect.lines) ∧ notSkip line = true := by
  induction code with
  | nil => simp [filterSkip]
  | cons sect rest ih =>
    rcases sect with ⟨k, lines⟩
    simp only [filterSkip, List.mem_cons, exists_eq_or_imp, List.mem_filter, ih]
    constructor
    · rintro (⟨hm, hn⟩ | ⟨hm, hn⟩)
      · exact ⟨Or.inl hm, hn⟩
      · exact ⟨Or.inr hm, hn⟩
    · rintro ⟨hm | hm, hn⟩
      · exact Or.inl ⟨hm, hn⟩
      · exact Or.inr ⟨hm, hn⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchAuxFilterSkip {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)))) (p : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)) :
    asmFetchAux p (filterSkip code) = some line ∧ notSkip line = true →
      ∃ p', asmFetchAux p' code = some line := by
  rintro ⟨h, _⟩
  obtain ⟨hm, hl⟩ := (fetchExists_iff (filterSkip code) line).mp ⟨p, h⟩
  exact (fetchExists_iff code line).mpr ⟨(memFilterSkip code line).mp hm |>.1, hl⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem impAsmFetchAuxFilterSkip {width : Nat} [NeZero width]
    (p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)))) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)) :
    asmFetchAux p code = some line ∧ notSkip line = true →
      ∃ p', asmFetchAux p' (filterSkip code) = some line := by
  rintro ⟨h, hn⟩
  obtain ⟨hm, hl⟩ := (fetchExists_iff code line).mp ⟨p, h⟩
  exact (fetchExists_iff (filterSkip code) line).mpr
    ⟨(memFilterSkip code line).mpr ⟨hm, hn⟩, hl⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem noShareMemFilterSkip {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) (BitVec width)))) :
    Flapjack.Compiler.Backend.LabProps.noShareMemInst (filterSkip code) ↔
      Flapjack.Compiler.Backend.LabProps.noShareMemInst code := by
  constructor
  · intro h p op reg addr bytes len hp
    obtain ⟨p', hp'⟩ := impAsmFetchAuxFilterSkip p code
      (.asm (.shareMem op reg addr) bytes len) ⟨hp, rfl⟩
    exact h p' op reg addr bytes len hp'
  · intro h p op reg addr bytes len hp
    obtain ⟨p', hp'⟩ := asmFetchAuxFilterSkip code p
      (.asm (.shareMem op reg addr) bytes len) ⟨hp, rfl⟩
    exact h p' op reg addr bytes len hp'

end Flapjack.Compiler.Backend.LabToTarget.FilterSkip
