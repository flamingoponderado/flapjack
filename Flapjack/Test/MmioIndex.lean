import Flapjack.Compiler.Backend.Semantics.TargetSem.MmioIndex
namespace Flapjack.Test.MmioIndex
open Flapjack
private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩
private def ext : HolFfiName := .extCall (Basis.Pure.MlString.MlString.implode [])
private def rd : HolFfiName := .sharedMem .mappedRead
private def wr : HolFfiName := .sharedMem .mappedWrite
-- mmio_empty
example : mmioPcsMinIndex [] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 0 at hjhi
    omega

-- mmio_0
example : mmioPcsMinIndex [ext] = some 1 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 := by omega
    have h := casesJ
    subst j
    exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 1 at hjhi
    omega

-- mmio_1
example : mmioPcsMinIndex [rd] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 1 at hjhi
    have casesJ : j = 0 := by omega
    have h := casesJ
    subst j
    exact ⟨.mappedRead, rfl⟩

-- mmio_2
example : mmioPcsMinIndex [wr] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 1 at hjhi
    have casesJ : j = 0 := by omega
    have h := casesJ
    subst j
    exact ⟨.mappedWrite, rfl⟩

-- mmio_00
example : mmioPcsMinIndex [ext, ext] = some 2 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with h | h
    · subst j
      exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
    · subst j
      exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 2 at hjhi
    omega

-- mmio_01
example : mmioPcsMinIndex [ext, rd] = some 1 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 := by omega
    have h := casesJ
    subst j
    exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 2 at hjhi
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with h | h
    · subst j
      omega
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_02
example : mmioPcsMinIndex [ext, wr] = some 1 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 := by omega
    have h := casesJ
    subst j
    exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 2 at hjhi
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with h | h
    · subst j
      omega
    · subst j
      exact ⟨.mappedWrite, rfl⟩

-- mmio_10
example : mmioPcsMinIndex [rd, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedRead = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 1 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_11
example : mmioPcsMinIndex [rd, rd] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 2 at hjhi
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with h | h
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_12
example : mmioPcsMinIndex [rd, wr] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 2 at hjhi
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with h | h
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩

-- mmio_20
example : mmioPcsMinIndex [wr, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedWrite = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 1 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_21
example : mmioPcsMinIndex [wr, rd] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 2 at hjhi
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with h | h
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_22
example : mmioPcsMinIndex [wr, wr] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 2 at hjhi
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with h | h
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩

-- mmio_000
example : mmioPcsMinIndex [ext, ext, ext] = some 3 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
    · subst j
      exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
    · subst j
      exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 3 at hjhi
    omega

-- mmio_001
example : mmioPcsMinIndex [ext, ext, rd] = some 2 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with h | h
    · subst j
      exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
    · subst j
      exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      omega
    · subst j
      omega
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_002
example : mmioPcsMinIndex [ext, ext, wr] = some 2 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with h | h
    · subst j
      exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
    · subst j
      exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      omega
    · subst j
      omega
    · subst j
      exact ⟨.mappedWrite, rfl⟩

-- mmio_010
example : mmioPcsMinIndex [ext, rd, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 1 := by
    by_cases h : x ≤ 1
    · exact h
    · obtain ⟨name, hn⟩ := hpre 1 (by omega)
      change HolFfiName.sharedMem .mappedRead = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 2 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_011
example : mmioPcsMinIndex [ext, rd, rd] = some 1 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 := by omega
    have h := casesJ
    subst j
    exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      omega
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_012
example : mmioPcsMinIndex [ext, rd, wr] = some 1 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 := by omega
    have h := casesJ
    subst j
    exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      omega
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩

-- mmio_020
example : mmioPcsMinIndex [ext, wr, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 1 := by
    by_cases h : x ≤ 1
    · exact h
    · obtain ⟨name, hn⟩ := hpre 1 (by omega)
      change HolFfiName.sharedMem .mappedWrite = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 2 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_021
example : mmioPcsMinIndex [ext, wr, rd] = some 1 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 := by omega
    have h := casesJ
    subst j
    exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      omega
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_022
example : mmioPcsMinIndex [ext, wr, wr] = some 1 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have casesJ : j = 0 := by omega
    have h := casesJ
    subst j
    exact ⟨Basis.Pure.MlString.MlString.implode [], rfl⟩
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      omega
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩

-- mmio_100
example : mmioPcsMinIndex [rd, ext, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedRead = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 1 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_101
example : mmioPcsMinIndex [rd, ext, rd] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedRead = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 1 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_102
example : mmioPcsMinIndex [rd, ext, wr] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedRead = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 1 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_110
example : mmioPcsMinIndex [rd, rd, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedRead = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 2 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_111
example : mmioPcsMinIndex [rd, rd, rd] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_112
example : mmioPcsMinIndex [rd, rd, wr] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩

-- mmio_120
example : mmioPcsMinIndex [rd, wr, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedRead = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 2 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_121
example : mmioPcsMinIndex [rd, wr, rd] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_122
example : mmioPcsMinIndex [rd, wr, wr] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩

-- mmio_200
example : mmioPcsMinIndex [wr, ext, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedWrite = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 1 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_201
example : mmioPcsMinIndex [wr, ext, rd] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedWrite = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 1 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_202
example : mmioPcsMinIndex [wr, ext, wr] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedWrite = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 1 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_210
example : mmioPcsMinIndex [wr, rd, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedWrite = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 2 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_211
example : mmioPcsMinIndex [wr, rd, rd] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_212
example : mmioPcsMinIndex [wr, rd, wr] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩

-- mmio_220
example : mmioPcsMinIndex [wr, wr, ext] = none := by
  apply mmioPcsMinIndex_eq_none
  rintro ⟨x, hx⟩
  rcases hx with ⟨hlen, hpre, hsuf⟩
  have hx : x ≤ 0 := by
    by_cases h : x ≤ 0
    · exact h
    · obtain ⟨name, hn⟩ := hpre 0 (by omega)
      change HolFfiName.sharedMem .mappedWrite = .extCall name at hn
      cases hn
  obtain ⟨op, ho⟩ := hsuf 2 (by omega) (by decide)
  change HolFfiName.extCall (Basis.Pure.MlString.MlString.implode []) = .sharedMem op at ho
  cases ho

-- mmio_221
example : mmioPcsMinIndex [wr, wr, rd] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedRead, rfl⟩

-- mmio_222
example : mmioPcsMinIndex [wr, wr, wr] = some 0 := by
  apply mmioPcsMinIndex_eq_some
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hjlo hjhi
    change j < 3 at hjhi
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with h | h | h
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩
    · subst j
      exact ⟨.mappedWrite, rfl⟩

end Flapjack.Test.MmioIndex
