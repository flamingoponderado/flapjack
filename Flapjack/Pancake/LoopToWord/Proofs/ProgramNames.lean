import Flapjack.Pancake.LoopToWord.CompFuncExact

namespace Flapjack

/-- Compiler-specific list projection identity, used to prove the original name invariant. -/
private theorem compiledNames {width : Nat} [NeZero width]
    (source : List (Nat × List Nat × HolLoopProg width)) :
    (loopToWordCompileProgHOL source).map Prod.fst = source.map Prod.fst := by
  simp [loopToWordCompileProgHOL, List.map_map]

/-- Source-shaped preservation of distinct function names over the native compiler. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordFirstCompileProgAllDistinct {width : Nat} [NeZero width]
    (source : List (Nat × List Nat × HolLoopProg width))
    (h : (source.map Prod.fst).Nodup) :
    ((loopToWordCompileProgHOL source).map Prod.fst).Nodup := by
  rw [compiledNames]
  exact h

/-- The compile wrapper retains precisely the original distinct-name premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordFirstCompileAllDistinct {width : Nat} [NeZero width]
    (source : List (Nat × List Nat × HolLoopProg width))
    (h : (source.map Prod.fst).Nodup) :
    ((loopToWordCompileHOL source).map Prod.fst).Nodup :=
  loopToWordFirstCompileProgAllDistinct source h

/-- Compilation maps a present source triple to its whole compiled triple. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordMemProgMemCompileProg {width : Nat} [NeZero width]
    (source : List (Nat × List Nat × HolLoopProg width)) (name : Nat)
    (params : List Nat) (body : HolLoopProg width)
    (h : (name, params, body) ∈ source) :
    (name, params.length + 1, loopToWordCompFuncHOL name params body) ∈
      loopToWordCompileProgHOL source := by
  exact List.mem_map.mpr ⟨(name, params, body), h, rfl⟩

/-- First-match native Spt lookup commutes with compilation, even for duplicate names. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordLookupProgSomeLookupCompileProg {width : Nat} [NeZero width]
    (source : List (Nat × List Nat × HolLoopProg width)) (name : Nat)
    (params : List Nat) (body : HolLoopProg width)
    (h : sptLookup name (sptFromAList source) = some (params, body)) :
    sptLookup name (sptFromAList (loopToWordCompileProgHOL source)) =
      some (params.length + 1, loopToWordCompFuncHOL name params body) := by
  simp only [sptLookup_sptFromAList] at h ⊢
  induction source with
  | nil => simp [sptAListLookup] at h
  | cons entry source ih =>
      obtain ⟨other, args, program⟩ := entry
      by_cases hn : name = other
      · subst other
        simp [sptAListLookup] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [loopToWordCompileProgHOL, sptAListLookup]
      · simp only [sptAListLookup, if_neg hn] at h
        simpa [loopToWordCompileProgHOL, sptAListLookup, hn] using ih h

end Flapjack
