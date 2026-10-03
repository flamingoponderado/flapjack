import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.HolRef

namespace Flapjack

/-- Literal wordProps GC callback contract with all seven original quantifiers.
FDOM is lookup nonabsence; FDOMSUB/FUPDATE use canonical eraseEq/updateEq.
The sole FAPPLY occurs under Handler ∈ FDOM: the witnesses below prove that
its fallback is unobservable there. No out-of-domain FAPPLY rendering or new
default assumption is introduced. The function qualifier inherits the reviewed
WordSemGcFun argument4/result3 alias translation. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_fun_ok_def"
  (fmap_as_finite_support_function := [argument_4, result_3])
  (words_as_type_indexed_bitvec)]
def wordGcFunOk {width : Nat} [NeZero width]
    (f : WordSemGcFun width) : Prop :=
  ∀ (wl : List (WordLocW width)) (m : BitVec width → WordLocW width)
    (d : BitVec width → Bool)
    (s : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (wl1 : List (WordLocW width)) (m1 : BitVec width → WordLocW width)
    (s1 : HolFiniteMapExact WordStoreHOL (WordLocW width)),
    s.lookup .handler ≠ none ∧
      f (wl, m, d, s.eraseEq .handler) = some (wl1, m1, s1) →
    wl.length = wl1.length ∧ s1.lookup .handler = none ∧
      f (wl, m, d, s) = some (wl1, m1,
        s1.updateEq (.handler, (s.lookup .handler).getD (.loc 0 0)))

/-- Flapjack representation support with no separately named HOL original:
the original domain guard supplies the unique Handler value. This does not
define total out-of-domain FAPPLY. -/
theorem wordGcHandlerValue {width : Nat} [NeZero width]
    (s : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (h : s.lookup .handler ≠ none) (fallback : WordLocW width) :
    ∃ value, s.lookup .handler = some value ∧
      (s.lookup .handler).getD fallback = value := by
  cases he : s.lookup .handler with
  | none => exact False.elim (h he)
  | some value => exact ⟨value, rfl, rfl⟩

/-- Flapjack infrastructure: the guarded occurrence is independent of fallback. -/
theorem wordGcHandlerFallback {width : Nat} [NeZero width]
    (s : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (h : s.lookup .handler ≠ none) (fallback : WordLocW width) :
    (s.lookup .handler).getD fallback = (s.lookup .handler).getD (.loc 0 0) := by
  obtain ⟨value, read, _⟩ := wordGcHandlerValue s h fallback
  simp [read]

end Flapjack
