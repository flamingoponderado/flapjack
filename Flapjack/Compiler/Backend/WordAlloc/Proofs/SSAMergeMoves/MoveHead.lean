import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
import Mathlib.Data.List.Nodup

namespace Flapjack.Compiler.Backend.WordAlloc

namespace MoveHeadWitnesses

/-- Flapjack carrier roundtrip infrastructure for the state fields translated
from HOL finite maps; this is not a separate HOL theorem port. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end MoveHeadWitnesses

/-- Flapjack selector infrastructure: a present source binding makes the
fallback irrelevant. This infrastructure has no independent HOL original.
No assertion about HOL THE NONE is made. -/
theorem moveHeadValue_defaultIndependent {α : Type} (locals : Spt α) (key : Nat)
    (present : sptDomain locals key) (first second : α) :
    (sptLookup key locals).getD first = (sptLookup key locals).getD second := by
  rcases (sptMem_iff_lookup key locals).mp present with ⟨value, lookup⟩
  simp only [lookup, Option.getD_some]

/-- Full Move-head evaluation law on the faithful native wordSem evaluator.
All four original premises are retained, including the source-not-written
premise. HOL THE is observed only at the source binding made present by the
second premise; `getD (.word 0)` therefore returns precisely its SOME payload,
independently of the fallback, as checked above. No THE NONE value is claimed.
The priority, move list, complete states, and positive word width are arbitrary.
The evaluator constant closure inherits its documented rational-cut FP boundary;
this Move branch runs only getVars/setVars, without evaluating an FP instruction. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem movEvalHead {width : Nat} [NeZero width] {C : Type} {F : Type}
    (priority : Nat) (moves : List (Nat × Nat))
    (state result : WordSemStateFiniteExact width C F) (x y : Nat)
    (evaluation : WordSemStateFiniteExact.evaluate (.move priority moves) state =
      (none, result))
    (sourcePresent : sptDomain state.locals y)
    (_sourceNotWritten : y ∉ moves.map Prod.fst)
    (destinationNotWritten : x ∉ moves.map Prod.fst) :
    WordSemStateFiniteExact.evaluate (.move priority ((x, y) :: moves)) state =
      (none, { result with locals := sptInsert x ((sptLookup y state.locals).getD (.word 0)) result.locals }) := by
  classical
  rcases (sptMem_iff_lookup y state.locals).mp sourcePresent with ⟨value, lookup⟩
  by_cases distinct : (moves.map Prod.fst).Nodup
  · cases values : WordSemStateFiniteExact.getVars (moves.map Prod.snd) state with
    | none => simp [WordSemStateFiniteExact.evaluate, distinct, values] at evaluation
    | some list =>
      have output : WordSemStateFiniteExact.setVars (moves.map Prod.fst) list state =
          result := by
        simpa only [WordSemStateFiniteExact.evaluate, if_pos distinct, values,
          Prod.mk.injEq, true_and] using evaluation
      subst result
      simp [WordSemStateFiniteExact.evaluate, List.nodup_cons,
        destinationNotWritten, distinct, WordSemStateFiniteExact.getVars,
        WordSemStateFiniteExact.getVar, lookup, values,
        WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert]
  · simp [WordSemStateFiniteExact.evaluate, distinct] at evaluation

end Flapjack.Compiler.Backend.WordAlloc
