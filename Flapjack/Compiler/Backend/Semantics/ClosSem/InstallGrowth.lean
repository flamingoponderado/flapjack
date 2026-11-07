import Flapjack.Compiler.Backend.Semantics.ClosSem.Install

/-! Code growth during proof-side closure installation. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Installation never changes a previously installed code entry. This
includes rejected requests and the valid-install timeout path. The finite-map
carrier and source correspondence are not yet reviewed. -/
theorem doInstall_code_submap {C F : Type} (values : List Value) (source next : State C F)
    (result : Result (List ClosLang.Exp) Value) (run : doInstall values source = (result, next)) :
    ∀ key entry, source.code.lookup key = some entry → next.code.lookup key = some entry := by
  intro key entry found
  by_cases typeError : result = .err (.abort .typeError)
  · subst result
    have nextEq : next = source := by
      unfold doInstall at run
      repeat' first | split at run | simp_all
    simpa [nextEq] using found
  · obtain ⟨_, _, _, _, _, _, auxiliary, _, _, _, _, _, _, fresh, _, _, _, nextEq, _⟩ :=
      doInstall_nonType_parts values source next result run typeError
    have absent : key ∉ auxiliary.map Prod.fst := by
      intro member
      have free := fresh key member
      rw [found] at free
      contradiction
    rw [nextEq]
    simp only [HolFiniteMapExact.lookup_updateListEq]
    have same := FLOOKUP_FUPDATE_LIST_HOL_not_mem source.code.lookup auxiliary key absent
    simpa [FLOOKUP, found] using same

end Flapjack.Compiler.Backend.ClosSem
