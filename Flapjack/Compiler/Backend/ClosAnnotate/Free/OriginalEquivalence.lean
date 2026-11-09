import Flapjack.Compiler.Backend.ClosAnnotate.Free.Original
import Flapjack.Compiler.Backend.ClosAnnotate.Free.SourceEquations

/-! Agreement between source-shaped and executable free-variable traversals. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang DbVars

/-- The source recursion and optimized list traversal compute the same result.
This auxiliary equality supports the original three-part HOL theorem. -/
theorem altFreeSource_eq_altFree (expressions : List Exp) :
    altFreeSource expressions = altFree expressions := by
  induction expressions using altFreeSource.induct <;>
    simp_all [altFreeSource, altFree_nil, altFree_cons_cons, altFree_var, altFree_if,
      altFree_let, altFree_raise, altFree_tick, altFree_op, altFree_app, altFree_fn,
      altFree_letrec, altFree_handle, altFree_call, pureList_eq_all]
  case case5 =>
    rename_i t xs body m rest vars result good ih
    have noOverlapTrue : noOverlap xs.length vars = true := good.1
    simp [noOverlapTrue]
  case case12 =>
    rename_i names loc selected functions body rest vars result ihBody ihFunctions
    simp only [List.map_attach_eq_pmap]
    have setsEq : functions.map (fun entry =>
        DbVarSet.shift (entry.1 + functions.length) (altFreeSource [entry.2]).2) =
      functions.map (fun entry =>
        DbVarSet.shift (entry.1 + functions.length) (altFree [entry.2]).2) := by
      apply List.map_congr_left
      intro entry member
      cases entry with
      | mk arity expression => rw [ihFunctions arity expression member]
    have pairsEq : functions.map (fun entry =>
        (entry.1, @Flapjack.holHd Exp ⟨.var .none 0⟩ (altFreeSource [entry.2]).1)) =
      functions.map (fun entry =>
        (entry.1, @Flapjack.holHd Exp ⟨.var .none 0⟩ (altFree [entry.2]).1)) := by
      apply List.map_congr_left
      intro entry member
      cases entry with
      | mk arity expression => rw [ihFunctions arity expression member]
    simp only [Function.comp_def]
    simp only [List.pmap_eq_map, setsEq, pairsEq]
    trivial

/-- The source and optimized free-variable traversals agree on singleton
expressions, lists, and recursive function groups. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "alt_free_sing_eq"]
theorem altFreeSource_sing_eq :
    (∀ expression, altFreeSource [expression] =
      (fun (e, dbs) => ([e], dbs)) (altFreeSing expression)) ∧
    (∀ expressions, altFreeSource expressions = altFreeList expressions) ∧
    (∀ count functions, (∀ entry ∈ functions, altFreeSource [entry.2] =
        (fun (e, dbs) => ([e], dbs)) (altFreeSing entry.2)) ∧
      altFreeFuns count functions = functions.map (fun (arity, body) =>
        let (result, live) := altFreeSing body
        ((arity, result), DbVarSet.shift (arity + count) live))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro expression
    rw [altFreeSource_eq_altFree]
    exact altFree_singleton expression
  · intro expressions
    exact altFreeSource_eq_altFree expressions
  · intro count functions
    constructor
    · intro entry _
      rw [altFreeSource_eq_altFree]
      exact altFree_singleton entry.2
    · simpa [altFree_singleton, Flapjack.holHd] using altFreeFuns_as_map count functions

end Flapjack.Compiler.Backend.ClosAnnotate
