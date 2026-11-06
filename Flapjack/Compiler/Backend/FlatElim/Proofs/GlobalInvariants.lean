import Flapjack.Compiler.Backend.FlatElim.Proofs.Removal
import Flapjack.Compiler.Backend.FlatProps.Globals

/-! Global-bag invariants of flat declaration elimination. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.Compiler.Backend.FlatProps

/-- Filtering cannot increase the multiplicity of any initialization. -/
theorem elistGlobals_filter_sub (predicate : FlatLang.Exp → Bool) (expressions : List FlatLang.Exp) :
    Flapjack.subBag (elistGlobals (expressions.filter predicate)) (elistGlobals expressions) := by
  have counts : ∀ key, elistGlobals (expressions.filter predicate) key ≤ elistGlobals expressions key := by
    intro key
    induction expressions with
    | nil => simp [elistGlobals, emptyGlobalBag]
    | cons expression rest ih =>
      cases keep : predicate expression <;> simp [List.filter, keep, elistGlobals, unionGlobalBag] at * <;> omega
  intro key count bound
  exact Nat.le_trans bound (counts key)

/-- Flat elimination cannot increase any global initialization count. The
expression carriers remain pending HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "remove_flat_prog_sub_bag"]
theorem removeFlatProg_subBag (declarations : List FlatLang.Exp) :
    Flapjack.subBag (elistGlobals (removeFlatProgTotal declarations)) (elistGlobals declarations) := by
  cases safe : declarations.any hasEvalDec with
  | true => simp [removeFlatProgTotal, safe, Flapjack.subBag, Flapjack.bagInn]
  | false =>
    cases analysis : analyseCode declarations with
    | mk roots tree =>
      simpa [removeFlatProgTotal, safe, analysis, removeUnreachable] using
        elistGlobals_filter_sub (keep (closureTotal roots tree)) declarations

/-- Removing declarations preserves an empty initialization bag. The
expression carriers remain pending HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "remove_flat_prog_elist_globals_eq_empty"]
theorem removeFlatProg_globals_empty (declarations : List FlatLang.Exp)
    (empty : elistGlobals declarations = emptyGlobalBag) :
    elistGlobals (removeFlatProgTotal declarations) = emptyGlobalBag := by
  funext key
  have bound := removeFlatProg_subBag declarations key (elistGlobals (removeFlatProgTotal declarations) key) (Nat.le_refl _)
  rw [empty] at bound
  simp [Flapjack.bagInn, emptyGlobalBag] at bound ⊢
  exact bound

/-- Removing declarations preserves the original per-expression
closure-freedom predicate. The carriers remain pending HOL review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "remove_flat_prog_esgc_free"]
theorem removeFlatProg_esgcFree (declarations : List FlatLang.Exp)
    (free : ∀ expression ∈ declarations, esgcFree expression) :
    ∀ expression ∈ removeFlatProgTotal declarations, esgcFree expression := by
  intro expression member
  cases safe : declarations.any hasEvalDec with
  | true =>
    have original : expression ∈ declarations := by simpa [removeFlatProgTotal, safe] using member
    exact free expression original
  | false =>
    cases analysis : analyseCode declarations with
    | mk roots tree =>
      have filtered : expression ∈ declarations.filter (keep (closureTotal roots tree)) := by
        simpa [removeFlatProgTotal, safe, analysis, removeUnreachable] using member
      exact free expression (List.mem_of_mem_filter filtered)

/-- Removing declarations preserves distinct global initialization keys. The
expression carriers remain pending HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "remove_flat_prog_distinct_globals"]
theorem removeFlatProg_distinctGlobals (declarations : List FlatLang.Exp)
    (distinct : Flapjack.bagAllDistinct (elistGlobals declarations)) :
    Flapjack.bagAllDistinct (elistGlobals (removeFlatProgTotal declarations)) :=
  Flapjack.bagAllDistinct_subBag _ _ ⟨removeFlatProg_subBag declarations, distinct⟩

end Flapjack.Compiler.Backend.FlatElim
