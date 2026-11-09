import Flapjack.Compiler.Backend.FlatElim.Proofs.Removal
import Flapjack.Compiler.Backend.FlatProps.Globals

/-! Global-bag invariants of flat declaration elimination. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.Compiler.Backend.FlatProps

/-- Filtering cannot increase the multiplicity of any initialization. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "elist_globals_filter_SUB_BAG"]
theorem elistGlobals_filter_sub (predicate : FlatLang.Exp → Bool) (expressions : List FlatLang.Exp) :
    Flapjack.subBag (elistGlobals (expressions.filter predicate)) (elistGlobals expressions) := by
  have counts : ∀ key, elistGlobals (expressions.filter predicate) key ≤ elistGlobals expressions key := by
    intro key
    induction expressions with
    | nil => simp [elistGlobals, emptyGlobalBag]
    | cons expression rest ih =>
      cases keep : predicate expression <;> simp [List.filter, keep, elistGlobals, unionGlobalBag, Flapjack.bagUnion] at * <;> omega
  intro key count bound
  exact Nat.le_trans bound (counts key)

/-- Filtering preserves an empty bag of global initializations. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "elist_globals_filter"]
theorem elistGlobals_filter_empty (expressions : List FlatLang.Exp) (predicate : FlatLang.Exp → Bool) :
    elistGlobals expressions = emptyGlobalBag →
      elistGlobals (expressions.filter predicate) = emptyGlobalBag := by
  intro empty
  funext key
  have bound := elistGlobals_filter_sub predicate expressions key
    (elistGlobals (expressions.filter predicate) key) (Nat.le_refl _)
  rw [empty] at bound
  simp [Flapjack.bagInn, emptyGlobalBag, Flapjack.emptyBag] at bound ⊢
  exact bound

/-- Filtering preserves the closure-freedom predicate on every expression. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "esgc_free_filter"]
theorem esgcFree_filter (expressions : List FlatLang.Exp) (predicate : FlatLang.Exp → Bool) :
    (∀ expression ∈ expressions, esgcFree expression) →
      ∀ expression ∈ expressions.filter predicate, esgcFree expression := by
  intro free expression member
  exact free expression (List.mem_of_mem_filter member)

/-- Flat elimination cannot increase any global initialization count. -/
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

/-- Removing declarations preserves an empty initialization bag. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "remove_flat_prog_elist_globals_eq_empty"]
theorem removeFlatProg_globals_empty (declarations : List FlatLang.Exp)
    (empty : elistGlobals declarations = emptyGlobalBag) :
    elistGlobals (removeFlatProgTotal declarations) = emptyGlobalBag := by
  cases safe : declarations.any hasEvalDec with
  | true => simpa [removeFlatProgTotal, safe] using empty
  | false =>
    cases analysis : analyseCode declarations with
    | mk roots tree =>
      simpa [removeFlatProgTotal, safe, analysis, removeUnreachable] using
        elistGlobals_filter_empty declarations (keep (closureTotal roots tree)) empty

/-- Removing declarations preserves the original per-expression
closure-freedom predicate. -/
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
      exact esgcFree_filter declarations (keep (closureTotal roots tree)) free expression filtered

/-- Removing declarations preserves distinct global initialization keys. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "remove_flat_prog_distinct_globals"]
theorem removeFlatProg_distinctGlobals (declarations : List FlatLang.Exp)
    (distinct : Flapjack.bagAllDistinct (elistGlobals declarations)) :
    Flapjack.bagAllDistinct (elistGlobals (removeFlatProgTotal declarations)) :=
  Flapjack.bagAllDistinct_subBag _ _ ⟨removeFlatProg_subBag declarations, distinct⟩

end Flapjack.Compiler.Backend.FlatElim
