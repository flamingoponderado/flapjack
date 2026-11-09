import Flapjack.Compiler.Backend.SourceToFlat.CompileExp
import Flapjack.Misc.List.Size

/-! List-shape prerequisite for the source-to-flat pass correctness proof. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- A list member's size is below any strict bound on the HOL list size. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "mem_size_lemma"]
theorem mem_size_lemma {α : Type} (sz : α → Nat) (xs : List α) (N : Nat) (x : α)
    (bound : listSizeHOL sz xs < N) (member : x ∈ xs) : sz x < N := by
  induction xs with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    simp only [listSizeHOL] at bound
    rcases member with rfl | member
    · omega
    · exact ih (by omega) member

/-- Indexed mapping over a final element uses the preceding list length. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "MAPi_SNOC"]
theorem mapIdx_snoc {α β : Type} (xs : List α) (x : α) (f : Nat → α → β) :
    (xs ++ [x]).mapIdx f = xs.mapIdx f ++ [f xs.length x] :=
  List.mapIdx_concat

/-- Compiling an expression list preserves its length. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_exps_length"]
theorem compileExps_length (t : List Basis.Pure.MlString.MlString)
    (env : Environment) (es : List AstHOL.Exp) :
    (compileExps t env es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [compileExps, ih]

/-- Index-aware mapping commutes with an ordinary map. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "mapi_map"]
theorem mapIdx_map {α β γ : Type} (f : Nat → β → γ) (g : α → β) (xs : List α) :
    (xs.map g).mapIdx f = xs.mapIdx (fun i x => f i (g x)) := by
  apply List.ext_getElem?
  intro i
  simp [Option.map_map, Function.comp_def]

/-- Filtering an indexed map keeps every entry exactly when the predicate
holds at every valid source index. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "FILTER_MAPi_ID"]
theorem filter_mapIdx_eq_self {α β : Type} (p : β → Bool) (xs : List α) (f : Nat → α → β) :
    (xs.mapIdx f).filter p = xs.mapIdx f ↔
      ∀ (i : Nat) (h : i < xs.length), p (f i xs[i]) = true := by
  rw [List.filter_eq_self]
  constructor
  · intro all i h
    exact all _ (List.mem_mapIdx.mpr ⟨i, h, rfl⟩)
  · intro all value member
    obtain ⟨i, h, rfl⟩ := List.mem_mapIdx.mp member
    exact all i h

end Flapjack.Compiler.Backend.SourceToFlat
