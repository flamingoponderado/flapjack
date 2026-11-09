import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.FreeVariables
import Flapjack.Compiler.Backend.ClosAnnotate.Free.OriginalEquivalence
import Flapjack.Compiler.Backend.ClosAnnotate.Shift.OriginalEquivalence

/-! Source-shaped free-variable observation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang DbVars

/-- Free-variable traversal and shifting preserve the position of each expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "EL_shift_alt_free"]
theorem el_shift_altFree (l m : Nat) (i : Spt Nat) (expressions : List Exp) (index : Nat)
    (bound : index < expressions.length) :
    [@Flapjack.holEl Exp ⟨.var .none 0⟩ index (shiftSource (altFreeSource expressions).1 l m i)] =
      shiftSource (altFreeSource [@Flapjack.holEl Exp ⟨.var .none 0⟩ index expressions]).1 l m i := by
  let : Nonempty Exp := ⟨.var .none 0⟩
  have freeMap : ∀ xs : List Exp, (altFree xs).1 = xs.map (fun x => (altFreeSing x).1) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change (altFreeList xs).1 = _ at ih
      simp [altFree, altFreeList, ih]
  have shiftMap : ∀ xs : List Exp, shiftList xs l m i = xs.map (fun x => shiftSing x l m i) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [shiftList, ih]
  rw [altFreeSource_eq_altFree, altFreeSource_eq_altFree, shiftSource_eq_shiftList,
    shiftSource_eq_shiftList, freeMap, freeMap, shiftMap, shiftMap]
  simp only [List.map_cons, List.map_nil, Flapjack.holEl_eq_getElem index expressions bound]
  rw [Flapjack.holEl_eq_getElem]
  · simp
  · simpa using bound

/-- Folding paired values separates the payload list from the variable-set fold. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "FOLDR_mk_Union"]
theorem foldr_mkUnion {α : Type} (ys : List (α × DbVarSet))
    (aux : List α) (live : DbVarSet) :
    ys.foldr (fun (x, vars) (tail, frees) => (x :: tail, mkUnion vars frees)) (aux, live) =
      (ys.map Prod.fst ++ aux, (ys.map Prod.snd).foldr mkUnion live) := by
  induction ys with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨x, vars⟩
    simp only [List.foldr_cons, List.map_cons, List.cons_append, ih]

/-- The source free-variable observation uses the original free-variable pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv_def"]
noncomputable def altFvSource (index : Nat) (expressions : List Exp) : Bool :=
  hasVar index (altFreeSource expressions).2

/-- The free-variable observation reads the second component of the pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_free_thm"]
theorem altFreeSource_observation (expressions : List Exp) :
    let (_, live) := altFreeSource expressions
    ∀ index, altFvSource index expressions = hasVar index live := by
  cases result : altFreeSource expressions with
  | mk output live => simp [altFvSource, result]

/-- The optimized observation computes the source free-variable predicate. -/
theorem altFvSource_eq_altFv (index : Nat) (expressions : List Exp) :
    altFvSource index expressions = altFv index expressions := by
  simp [altFvSource, altFv, altFreeSource_eq_altFree]

/-- Free-variable membership in a singleton expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv1_def"]
noncomputable def altFvOneSource (index : Nat) (expression : Exp) : Bool :=
  altFvSource index [expression]

/-- The empty expression list has no free variables. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv_nil"]
theorem altFvSource_nil (index : Nat) : altFvSource index [] = false := by
  rw [altFvSource_eq_altFv, altFv_nil]

/-- Free-variable membership of a list is membership in its head or tail. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv_cons"]
theorem altFvSource_cons (index : Nat) (first : Exp) (rest : List Exp) :
    altFvSource index (first :: rest) =
      (altFvOneSource index first || altFvSource index rest) := by
  simp only [altFvOneSource, altFvSource_eq_altFv]
  exact altFv_cons index first rest

/-- Replication has the same free variables as its element when nonempty. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv_REPLICATE"]
theorem altFvSource_replicate (index count : Nat) (expression : Exp) :
    altFvSource index (List.replicate count expression) =
      (decide (0 < count) && altFvOneSource index expression) := by
  induction count with
  | zero => simp [altFvSource_nil]
  | succ count ih =>
    rw [List.replicate_succ, altFvSource_cons, ih]
    cases count <;> simp

end Flapjack.Compiler.Backend.ClosAnnotate
