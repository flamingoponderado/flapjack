import Flapjack.Compiler.Backend.BviLet.SourceSing
import Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate

/-! Environment invariants for the BVI let-propagation simulation. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs

/-- The displacement at each source position selects the same value in the
corresponding suffix of the optimized environment. After the displacements
end, the source is a suffix of the optimized environment. This infrastructure
is untagged pending comparison of the inferred HOL polymorphic types. -/
def envRel {α : Type} : List Nat → Nat → List α → List α → Prop
  | [], d, source, target => source = target.drop d
  | a :: rest, d, x :: source, y :: target =>
      (y :: target)[a]? = some x ∧ envRel rest d source target
  | _ :: _, _, _, _ => False

/-- A propagated lookup selects the original value at the adjusted index. -/
theorem envRel_lookup {α : Type} (offsets : List Nat) (d : Nat)
    (source target : List α) (related : envRel offsets d source target)
    (index : Nat) (value : α) (lookup : source[index]? = some value) :
    target[index + (offsets[index]?.getD d)]? = some value := by
  induction offsets generalizing source target index with
  | nil =>
    simp only [envRel] at related
    subst source
    simpa [List.getElem?_drop, Nat.add_comm] using lookup
  | cons a rest ih =>
    cases source with
    | nil => simp at lookup
    | cons x source =>
      cases target with
      | nil => simp [envRel] at related
      | cons y target =>
        simp only [envRel] at related
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst value
          simpa using related.1
        | succ index =>
          simp only [List.getElem?_cons_succ] at lookup
          change (y :: target)[Nat.succ index + (rest[index]?.getD d)]? = some value
          rw [Nat.succ_add, List.getElem?_cons_succ]
          exact ih source target related.2 index lookup

/-- Prefixing matching values gives zero displacements for the new entries. -/
theorem envRel_replicate {α : Type} (values : List α) (offsets : List Nat)
    (d : Nat) (source target : List α) (related : envRel offsets d source target) :
    envRel (List.replicate values.length 0 ++ offsets) d (values ++ source)
      (values ++ target) := by
  induction values with
  | nil => simpa using related
  | cons value values ih => simpa [List.replicate_succ, envRel] using ih

/-- Adding one target-only value shifts every displacement and the suffix
offset by one. -/
theorem envRel_shiftOne {α : Type} (offsets : List Nat) (d : Nat)
    (source target : List α) (related : envRel offsets d source target) (value : α) :
    envRel (offsets.map (1 + ·)) (d + 1) source (value :: target) := by
  induction offsets generalizing source target value with
  | nil =>
    simp only [envRel] at related
    simpa [envRel, Nat.add_comm] using related
  | cons a rest ih =>
    cases source with
    | nil => cases target <;> simp [envRel] at related
    | cons x source =>
      cases target with
      | nil => simp [envRel] at related
      | cons y target =>
        simp only [envRel] at related
        simp only [List.map_cons, envRel]
        constructor
        · simpa [Nat.add_comm] using related.1
        · exact ih source target related.2 y

/-- A target-only prefix shifts every displacement by its length. -/
theorem envRel_shift {α : Type} (added : List α) (offsets : List Nat) (d : Nat)
    (source target : List α) (related : envRel offsets d source target) :
    envRel (offsets.map (added.length + ·)) (d + added.length) source
      (added ++ target) := by
  induction added with
  | nil => simpa using related
  | cons value added ih =>
    have shifted := envRel_shiftOne (offsets.map (added.length + ·))
      (d + added.length) source (added ++ target) ih value
    simpa [List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using shifted

/-- Related source environments are no longer than their targets. -/
theorem envRel_length {α : Type} (offsets : List Nat) (d : Nat)
    (source target : List α) (related : envRel offsets d source target) :
    source.length ≤ target.length := by
  induction offsets generalizing source target with
  | nil =>
    simp only [envRel] at related
    subst source
    simp
  | cons a rest ih =>
    cases source with
    | nil => simp
    | cons x source =>
      cases target with
      | nil => simp [envRel] at related
      | cons y target =>
        simp only [envRel] at related
        simpa using ih source target related.2

/-- The variable case of let-optimizer evaluation preserves every result
except the source type error. Untagged until BVI evaluation is reviewed. -/
theorem evaluate_compile_var {C F : Type} (offsets : List Nat) (d index : Nat)
    (source target : List BvlSem.Value) (state next : BviSem.BviState C F)
    (result : BviSem.BviResult) (related : envRel offsets d source target)
    (run : BviSem.evaluate [.var index] source state = (result, next))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    BviSem.evaluate [compileSing offsets d (.var index)] target state = (result, next) := by
  cases lookup : source[index]? with
  | none =>
    simp [BviSem.evaluate, lookup] at run
    exact False.elim (notTypeError run.1.symm)
  | some value =>
    have targetLookup := envRel_lookup offsets d source target related index value lookup
    simp [BviSem.evaluate, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    simp [compileSing, BviSem.evaluate, targetLookup]

/-- Removing a variable expression preserves a non-type-error singleton
failure. Untagged until BVI evaluation is reviewed. -/
theorem evaluate_deleteVar_error {C F : Type} (expression : Bvi.Exp)
    (env : List BvlSem.Value) (state next : BviSem.BviState C F)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (run : BviSem.evaluate [expression] env state = (.err error, next))
    (notTypeError : error ≠ .abort .typeError) :
    BviSem.evaluate [deleteVar expression] env state = (.err error, next) := by
  cases expression with
  | var index =>
    cases lookup : env[index]? with
    | none =>
      simp [BviSem.evaluate, lookup] at run
      exact False.elim (notTypeError run.1.symm)
    | some value => simp [BviSem.evaluate, lookup] at run
  | _ => simpa [deleteVar] using run

end Flapjack.Compiler.Backend.BviLet.Proofs
