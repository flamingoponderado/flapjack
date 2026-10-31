import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteCorrespondence
import Flapjack.Compiler.Backend.Semantics.BvlSem.Value
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ListLengthStub
import Mathlib.Data.List.Forall2

/-! Value and environment relations used by the source tail-recursion proof. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open BvlSem
open Flapjack.Compiler.Backend.BackendCommon

/-- The inferred type context is sound for each value in the environment. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "ty_rel_def"]
def tyRel (env : List Value) (types : List ValueType) : Prop :=
  List.Forall₂ (fun value ty =>
    (ty = .int → ∃ k, value = .number k) ∧
    (ty = .list → ∃ ys, valueToList value = some ys)) env types

/-- Value of the identity expression for each accumulator operation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "op_id_val_def"]
def opIdValue : AssocOp → Value
  | .plus => .number 0
  | .times => .number 1
  | .append => .block nilTag []
  | .noop => .number 6333

/-- The source environment relation, using optional lookup for its bounded
accumulator position. The source uses `EL`; the bound makes the lookup total. -/
def envRel (ty : ValueType) (optimized : Bool) (acc : Nat)
    (env1 env2 : List Value) : Prop :=
  env1 <+: env2 ∧
    (optimized = true → env1.length = acc ∧ acc < env2.length ∧
      match ty with
      | .int => ∃ k, env2[acc]? = some (.number k)
      | .list => ∃ value ys, env2[acc]? = some value ∧ valueToList value = some ys
      | .any => False)

/-- Decoding the source list encoding returns the original elements. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "list_to_v_simp"]
theorem listToValue_decode (xs : List Value) : valueToList (listToValue xs) = some xs :=
  valueToList_listToValue xs

/-- A successfully decoded list is the corresponding canonical encoding. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "list_to_v_imp"]
theorem listToValue_of_decode (x : Value) (xs : List Value)
    (h : valueToList x = some xs) : listToValue xs = x :=
  BvlToBvi.Proofs.valueToList_inverse x xs h

/-- A sound type context has exactly one entry per environment value. -/
theorem tyRel_length {env : List Value} {types : List ValueType} (h : tyRel env types) :
    env.length = types.length := h.length_eq

/-- A context lookup identifies an environment value satisfying its inferred
type. This is auxiliary infrastructure for the term-evaluation cases. -/
theorem tyRel_lookup {env : List Value} {types : List ValueType} (h : tyRel env types)
    (n : Nat) (ty : ValueType) (found : types[n]? = some ty) :
    ∃ value, env[n]? = some value ∧
      (ty = .int → ∃ k, value = .number k) ∧
      (ty = .list → ∃ ys, valueToList value = some ys) := by
  induction h generalizing n ty with
  | nil => simp at found
  | @cons value head env types hhead htail ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst ty
      exact ⟨value, rfl, hhead⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at found ⊢
      exact ih n ty found

/-- Variable case of integer-term evaluation. This is untagged until the
source evaluator's state and primitive dispatcher have been reviewed. -/
theorem termInt_var_evaluation {C F : Type} (ts : List ValueType) (n : Nat)
    (env : List Value) (state next : BviSem.BviState C F) (result : BviSem.BviResult)
    (h : termInt ts (.var n) = true ∧ tyRel env ts ∧
      BviSem.evaluate [.var n] env state = (result, next)) :
    state = next ∧ ∃ value, result = .val [value] ∧
      (∀ state' : BviSem.BviState C F, BviSem.evaluate [.var n] env state' = (result, state')) ∧
      ∃ k, value = .number k := by
  obtain ⟨term, related, run⟩ := h
  have found : ts[n]? = some .int := by
    cases hget : ts[n]? with
    | none => simp [termInt, hget] at term
    | some ty =>
      cases ty <;> simp_all [termInt, BEq.beq, Option.instBEq.beq, instBEqValueType.beq, ValueType.ctorIdx]
  obtain ⟨value, lookup, typed, _⟩ := tyRel_lookup related n .int found
  obtain ⟨k, eq⟩ := typed rfl
  have resultEq : (result, next) = (.val [value], state) := by
    simpa [BviSem.evaluate, lookup] using run.symm
  cases resultEq
  exact ⟨rfl, value, rfl, (by intro state'; simp [BviSem.evaluate, lookup]), k, eq⟩

/-- Type soundness is preserved by prefixing related values and types. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "ty_rel_APPEND"]
theorem tyRel_append (env : List Value) (ts ws : List ValueType) (vs : List Value)
    (h : tyRel env ts ∧ tyRel vs ws) : tyRel (vs ++ env) (ws ++ ts) := by
  exact List.rel_append h.2 h.1

/-- A source-typed environment remains well typed when joined with another
context of the same length. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "ty_rel_decide_ty"]
theorem tyRel_decideType (ts tt : List ValueType) (env : List Value)
    (hyp : (tyRel env ts ∨ tyRel env tt) ∧ ts.length = tt.length) :
    tyRel env ((ts.zip tt).map fun (x, y) => decideType x y) := by
  obtain ⟨valid, sameLength⟩ := hyp
  induction ts generalizing tt env with
  | nil =>
    cases tt <;> simp_all [tyRel]
  | cons t ts ih =>
    cases tt with
    | nil => simp at sameLength
    | cons u tt =>
      cases env with
      | nil => simp [tyRel] at valid
      | cons v env =>
        simp only [tyRel, List.forall₂_cons] at valid ⊢
        have tails : tyRel env ts ∨ tyRel env tt := by
          rcases valid with h | h
          · exact Or.inl h.2
          · exact Or.inr h.2
        constructor
        · cases t <;> cases u <;> simp_all [decideType, tyRel] <;> tauto
        · exact ih tt env tails (by simpa using sameLength)

end Flapjack.Compiler.Backend.BviTailrec
