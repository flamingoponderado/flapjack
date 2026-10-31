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

/-- A small integer constant evaluates to its integer value without changing
the BVI state. This is untagged pending evaluator and dispatcher review. -/
theorem evaluate_smallInt {C F : Type} (k : Int) (small : smallEnoughInt k)
    (env : List Value) (state : BviSem.BviState C F) :
    BviSem.evaluate [.op (.intOp (.const k)) []] env state = (.val [.number k], state) := by
  simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
    BviSem.doAppAux, small]

/-- Constant case of the integer-term evaluation theorem, with the source
term checker supplying the small-integer side condition. -/
theorem termInt_const_evaluation {C F : Type} (ts : List ValueType) (k : Int)
    (env : List Value) (state next : BviSem.BviState C F) (result : BviSem.BviResult)
    (h : termInt ts (.op (.intOp (.const k)) []) = true ∧ tyRel env ts ∧
      BviSem.evaluate [.op (.intOp (.const k)) []] env state = (result, next)) :
    state = next ∧ ∃ value, result = .val [value] ∧
      (∀ state' : BviSem.BviState C F,
        BviSem.evaluate [.op (.intOp (.const k)) []] env state' = (result, state')) ∧
      ∃ integer, value = .number integer := by
  obtain ⟨term, _, run⟩ := h
  have small : smallEnoughInt k := by
    rw [termInt.eq_def] at term
    change (decide (-268435457 ≤ k) && decide (k ≤ 268435457)) = true at term
    simpa [smallEnoughInt] using term
  have resultEq : (result, next) = (.val [.number k], state) := by
    simpa [evaluate_smallInt k small env state] using run.symm
  cases resultEq
  exact ⟨rfl, .number k, rfl, (fun state' => evaluate_smallInt k small env state'), k, rfl⟩

/-- Arithmetic operators accepted by the integer-term checker return an
integer and preserve the state for two integer operands. -/
theorem doApp_arith {C F : Type} (op : ClosLang.IntOp) (a b : Int)
    (allowed : isArith (.intOp op) = true) :
    ∃ integer, ∀ state : BviSem.BviState C F,
      BviSem.doApp (.intOp op) [.number a, .number b] state = (.val (.number integer, state)) := by
  cases op <;> try simp [isArith] at allowed
  case add =>
    refine ⟨a + b, ?_⟩
    intro state
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp, BviSem.fromBvl_toBvl]

  case sub =>
    refine ⟨a - b, ?_⟩
    intro state
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp, BviSem.fromBvl_toBvl]
  case mult =>
    refine ⟨a * b, ?_⟩
    intro state
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp, BviSem.fromBvl_toBvl]

/-- Every accepted integer term evaluates to the same integer in every BVI
state and leaves that state unchanged. Untagged pending evaluator review. -/
theorem termInt_total {C F : Type} (ts : List ValueType) (e : Bvi.Exp) (env : List Value)
    (accepted : termInt ts e = true) (related : tyRel env ts) :
    ∃ integer, ∀ state : BviSem.BviState C F,
      BviSem.evaluate [e] env state = (.val [.number integer], state) := by
  cases e with
  | var n =>
    have found : ts[n]? = some .int := by
      cases hget : ts[n]? with
      | none => simp [termInt, hget] at accepted
      | some ty =>
        cases ty <;> simp_all [termInt, BEq.beq, Option.instBEq.beq, instBEqValueType.beq, ValueType.ctorIdx]
    obtain ⟨value, lookup, typed, _⟩ := tyRel_lookup related n .int found
    obtain ⟨integer, rfl⟩ := typed rfl
    exact ⟨integer, by intro state; simp [BviSem.evaluate, lookup]⟩
  | op op xs =>
    cases xs with
    | nil =>
      cases op with
      | intOp operation =>
        cases operation with
        | const k =>
          have small : smallEnoughInt k := by
            rw [termInt.eq_def] at accepted
            change (decide (-268435457 ≤ k) && decide (k ≤ 268435457)) = true at accepted
            simpa [smallEnoughInt] using accepted
          exact ⟨k, fun state => evaluate_smallInt k small env state⟩
        | _ => simp [termInt, isConst] at accepted
      | _ => simp [termInt, isConst] at accepted
    | cons x xs =>
      cases xs with
      | nil => simp [termInt] at accepted
      | cons y ys =>
        cases ys with
        | cons z zs => simp [termInt] at accepted
        | nil =>
          have parts : isArith op = true ∧ termInt ts x = true ∧ termInt ts y = true := by
            rw [termInt.eq_def] at accepted
            change (isArith op && termInt ts x && termInt ts y) = true at accepted
            simpa only [Bool.and_eq_true, and_assoc] using accepted
          obtain ⟨a, ha⟩ := termInt_total ts x env parts.2.1 related
          obtain ⟨b, hb⟩ := termInt_total ts y env parts.2.2 related
          cases op with
          | intOp operation =>
            obtain ⟨integer, hr⟩ := doApp_arith (C := C) (F := F) operation b a parts.1
            refine ⟨integer, ?_⟩
            intro state
            have args := BvlToBvi.Proofs.evaluate_pair x y env state (.number a) (.number b) (ha state) (hb state)
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
              List.cons_append]
            rw [hr state]
          | _ => simp [isArith] at parts
  | _ => simp [termInt] at accepted
termination_by sizeOf e

/-- Integer-term evaluation has the source theorem's result and state shape.
This is untagged until the BVI evaluator and dispatcher are source-reviewed. -/
theorem termInt_evaluation {C F : Type} (ts : List ValueType) (e : Bvi.Exp)
    (env : List Value) (state next : BviSem.BviState C F) (result : BviSem.BviResult)
    (h : termInt ts e = true ∧ tyRel env ts ∧ BviSem.evaluate [e] env state = (result, next)) :
    state = next ∧ ∃ value, result = .val [value] ∧
      (∀ state' : BviSem.BviState C F, BviSem.evaluate [e] env state' = (result, state')) ∧
      ∃ integer, value = .number integer := by
  obtain ⟨accepted, related, run⟩ := h
  obtain ⟨integer, evaluate⟩ := termInt_total (C := C) (F := F) ts e env accepted related
  have resultEq : (result, next) = (.val [.number integer], state) := run.symm.trans (evaluate state)
  cases resultEq
  exact ⟨rfl, .number integer, rfl, evaluate, integer, rfl⟩

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
