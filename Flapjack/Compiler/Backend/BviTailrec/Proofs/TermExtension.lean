import Flapjack.Compiler.Backend.BviTailrec.Proofs.Semantics

/-! The source term checks remain valid when their type context is extended.
These results remain untagged pending carrier review. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi BvlSem

/-- Extending a context preserves accepted integer terms. -/
theorem termInt_extend (e : Bvi.Exp) (ctx extra : List ValueType)
    (accepted : termInt ctx e = true) : termInt (ctx ++ extra) e = true := by
  cases e with
  | var n =>
    have found : ctx[n]? = some .int := by
      cases h : ctx[n]? with
      | none => simp [termInt, h] at accepted
      | some ty => cases ty <;> simp_all [termInt, BEq.beq, Option.instBEq.beq,
          instBEqValueType.beq, ValueType.ctorIdx]
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp [termInt, List.getElem?_append_left bound, found, BEq.beq, Option.instBEq.beq, instBEqValueType.beq, ValueType.ctorIdx]
  | op operation args =>
    cases args with
    | nil => simpa [termInt.eq_def] using accepted
    | cons x rest =>
      cases rest with
      | nil => simp [termInt.eq_def] at accepted
      | cons y tail =>
        cases tail with
        | cons z zs => simp [termInt.eq_def] at accepted
        | nil =>
          rw [termInt.eq_def] at accepted ⊢
          simp only [Bool.and_eq_true] at accepted ⊢
          exact ⟨⟨accepted.1.1, termInt_extend x ctx extra accepted.1.2⟩,
            termInt_extend y ctx extra accepted.2⟩
  | _ => simp [termInt.eq_def] at accepted
termination_by sizeOf e

/-- Extending a context preserves accepted list and arbitrary terms. -/
theorem termAny_extend (e : Bvi.Exp) (ctx extra : List ValueType) (list : Bool)
    (accepted : termAny ctx list e = true) : termAny (ctx ++ extra) list e = true := by
  cases e with
  | var n =>
    cases list with
    | false =>
      have bound : n < ctx.length := by simpa [termAny] using accepted
      simp [termAny, List.length_append, show n < ctx.length + extra.length by omega]
    | true =>
      have found : ctx[n]? = some .list := by
        cases h : ctx[n]? with
        | none => simp [termAny, h] at accepted
        | some ty => cases ty <;> simp_all [termAny, BEq.beq, Option.instBEq.beq,
            instBEqValueType.beq, ValueType.ctorIdx]
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simp [termAny, List.getElem?_append_left bound, found, BEq.beq, Option.instBEq.beq,
        instBEqValueType.beq, ValueType.ctorIdx]
  | op operation args =>
    cases args with
    | nil =>
      cases operation with
      | blockOp block =>
        cases block with
        | cons tag => cases tag <;> simpa [termAny] using accepted
        | _ => simpa [termAny] using accepted
      | _ => simpa [termAny] using accepted
    | cons x rest =>
      cases rest with
      | nil => simp [termAny.eq_def] at accepted
      | cons y tail =>
        cases tail with
        | cons z zs => simp [termAny.eq_def] at accepted
        | nil =>
          cases operation with
          | blockOp block =>
            cases block with
            | listAppend =>
              rw [termAny.eq_def] at accepted ⊢
              simp only [Bool.and_eq_true] at accepted ⊢
              exact ⟨termAny_extend x ctx extra true accepted.1, termAny_extend y ctx extra true accepted.2⟩
            | cons tag =>
              cases tag with
              | zero =>
                rw [termAny.eq_def] at accepted ⊢
                simp only [Bool.and_eq_true] at accepted ⊢
                exact ⟨termAny_extend x ctx extra true accepted.1, termAny_extend y ctx extra false accepted.2⟩
              | succ tag => cases list <;> simp [termAny, isArith, isRel] at accepted
            | _ => cases list <;> simp [termAny, isArith, isRel] at accepted
          | intOp operation =>
            cases list with
            | true => simp [termAny] at accepted
            | false =>
              rw [termAny.eq_def] at accepted ⊢
              simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true] at accepted ⊢
              exact ⟨⟨accepted.1.1, termInt_extend x ctx extra accepted.1.2⟩,
                termInt_extend y ctx extra accepted.2⟩
          | _ => cases list <;> simp [termAny, isArith, isRel] at accepted
  | _ => simp [termAny.eq_def] at accepted
termination_by sizeOf e

/-- The type-directed term check is monotone under context extension. -/
theorem term_extend (e : Bvi.Exp) (ctx extra : List ValueType) (ty : ValueType)
    (accepted : term ctx ty e = true) : term (ctx ++ extra) ty e = true := by
  cases ty with
  | int => exact termInt_extend e ctx extra accepted
  | list => exact termAny_extend e ctx extra true accepted
  | any => exact termAny_extend e ctx extra false accepted

/-- Every list of values satisfies an equally long unknown-type context. -/
theorem tyRel_unknown (values : List Value) : tyRel values (List.replicate values.length .any) := by
  induction values with
  | nil => simp [tyRel]
  | cons value rest ih =>
    simp only [List.length_cons, List.replicate_succ]
    exact .cons (by simp) ih

/-- Extending a related value environment extends its type context with
unknown entries. -/
theorem tyRel_prefix_extend (env : List Value) (ctx : List ValueType) (suffix : List Value)
    (related : tyRel env ctx) :
    tyRel (env ++ suffix) (ctx ++ List.replicate suffix.length .any) := by
  exact tyRel_append suffix (List.replicate suffix.length .any) ctx env ⟨tyRel_unknown suffix, related⟩

end Flapjack.Compiler.Backend.BviTailrec
