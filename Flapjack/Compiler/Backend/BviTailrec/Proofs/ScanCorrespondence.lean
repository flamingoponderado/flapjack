import Flapjack.Compiler.Backend.BviTailrec.Proofs.ScanTotal
import Flapjack.Compiler.Backend.BviTailrec.Proofs.TermCorrespondence
import Flapjack.Compiler.Backend.BviTailrec.Proofs.HasRecCorrespondence

/-! Correspondence between source-shaped and executed tail-recursion scans. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

mutual
/-- A singleton list scan returns exactly the source single-expression scan. -/
theorem scanExpr_single (ctx : List ValueType) (loc : Nat) (e : Exp) :
    scanExpr ctx loc [e] = [scanSing ctx loc e] := by
  cases e with
  | ifThenElse cond yes no =>
    rw [scanExpr.eq_def, scanSing.eq_def]
    try dsimp only
    rw [scanExpr_single ctx loc cond]
    try dsimp only
    rw [scanExpr_single _ loc yes, scanExpr_single _ loc no]
    rfl
  | «let» xs body =>
    rw [scanExpr.eq_def, scanSing.eq_def]
    try dsimp only
    rw [scanExpr_list ctx loc xs]
    rw [scanExpr_single _ loc body]
    cases last : (scanList ctx loc xs).getLast? with
    | none => rfl
    | some s => obtain ⟨a, b, c, d⟩ := s; rfl
  | tick body =>
    rw [scanExpr.eq_def, scanSing.eq_def]
    try dsimp only
    exact scanExpr_single ctx loc body
  | var n => rw [scanExpr.eq_def]
  | force a n => rw [scanExpr.eq_def]
  | op op xs => rw [scanExpr.eq_def]
  | raise e => rw [scanExpr.eq_def]
  | call a b c d => rw [scanExpr.eq_def]
  | «return» xs => rw [scanExpr.eq_def]
  | letCall a b c d e => rw [scanExpr.eq_def]
termination_by sizeOf e

/-- The source list traversal agrees with the context-threaded list scan. -/
theorem scanExpr_list (ctx : List ValueType) (loc : Nat) (xs : List Exp) :
    scanExpr ctx loc xs = scanList ctx loc xs := by
  cases xs with
  | nil => rw [scanExpr.eq_def, scanList.eq_def]
  | cons x xs =>
    cases xs with
    | nil =>
      rw [scanExpr_single, scanList.eq_def]
      dsimp only
      rw [scanList.eq_def]
    | cons y ys =>
      rw [scanExpr.eq_def, scanList.eq_def]
      try dsimp only
      rw [scanExpr_single ctx loc x]
      try dsimp only
      rw [scanExpr_list _ loc (y :: ys)]
      rfl
termination_by sizeOf xs
end

/-- Refining an operand never changes the context length. -/
theorem update_length (ty : ValueType) (e : Exp) (ctx : List ValueType) :
    (update ty e ctx).length = ctx.length := by
  cases e <;> simp [update]
  split <;> simp

/-- Refining both operands never changes the context length. -/
theorem updateContext_length (ty : ValueType) (ctx : List ValueType) (x y : Exp) :
    (updateContext ty ctx x y).length = ctx.length := by
  simp [updateContext, update_length]

/-- Scanning operands produces one result per input expression. -/
theorem scanList_length (ctx : List ValueType) (loc : Nat) (xs : List Exp) :
    (scanList ctx loc xs).length = xs.length := by
  induction xs generalizing ctx with
  | nil => rw [scanList.eq_def]; rfl
  | cons x xs ih =>
    rw [scanList.eq_def]
    simp only [List.length_cons]
    rw [ih]

/-- The source-shaped list scan preserves the input length. -/
theorem scanExpr_length (ctx : List ValueType) (loc : Nat) (xs : List Exp) :
    (scanExpr ctx loc xs).length = xs.length := by
  rw [scanExpr_list, scanList_length]

/-- A source-shaped singleton scan cannot be empty. -/
theorem scanExpr_single_ne_nil (ctx : List ValueType) (loc : Nat) (e : Exp) :
    scanExpr ctx loc [e] ≠ [] := by
  simp [scanExpr_single]

mutual
/-- A single scan preserves the length of the inferred context. -/
theorem scanSing_context_length (ctx : List ValueType) (loc : Nat) (e : Exp) :
    (scanSing ctx loc e).1.length = ctx.length := by
  cases e with
  | ifThenElse cond yes no =>
    rw [scanSing.eq_def]
    dsimp only
    have hc := scanSing_context_length ctx loc cond
    have hy := scanSing_context_length (scanSing ctx loc cond).1 loc yes
    have hn := scanSing_context_length (scanSing ctx loc cond).1 loc no
    simp only [List.length_map, List.length_zip]
    omega
  | «let» xs body =>
    rw [scanSing.eq_def]
    dsimp only
    generalize hscans : scanList ctx loc xs = scans
    cases last : scans.getLast? with
    | none =>
      simp only
      have length := scanSing_context_length
        ((scans.map fun (_, ty, _, _) => ty) ++ ctx) loc body
      simp only [List.length_append, List.length_map] at length
      simp only [List.length_drop]
      omega
    | some entry =>
      have entryLength : entry.1.length = ctx.length := by
        apply scanList_context_length ctx loc xs entry
        rw [hscans]
        exact List.mem_of_getLast? last
      obtain ⟨a, b, c, d⟩ := entry
      change a.length = ctx.length at entryLength
      simp only
      have length := scanSing_context_length
        ((scans.map fun (_, ty, _, _) => ty) ++ a) loc body
      simp only [List.length_append, List.length_map] at length
      simp only [List.length_drop]
      omega
  | tick body =>
    rw [scanSing.eq_def]
    exact scanSing_context_length ctx loc body
  | op op xs =>
    rw [scanSing.eq_def]
    dsimp only
    cases h : fromOp op == .noop with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases check : (checkOp ctx (fromOp op) loc (.op op xs)).isSome <;>
        simp only [Bool.false_eq_true, ↓reduceIte]
      cases termResult : term ctx (opType (fromOp op)) (.op op xs) <;>
        simp only [Bool.false_eq_true, ↓reduceIte]
      cases xs with
      | nil => rfl
      | cons x xs => cases xs with
        | nil => rfl
        | cons y ys => cases ys <;> simp [updateContext_length]
    | true =>
      simp only [↓reduceIte]
      cases arg : argType op == .int <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · cases xs with
        | nil =>
          cases op <;> try rfl
          case blockOp operation => cases operation <;> (try simp) <;> (try split) <;> rfl
        | cons x xs => cases xs with
          | nil =>
            cases op <;> try rfl
            case blockOp operation => cases operation <;> (try simp) <;> (try split) <;> rfl
          | cons y ys =>
            cases op <;> try rfl
            case blockOp operation => cases operation <;> (try simp) <;> (try split) <;> rfl
      · cases xs with
        | nil => cases c : isConst op <;> simp
        | cons x xs => cases xs with
          | nil => cases c : isConst op <;> simp
          | cons y ys => cases ys <;> cases c : isConst op <;> simp [updateContext_length]
  | var n => rw [scanSing.eq_def]
  | force l n => rw [scanSing.eq_def]
  | raise e => rw [scanSing.eq_def]
  | call a b c d => rw [scanSing.eq_def]
  | «return» xs => rw [scanSing.eq_def]
  | letCall a b c d e => rw [scanSing.eq_def]
termination_by sizeOf e

/-- Every context in a list scan has the input context's length. -/
theorem scanList_context_length (ctx : List ValueType) (loc : Nat) (xs : List Exp)
    (entry : List ValueType × ValueType × Bool × Option AssocOp)
    (mem : entry ∈ scanList ctx loc xs) : entry.1.length = ctx.length := by
  cases xs with
  | nil => rw [scanList.eq_def] at mem; simp at mem
  | cons x xs =>
    rw [scanList.eq_def] at mem
    dsimp only at mem
    simp only [List.mem_cons] at mem
    rcases mem with same | tail
    · subst entry; exact scanSing_context_length ctx loc x
    · exact (scanList_context_length _ loc xs entry tail).trans (scanSing_context_length ctx loc x)
termination_by sizeOf xs
end

/-- Every context produced by the source-shaped list scan has the input
context's length. -/
theorem scanExpr_context_length (ctx : List ValueType) (loc : Nat) (xs : List Exp)
    (entry : List ValueType × ValueType × Bool × Option AssocOp)
    (mem : entry ∈ scanExpr ctx loc xs) : entry.1.length = ctx.length := by
  rw [scanExpr_list] at mem
  exact scanList_context_length ctx loc xs entry mem

/-- Every recognized accumulator operator round-trips to its source BVI
operation. -/
theorem toOp_fromOp (op : ClosLang.Op) (recognized : fromOp op ≠ .noop) : toOp (fromOp op) = op := by
  cases op <;> try (simp_all [fromOp, toOp])
  case intOp operation => cases operation <;> simp_all
  case blockOp operation => cases operation <;> simp_all

/-- Classifying an accumulator operation after conversion recovers it. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "from_op_to_op"]
theorem fromOp_toOp (assoc : AssocOp) : fromOp (toOp assoc) = assoc := by
  cases assoc <;> rfl

/-- Candidate analysis agrees with the source check on each operation
recognized by `fromOp`. -/
theorem checkOpFuel_eq_recognized (fuel : Nat) (ctx : List ValueType) (op : ClosLang.Op)
    (loc : Nat) (args : List Exp) (recognized : fromOp op ≠ .noop) :
    checkOpFuel fuel ctx (fromOp op) loc args = some (checkOp ctx (fromOp op) loc (.op op args)) := by
  have opEq := toOp_fromOp op recognized
  simpa only [opEq] using checkOpFuel_eq fuel ctx (fromOp op) loc args recognized

/-- The operation branch of the executed scan agrees with the source scan
whenever it returns. -/
theorem scanFuel_op_eq (fuel : Nat) (ctx : List ValueType) (loc : Nat)
    (op : ClosLang.Op) (args : List Exp)
    (result : List ValueType × ValueType × Bool × Option AssocOp)
    (run : scanFuel (fuel + 1) ctx loc (.op op args) = some result) :
    result = scanSing ctx loc (.op op args) := by
  have same : scanFuel (fuel + 1) ctx loc (.op op args) = some (scanSing ctx loc (.op op args)) := by
    rw [scanFuel.eq_def, scanSing.eq_def]
    dsimp only
    cases assoc : fromOp op with
    | noop =>
      simp only [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx]
      cases args with
      | nil => cases op <;> simp_all [apply_ite] <;> split <;> simp_all
      | cons x xs => cases xs with
        | nil => simp_all [apply_ite]
        | cons y ys => cases ys <;> simp_all [apply_ite]
    | plus | times | append =>
      have recognized : fromOp op ≠ .noop := by rw [assoc]; decide
      have checked := checkOpFuel_eq_recognized fuel ctx op loc args recognized
      rw [assoc] at checked
      simp only [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx,
        checked, termBounded_eq, bind, Option.bind, pure]
      cases check : checkOp ctx _ loc (.op op args) <;> cases termResult : term ctx _ (.op op args) <;>
        cases args with
        | nil => simp_all
        | cons x xs => cases xs with
          | nil => simp_all
          | cons y ys => cases ys <;> simp_all
  rw [same] at run
  exact (Option.some.inj run).symm

/-- Successful fuel-bounded scans return the source-shaped scan results. -/
theorem scanFuel_correspondence (fuel : Nat) :
    (∀ ctx loc e result, scanFuel fuel ctx loc e = some result → result = scanSing ctx loc e) ∧
    (∀ ctx loc xs result, scanListFuel fuel ctx loc xs = some result → result = scanList ctx loc xs) := by
  induction fuel with
  | zero =>
    constructor
    · intro ctx loc e result run
      simp [scanFuel] at run
    · intro ctx loc xs result run
      cases xs <;> simp_all [scanListFuel, scanList.eq_def]
  | succ fuel ih =>
    constructor
    · intro ctx loc e result run
      cases e with
      | op op args => exact scanFuel_op_eq fuel ctx loc op args result run
      | ifThenElse cond yes no =>
        cases hc : scanFuel fuel ctx loc cond with
        | none => simp [scanFuel, hc] at run
        | some c =>
          have ceq := ih.1 ctx loc cond c hc
          subst c
          cases hy : scanFuel fuel (scanSing ctx loc cond).1 loc yes with
          | none => simp [scanFuel, hc, hy] at run
          | some y =>
            have yeq := ih.1 (scanSing ctx loc cond).1 loc yes y hy
            subst y
            cases hn : scanFuel fuel (scanSing ctx loc cond).1 loc no with
            | none => simp [scanFuel, hc, hy, hn] at run
            | some n =>
              have neq := ih.1 (scanSing ctx loc cond).1 loc no n hn
              subst n
              rw [scanSing.eq_def]
              simpa [scanFuel, hc, hy, hn] using run.symm
      | «let» xs body =>
        cases hs : scanListFuel fuel ctx loc xs with
        | none => simp [scanFuel, hs] at run
        | some scans =>
          have seq := ih.2 ctx loc xs scans hs
          subst scans
          simp only [scanFuel, hs, bind, Option.bind, pure] at run
          generalize hb : scanFuel fuel _ loc body = answer at run
          cases answer with
          | none => simp at run
          | some b =>
            have beq := ih.1 _ loc body b hb
            subst b
            rw [scanSing.eq_def]
            simpa using run.symm
      | tick body =>
        rw [scanSing.eq_def]
        exact ih.1 ctx loc body result run
      | var n => simpa [scanFuel, scanSing.eq_def] using run.symm
      | force b n => simpa [scanFuel, scanSing.eq_def] using run.symm
      | raise e => simpa [scanFuel, scanSing.eq_def] using run.symm
      | call a b c d => simpa [scanFuel, scanSing.eq_def] using run.symm
      | «return» xs => simpa [scanFuel, scanSing.eq_def] using run.symm
      | letCall a b c d e => simpa [scanFuel, scanSing.eq_def] using run.symm
    · intro ctx loc xs result run
      cases xs with
      | nil => simpa [scanListFuel, scanList.eq_def] using run.symm
      | cons x xs =>
        cases hx : scanFuel fuel ctx loc x with
        | none => simp [scanListFuel, hx] at run
        | some head =>
          have heq := ih.1 ctx loc x head hx
          subst head
          cases ht : scanListFuel fuel (scanSing ctx loc x).1 loc xs with
          | none => simp [scanListFuel, hx, ht] at run
          | some tail =>
            have teq := ih.2 (scanSing ctx loc x).1 loc xs tail ht
            subst tail
            rw [scanList.eq_def]
            simpa [scanListFuel, hx, ht] using run.symm

/-- Retrying with structural fuel computes the source expression scan. -/
theorem scanBounded_eq (fuel : Nat) (ctx : List ValueType) (loc : Nat) (e : Exp) :
    scanBounded fuel ctx loc e = some (scanSing ctx loc e) := by
  cases h : scanFuel fuel ctx loc e with
  | some result =>
    have eq := (scanFuel_correspondence fuel).1 ctx loc e result h
    subst result
    simp [scanBounded, h]
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := scanFuel_succeeds (max fuel (expBudget e + 1)) ctx loc e bound
    have eq := (scanFuel_correspondence _).1 ctx loc e result done
    subst result
    simp [scanBounded, h, done]

/-- Retrying with structural fuel computes the source list scan. -/
theorem scanListBounded_eq (fuel : Nat) (ctx : List ValueType) (loc : Nat) (xs : List Exp) :
    scanListBounded fuel ctx loc xs = some (scanList ctx loc xs) := by
  cases h : scanListFuel fuel ctx loc xs with
  | some result =>
    have eq := (scanFuel_correspondence fuel).2 ctx loc xs result h
    subst result
    simp [scanListBounded, h]
  | none =>
    have bound : listBudget xs < max fuel (listBudget xs + 1) := by omega
    obtain ⟨result, done⟩ := scanListFuel_succeeds (max fuel (listBudget xs + 1)) ctx loc xs bound
    have eq := (scanFuel_correspondence _).2 ctx loc xs result done
    subst result
    simp [scanListBounded, h, done]

/-- Flapjack's single-expression form of the source rewrite decision. The
source definition uses a singleton list scan; this form uses `scanSing`. -/
def checkExpSingle (loc arity : Nat) (e : Exp) : Option AssocOp :=
  if !hasRec1 loc e then none else
    let (_, ty, _, op) := scanSing (List.replicate arity .any) loc e
    match op with
    | some o => if ty == opType o then some o else none
    | none => none

/-- Source-shaped candidate decision using the original list-based scan. -/
def checkExpOriginal (loc arity : Nat) (e : Exp) : Option AssocOp :=
  if !hasRec1 loc e then none else
    match scanExpr (List.replicate arity .any) loc [e] with
    | [] => none
    | (_, ty, _, op) :: _ =>
      match op with
      | some o => if ty == opType o then some o else none
      | none => none

/-- The source's list-based decision and its singleton form agree. -/
theorem checkExpOriginal_eq (loc arity : Nat) (e : Exp) :
    checkExpOriginal loc arity e = checkExpSingle loc arity e := by
  simp [checkExpOriginal, checkExpSingle, scanExpr_single]

/-- The executed decision computes the source-shaped single-expression
decision for every fuel value. -/
theorem checkExpFuel_eq (fuel loc arity : Nat) (e : Exp) :
    checkExpFuel fuel loc arity e = some (checkExpSingle loc arity e) := by
  simp [checkExpFuel, checkExpSingle, hasRecBounded_eq_hasRec1, scanBounded_eq]
  split <;> simp_all
  split <;> simp_all

end Flapjack.Compiler.Backend.BviTailrec
