import Flapjack.Compiler.Backend.BviTailrec.Proofs.ScanCorrespondence
import Flapjack.Compiler.Backend.BviTailrec.Proofs.Total

/-! Correspondence between the executed accumulator rewrite and the
source-shaped rewrite, using the source single-expression scan form. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

/-- A source candidate that does not match the requested operator is rejected. -/
theorem checkOp_of_not_opEq (ctx : List ValueType) (op : AssocOp) (loc : Nat) (e : Exp)
    (mismatch : opEq op e = false) : checkOp ctx op loc e = none := by
  simp [checkOp, trySwap, opBinArgs, mismatch]

/-- The executable's operator guard recognizes exactly the source predicate. -/
theorem opEq_guard (op : AssocOp) (actual : ClosLang.Op) (xs : List Exp) :
    opEq op (.op actual xs) = (fromOp actual == op && op != .noop) := by
  cases op <;> cases actual <;> simp [opEq, fromOp, BEq.beq, instBEqAssocOp.beq,
    AssocOp.ctorIdx, bne]
  all_goals rename_i operation; cases operation <;> simp

/-- Every successful source check constructs an operator applied to a value and
a direct recursive call; the call has no exception handler. -/
theorem checkOp_success_shape (ctx : List ValueType) (op : AssocOp) (loc : Nat)
    (e checked : Exp) (success : checkOp ctx op loc e = some checked) :
    ∃ value ticks dest args, checked = applyOp op value (.call ticks (some dest) args none) := by
  simp only [checkOp] at success
  cases args : opBinArgs op (trySwap loc op e) with
  | none => simp [args] at success
  | some pair =>
    obtain ⟨value, call⟩ := pair
    simp only [args] at success
    split at success
    next accepted =>
      simp only [Option.some.injEq] at success
      subst checked
      have both : isRec loc call = true ∧ term ctx (opType op) value = true := by
        simpa only [Bool.and_eq_true] using accepted
      have recCall := both.1
      cases call <;> simp [isRec] at recCall
      case call ticks dest values handler =>
        cases dest <;> cases handler <;> simp_all [isRec]
        exact ⟨value, ticks, _, values, rfl⟩
    next => simp at success

/-- The non-structural branch of the original rewrite definition. -/
def sourceDispatch (loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) (e : Exp) : Bool × Exp :=
  match checkOp ctx op loc e with
  | none => (false, applyOp op (.var acc) e)
  | some checked =>
    match opBinArgs op checked with
    | none => (false, applyOp op (.var acc) checked)
    | some (value, call) => (true, pushCall next op acc value (argsFrom call))

/-- `Noop` cannot select a source operation candidate. -/
theorem checkOp_noop (ctx : List ValueType) (loc : Nat) (e : Exp) :
    checkOp ctx .noop loc e = none := by
  apply checkOp_of_not_opEq
  cases e <;> rfl

/-- The normalized operation branch is exactly the original source dispatch. -/
theorem sourceDispatch_op (loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) (actual : ClosLang.Op) (xs : List Exp) :
    sourceDispatch loc next op acc ctx (.op actual xs) =
      (if fromOp actual == op && op != .noop then
        match checkOp ctx op loc (.op actual xs) with
        | some (.op _ [value, .call ticks (some _) args handler]) =>
          (true, .call ticks (some next) (args ++ [applyOp op (.var acc) value]) handler)
        | _ => (false, applyOp op (.var acc) (.op actual xs))
       else (false, applyOp op (.var acc) (.op actual xs))) := by
  cases guard : opEq op (.op actual xs) with
  | false =>
    have checked := checkOp_of_not_opEq ctx op loc (.op actual xs) guard
    have guard' : (fromOp actual == op && op != .noop) = false := by simpa [opEq_guard] using guard
    simp [sourceDispatch, checked, guard']
  | true =>
    have guard' : (fromOp actual == op && op != .noop) = true := by simpa [opEq_guard] using guard
    cases checked : checkOp ctx op loc (.op actual xs) with
    | none => simp [sourceDispatch, checked, guard']
    | some e =>
      obtain ⟨value, ticks, dest, args, he⟩ := checkOp_success_shape ctx op loc _ e checked
      subst e
      cases op <;> simp_all [sourceDispatch, opBinArgs, opEq, applyOp, getBinArgs,
        toOp, argsFrom, pushCall]

/-- Flapjack's fuel-free rewrite, with source-shaped scans and candidate checks.
The operation dispatch is the executable's normalized form. -/
def rewriteSingle (loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) : Exp → Bool × Exp
  | .var n => (false, .var n)
  | .force l n => (false, .force l n)
  | .ifThenElse cond yes no =>
    let ctx' := (scanSing ctx loc cond).1
    let (ry, y) := rewriteSingle loc next op acc ctx' yes
    let (rn, n) := rewriteSingle loc next op acc ctx' no
    let y := if ry then y else applyOp op (.var acc) yes
    let n := if rn then n else applyOp op (.var acc) no
    (ry || rn, .ifThenElse cond y n)
  | .let xs body =>
    let scans := scanList ctx loc xs
    let types := scans.map fun (_, ty, _, _) => ty
    let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
    let (r, body) := rewriteSingle loc next op (acc + xs.length) (types ++ last) body
    (r, .let xs body)
  | .tick x =>
    let (r, x) := rewriteSingle loc next op acc ctx x
    (r, .tick x)
  | .op actual xs =>
    if fromOp actual == op && op != .noop then
      match checkOp ctx op loc (.op actual xs) with
      | some (.op _ [value, .call ticks (some _) args handler]) =>
        (true, .call ticks (some next) (args ++ [applyOp op (.var acc) value]) handler)
      | _ => (false, applyOp op (.var acc) (.op actual xs))
    else (false, applyOp op (.var acc) (.op actual xs))
  | e => (false, applyOp op (.var acc) e)
termination_by e => sizeOf e

/-- Source rewrite after replacing singleton and list scans with their
source-defined single-expression and list counterparts. -/
def rewriteSource (loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) : Exp → Bool × Exp
  | .var n => (false, .var n)
  | .force l n => (false, .force l n)
  | .ifThenElse cond yes no =>
    let ctx' := (scanSing ctx loc cond).1
    let (ry, y) := rewriteSource loc next op acc ctx' yes
    let (rn, n) := rewriteSource loc next op acc ctx' no
    let y := if ry then y else applyOp op (.var acc) yes
    let n := if rn then n else applyOp op (.var acc) no
    (ry || rn, .ifThenElse cond y n)
  | .let xs body =>
    let scans := scanList ctx loc xs
    let types := scans.map fun (_, ty, _, _) => ty
    let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
    let (r, body) := rewriteSource loc next op (acc + xs.length) (types ++ last) body
    (r, .let xs body)
  | .tick x =>
    let (r, x) := rewriteSource loc next op acc ctx x
    (r, .tick x)
  | e => sourceDispatch loc next op acc ctx e
termination_by e => sizeOf e

/-- The executed rewrite normal form agrees with the source-shaped rewrite. -/
theorem rewriteSingle_eq_source (loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) (e : Exp) :
    rewriteSingle loc next op acc ctx e = rewriteSource loc next op acc ctx e := by
  cases e with
  | op actual xs =>
    rw [rewriteSingle.eq_def, rewriteSource.eq_def]
    dsimp only
    rw [sourceDispatch_op]
  | ifThenElse cond yes no =>
    rw [rewriteSingle.eq_def, rewriteSource.eq_def]
    dsimp only
    rw [rewriteSingle_eq_source loc next op acc _ yes, rewriteSingle_eq_source loc next op acc _ no]
  | «let» xs body =>
    rw [rewriteSingle.eq_def, rewriteSource.eq_def]
    dsimp only
    cases last : (scanList ctx loc xs).getLast? with
    | none =>
      rw [rewriteSingle_eq_source loc next op (acc + xs.length) _ body]
    | some s =>
      obtain ⟨a, b, c, d⟩ := s
      rw [rewriteSingle_eq_source loc next op (acc + xs.length) _ body]
  | tick body =>
    rw [rewriteSingle.eq_def, rewriteSource.eq_def]
    dsimp only
    rw [rewriteSingle_eq_source loc next op acc ctx body]
  | var n => rw [rewriteSingle.eq_def, rewriteSource.eq_def]
  | force l n => rw [rewriteSingle.eq_def, rewriteSource.eq_def]
  | raise e => cases op <;> simp [rewriteSingle.eq_def, rewriteSource.eq_def, sourceDispatch,
      checkOp, trySwap, opBinArgs, opEq]
  | call a b c d => cases op <;> simp [rewriteSingle.eq_def, rewriteSource.eq_def, sourceDispatch,
      checkOp, trySwap, opBinArgs, opEq]
  | «return» xs => cases op <;> simp [rewriteSingle.eq_def, rewriteSource.eq_def, sourceDispatch,
      checkOp, trySwap, opBinArgs, opEq]
  | letCall a b c d e => cases op <;> simp [rewriteSingle.eq_def, rewriteSource.eq_def, sourceDispatch,
      checkOp, trySwap, opBinArgs, opEq]
termination_by sizeOf e

/-- An operation rewrite uses the same candidate check as the fuel-free form. -/
theorem rewriteFuel_op_eq (fuel loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) (actual : ClosLang.Op) (xs : List Exp) :
    rewriteFuel (fuel + 1) loc next op acc ctx (.op actual xs) =
      some (rewriteSingle loc next op acc ctx (.op actual xs)) := by
  rw [rewriteFuel, rewriteSingle.eq_def]
  cases op <;> cases hop : fromOp actual <;>
    simp_all [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx, bne]
  all_goals
    have recognized : fromOp actual ≠ .noop := by rw [hop]; decide
    have checked := checkOpFuel_eq_recognized fuel ctx actual loc xs recognized
    simp only [hop] at checked
    rw [checked]
    simp only [Option.bind]
    split <;> simp_all

/-- Any successful bounded rewrite equals the fuel-free normal form. -/
theorem rewriteFuel_eq (fuel loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) (e : Exp) (result : Bool × Exp)
    (run : rewriteFuel fuel loc next op acc ctx e = some result) :
    result = rewriteSingle loc next op acc ctx e := by
  induction fuel generalizing acc ctx e result with
  | zero => simp [rewriteFuel] at run
  | succ fuel ih =>
    cases e with
    | op actual xs =>
      rw [rewriteFuel_op_eq] at run
      exact (Option.some.inj run).symm
    | ifThenElse cond yes no =>
      cases hy : rewriteFuel fuel loc next op acc (scanSing ctx loc cond).1 yes with
      | none => simp [rewriteFuel, scanBounded_eq, hy] at run
      | some y =>
        have yeq := ih acc _ yes y hy
        subst y
        cases hn : rewriteFuel fuel loc next op acc (scanSing ctx loc cond).1 no with
        | none => simp [rewriteFuel, scanBounded_eq, hy, hn] at run
        | some n =>
          have neq := ih acc _ no n hn
          subst n
          rw [rewriteSingle.eq_def]
          simpa [rewriteFuel, scanBounded_eq, hy, hn] using run.symm
    | «let» xs body =>
      simp only [rewriteFuel, scanListBounded_eq, bind, Option.bind, pure] at run
      generalize hb : rewriteFuel fuel loc next op (acc + xs.length) _ body = answer at run
      cases answer with
      | none => simp at run
      | some b =>
        have beq := ih (acc + xs.length) _ body b hb
        subst b
        rw [rewriteSingle.eq_def]
        cases last : (scanList ctx loc xs).getLast? with
        | none => simpa only [last, Option.bind, Option.some.injEq] using run.symm
        | some s =>
          obtain ⟨a, b, c, d⟩ := s
          simpa only [last, Option.bind, Option.some.injEq] using run.symm
    | tick body =>
      cases hb : rewriteFuel fuel loc next op acc ctx body with
      | none => simp [rewriteFuel, hb] at run
      | some b =>
        have beq := ih acc ctx body b hb
        subst b
        rw [rewriteSingle.eq_def]
        simpa [rewriteFuel, hb] using run.symm
    | var n => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | force l n => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | raise e => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | call a b c d => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | «return» xs => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm
    | letCall a b c d e => simpa [rewriteFuel, rewriteSingle.eq_def] using run.symm

/-- Flapjack's fuel-free expression compilation normal form. -/
def compileExpSingle (loc next arity : Nat) (e : Exp) : Option (Exp × Exp) :=
  match checkExpSingle loc arity e with
  | none => none
  | some op =>
    let worker := (rewriteSingle loc next op arity (List.replicate arity .any) e).2
    let wrapper := .let ((List.range arity).map .var ++ [identity op]) worker
    some (wrapper, worker)

/-- A successful expression compilation equals the fuel-free normal form. -/
theorem compileExpFuel_eq (fuel loc next arity : Nat) (e : Exp)
    (result : Option (Exp × Exp)) (run : compileExpFuel fuel loc next arity e = some result) :
    result = compileExpSingle loc next arity e := by
  cases decision : checkExpSingle loc arity e with
  | none => simpa [compileExpFuel, compileExpSingle, checkExpFuel_eq, decision] using run.symm
  | some op =>
    cases rewrite : rewriteFuel fuel loc next op arity (List.replicate arity .any) e with
    | none => simp [compileExpFuel, checkExpFuel_eq, decision, rewrite] at run
    | some output =>
      have eq := rewriteFuel_eq fuel loc next op arity (List.replicate arity .any) e output rewrite
      subst output
      simpa [compileExpFuel, compileExpSingle, checkExpFuel_eq, decision, rewrite] using run.symm

/-- The production retry returns the fuel-free expression compilation result. -/
theorem compileExpBounded_eq (fuel loc next arity : Nat) (e : Exp) :
    compileExpBounded fuel loc next arity e = some (compileExpSingle loc next arity e) := by
  cases first : compileExpFuel fuel loc next arity e with
  | some result =>
    have eq := compileExpFuel_eq fuel loc next arity e result first
    subst result
    simp [compileExpBounded, first]
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := compileExpFuel_succeeds (max fuel (expBudget e + 1)) loc next arity e bound
    have eq := compileExpFuel_eq _ loc next arity e result done
    subst result
    simp [compileExpBounded, first, done]

/-- The production expression compiler returns the source-shaped rewrite
when the single-expression candidate check selects an operator. -/
theorem compileExpBounded_eq_source (fuel loc next arity : Nat) (e : Exp) :
    compileExpBounded fuel loc next arity e = some
      (match checkExpSingle loc arity e with
       | none => none
       | some op =>
         let worker := (rewriteSource loc next op arity (List.replicate arity .any) e).2
         some (.let ((List.range arity).map .var ++ [identity op]) worker, worker)) := by
  rw [compileExpBounded_eq]
  unfold compileExpSingle
  cases checkExpSingle loc arity e with
  | none => rfl
  | some op =>
    dsimp only
    rw [rewriteSingle_eq_source]

end Flapjack.Compiler.Backend.BviTailrec
