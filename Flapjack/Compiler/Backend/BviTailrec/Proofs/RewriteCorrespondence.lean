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

/-- Extracting binary operands from a recognized accumulator operation
recovers its exact source operator and operands. -/
theorem opBinArgs_success_shape (assoc : AssocOp) (e x y : Exp)
    (run : opBinArgs assoc e = some (x, y)) :
    assoc ≠ .noop ∧ e = applyOp assoc x y := by
  unfold opBinArgs at run
  split at run
  next guard =>
    cases e with
    | op actual args =>
      cases args with
      | nil => simp [getBinArgs] at run
      | cons a rest =>
        cases rest with
        | nil => simp [getBinArgs] at run
        | cons b tail =>
          cases tail with
          | cons c cs => simp [getBinArgs] at run
          | nil =>
            simp [getBinArgs] at run
            obtain ⟨rfl, rfl⟩ := run
            have recognized : fromOp actual = assoc ∧ assoc ≠ .noop := by
              rw [opEq_guard] at guard
              cases assoc <;> cases actualFrom : fromOp actual <;>
                simp_all [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx, bne]
            have original := toOp_fromOp actual (by simpa [recognized.1] using recognized.2)
            rw [recognized.1] at original
            exact ⟨recognized.2, by simp [applyOp, original]⟩
    | _ => simp [getBinArgs] at run
  next => simp at run

/-- A successful candidate after operand normalization came either from the
original order or from swapping a commutative accumulator's operands. -/
theorem trySwap_success_shape (loc : Nat) (assoc : AssocOp) (e x y : Exp)
    (run : opBinArgs assoc (trySwap loc assoc e) = some (x, y)) :
    assoc ≠ .noop ∧
      (e = applyOp assoc x y ∨ (assoc ≠ .append ∧ e = applyOp assoc y x)) := by
  unfold trySwap at run
  split at run
  next =>
    obtain ⟨notNoop, shape⟩ := opBinArgs_success_shape assoc e x y run
    exact ⟨notNoop, Or.inl shape⟩
  next notAppend =>
    cases original : opBinArgs assoc e with
    | none => simp [original] at run
    | some pair =>
      obtain ⟨a, b⟩ := pair
      simp only [original] at run
      cases recursive : isRec loc a with
      | false =>
        simp only [recursive, Bool.false_eq_true, ↓reduceIte] at run
        obtain ⟨notNoop, shape⟩ := opBinArgs_success_shape assoc e x y run
        exact ⟨notNoop, Or.inl shape⟩
      | true =>
        simp only [recursive, ↓reduceIte] at run
        obtain ⟨notNoop, shape⟩ := opBinArgs_success_shape assoc e a b original
        obtain ⟨_, swapped⟩ := opBinArgs_success_shape assoc (applyOp assoc b a) x y run
        have operands : (b, a) = (x, y) := by
          have extracted := congrArg getBinArgs swapped
          simpa [applyOp, getBinArgs] using extracted
        cases operands
        have notList : assoc ≠ .append := by
          cases assoc <;> simp_all [BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx]
        exact ⟨notNoop, Or.inr ⟨notList, shape⟩⟩

/-- A successful candidate check identifies the recursive call and its pure
accumulator operand, and records whether the input operands were swapped.
The carriers remain untagged until source review is complete. -/
theorem checkOp_candidate (ctx : List ValueType) (assoc : AssocOp) (loc : Nat)
    (e checked : Exp) (run : checkOp ctx assoc loc e = some checked) :
    ∃ recursive pure,
      isRec loc recursive = true ∧ term ctx (opType assoc) pure = true ∧
      checked = applyOp assoc pure recursive ∧ assoc ≠ .noop ∧
      (e = applyOp assoc pure recursive ∨
        (assoc ≠ .append ∧ e = applyOp assoc recursive pure)) := by
  unfold checkOp at run
  cases selected : opBinArgs assoc (trySwap loc assoc e) with
  | none => simp [selected] at run
  | some pair =>
    obtain ⟨pure, recursive⟩ := pair
    simp only [selected] at run
    split at run
    next accepted =>
      simp only [Option.some.injEq] at run
      subst checked
      have facts : isRec loc recursive = true ∧ term ctx (opType assoc) pure = true := by
        simpa only [Bool.and_eq_true] using accepted
      obtain ⟨notNoop, shape⟩ := trySwap_success_shape loc assoc e pure recursive selected
      exact ⟨recursive, pure, facts.1, facts.2, rfl, notNoop, shape⟩
    next => simp at run

/-- A successful candidate uses a direct self-call without an exception
handler. -/
theorem checkOp_candidate_call (ctx : List ValueType) (assoc : AssocOp) (loc : Nat)
    (e checked : Exp) (run : checkOp ctx assoc loc e = some checked) :
    ∃ pure ticks args,
      term ctx (opType assoc) pure = true ∧
      checked = applyOp assoc pure (.call ticks (some loc) args none) ∧ assoc ≠ .noop ∧
      (e = applyOp assoc pure (.call ticks (some loc) args none) ∨
        (assoc ≠ .append ∧ e = applyOp assoc (.call ticks (some loc) args none) pure)) := by
  obtain ⟨recursive, pure, rec, termOk, shape, notNoop, original⟩ :=
    checkOp_candidate ctx assoc loc e checked run
  cases recursive <;> simp [isRec] at rec
  case call ticks dest args handler =>
    cases dest <;> cases handler <;> simp_all
    exact ⟨pure, termOk, ticks, args, rfl, original⟩

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

/-- Source-shaped rewrite using the original list-based scan. -/
def rewriteSource (loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) : Exp → Bool × Exp
  | .var n => (false, .var n)
  | .force l n => (false, .force l n)
  | .ifThenElse cond yes no =>
    let ctx' := ((scanExpr ctx loc [cond]).headD (ctx, .any, false, none)).1
    let (ry, y) := rewriteSource loc next op acc ctx' yes
    let (rn, n) := rewriteSource loc next op acc ctx' no
    let y := if ry then y else applyOp op (.var acc) yes
    let n := if rn then n else applyOp op (.var acc) no
    (ry || rn, .ifThenElse cond y n)
  | .let xs body =>
    let scans := scanExpr ctx loc xs
    let types := scans.map fun (_, ty, _, _) => ty
    let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
    let (r, body) := rewriteSource loc next op (acc + xs.length) (types ++ last) body
    (r, .let xs body)
  | .tick x =>
    let (r, x) := rewriteSource loc next op acc ctx x
    (r, .tick x)
  | e => sourceDispatch loc next op acc ctx e
termination_by e => sizeOf e

/-- A successful candidate is rewritten to a direct worker call with the
pure operand combined into the accumulator. -/
theorem checkOp_rewrite_worker (ctx : List ValueType) (assoc : AssocOp) (loc next acc : Nat)
    (e checked : Exp) (check : checkOp ctx assoc loc e = some checked) :
    ∃ pure ticks args,
      term ctx (opType assoc) pure = true ∧ assoc ≠ .noop ∧
      (e = applyOp assoc pure (.call ticks (some loc) args none) ∨
        (assoc ≠ .append ∧ e = applyOp assoc (.call ticks (some loc) args none) pure)) ∧
      rewriteSource loc next assoc acc ctx e =
        (true, .call ticks (some next) (args ++ [applyOp assoc (.var acc) pure]) none) := by
  obtain ⟨pure, ticks, args, termOk, checkedShape, notNoop, original⟩ :=
    checkOp_candidate_call ctx assoc loc e checked check
  have expressionShape : ∃ actual operands, e = .op actual operands := by
    rcases original with direct | ⟨_, swapped⟩
    · rw [direct]
      exact ⟨toOp assoc, _, rfl⟩
    · rw [swapped]
      exact ⟨toOp assoc, _, rfl⟩
  obtain ⟨actual, operands, rfl⟩ := expressionShape
  have guard : (fromOp actual == assoc && assoc != .noop) = true := by
    cases same : opEq assoc (.op actual operands) with
    | false =>
      have none := checkOp_of_not_opEq ctx assoc loc (.op actual operands) same
      rw [none] at check
      contradiction
    | true => simpa [opEq_guard] using same
  refine ⟨pure, ticks, args, termOk, notNoop, original, ?_⟩
  rw [rewriteSource.eq_def]
  dsimp only
  rw [sourceDispatch_op]
  simp [guard, check, checkedShape, applyOp]

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
    rw [scanExpr_single ctx loc cond]
    rw [rewriteSingle_eq_source loc next op acc _ yes, rewriteSingle_eq_source loc next op acc _ no]
    rfl
  | «let» xs body =>
    rw [rewriteSingle.eq_def, rewriteSource.eq_def]
    dsimp only
    rw [scanExpr_list ctx loc xs]
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
      (match checkExpOriginal loc arity e with
       | none => none
       | some op =>
         let worker := (rewriteSource loc next op arity (List.replicate arity .any) e).2
         some (.let ((List.range arity).map .var ++ [identity op]) worker, worker)) := by
  rw [compileExpBounded_eq]
  unfold compileExpSingle
  rw [checkExpOriginal_eq]
  cases checkExpSingle loc arity e with
  | none => rfl
  | some op =>
    dsimp only
    rw [rewriteSingle_eq_source]

/-- Source-shaped expression compilation, with the original list scan and
rewrite. -/
def compileExpSource (loc next arity : Nat) (e : Exp) : Option (Exp × Exp) :=
  match checkExpOriginal loc arity e with
  | none => none
  | some op =>
    let worker := (rewriteSource loc next op arity (List.replicate arity .any) e).2
    some (letWrap arity (identity op) worker, worker)

/-- Fuel-bounded expression compilation returns the source-shaped result. -/
theorem compileExpBounded_eq_compileExpSource (fuel loc next arity : Nat) (e : Exp) :
    compileExpBounded fuel loc next arity e = some (compileExpSource loc next arity e) := by
  simpa [compileExpSource, letWrap] using compileExpBounded_eq_source fuel loc next arity e

/-- Source-shaped function-list compilation in source order. -/
def compileEachSource : Nat → List (Nat × Nat × Exp) → Nat × List (Nat × Nat × Exp)
  | next, [] => (next, [])
  | next, (loc, arity, body) :: rest =>
    match compileExpSource loc next arity body with
    | none =>
      let (last, compiled) := compileEachSource next rest
      (last, (loc, arity, body) :: compiled)
    | some (wrapper, worker) =>
      let (last, compiled) := compileEachSource (next + Flapjack.bvlToBviNamespaces) rest
      (last, (loc, arity, wrapper) :: (next, arity + 1, worker) :: compiled)

/-- The executed function-list pass produces the source-shaped list and
allocates the same worker labels, independently of the supplied fuel. -/
theorem compileEachFuel_eq_source (fuel next : Nat) (code : List (Nat × Nat × Exp)) :
    compileEachFuel fuel next code = some (compileEachSource next code) := by
  induction code generalizing next with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases decision : compileExpSource loc next arity body with
    | none => simp [compileEachFuel, compileEachSource, compileExpBounded_eq_compileExpSource,
        decision, ih]
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      simp [compileEachFuel, compileEachSource, compileExpBounded_eq_compileExpSource,
        decision, ih]

/-- Source-shaped program pass, including the disabled case. -/
def compileProgSource (enabled : Bool) (next : Nat) (code : List (Nat × Nat × Exp)) :
    Nat × List (Nat × Nat × Exp) :=
  if enabled then compileEachSource next code else (next, code)

/-- The complete executed tail-recursion pass produces the source-shaped
program transformation. This is a compiler-function correspondence, not the
pass semantic correctness theorem. -/
theorem compileProgFuel_eq_source (fuel : Nat) (enabled : Bool) (next : Nat)
    (code : List (Nat × Nat × Exp)) :
    compileProgFuel fuel enabled next code = some (compileProgSource enabled next code) := by
  cases enabled <;> simp [compileProgFuel, compileProgSource, compileEachFuel_eq_source]

end Flapjack.Compiler.Backend.BviTailrec
