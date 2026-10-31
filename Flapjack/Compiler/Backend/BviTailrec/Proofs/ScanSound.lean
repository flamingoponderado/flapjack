import Flapjack.Compiler.Backend.BviTailrec.Proofs.Semantics

/-! Cases of the tail-recursion scan type-soundness invariant. The BVI
evaluator is not yet source-reviewed, so these supporting results are untagged. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi BvlSem

/-- Successful evaluation agrees with the contexts and result types inferred
by a source-shaped list scan. -/
def scanSound {C F : Type} (ctx : List ValueType) (loc : Nat) (xs : List Bvi.Exp) : Prop :=
  ∀ (env : List Value) (state next : BviSem.BviState C F) (values : List Value),
    tyRel env ctx → BviSem.evaluate xs env state = (.val values, next) →
      (∀ entry ∈ scanExpr ctx loc xs, tyRel env entry.1) ∧
        tyRel values ((scanExpr ctx loc xs).map fun (_, ty, _, _) => ty)

/-- Joining type facts cannot invalidate a value that satisfies the left
branch's type. -/
theorem valueMatchesType_decide_left (value : Value) (left right : ValueType)
    (typed : valueMatchesType value left) : valueMatchesType value (decideType left right) := by
  cases left <;> cases right <;> simp_all [valueMatchesType, decideType]

/-- Joining type facts cannot invalidate a value that satisfies the right
branch's type. -/
theorem valueMatchesType_decide_right (value : Value) (left right : ValueType)
    (typed : valueMatchesType value right) : valueMatchesType value (decideType left right) := by
  cases left <;> cases right <;> simp_all [valueMatchesType, decideType]

/-- The type selected for a conditional is sound for a value from either
branch, including the extra accumulator-type join. -/
theorem valueMatchesType_ifJoin (value : Value) (left right : ValueType) (op : Option AssocOp)
    (typed : valueMatchesType value left ∨ valueMatchesType value right) :
    valueMatchesType value (match op with
      | none => decideType left right
      | some a => decideType left (decideType right (opType a))) := by
  cases op with
  | none =>
    rcases typed with h | h
    · exact valueMatchesType_decide_left value left right h
    · exact valueMatchesType_decide_right value left right h
  | some a =>
    rcases typed with h | h
    · exact valueMatchesType_decide_left value left _ h
    · exact valueMatchesType_decide_right value left _ (valueMatchesType_decide_left value right _ h)

/-- The empty scan is sound for successful evaluation. -/
theorem scanSound_nil {C F : Type} (ctx : List ValueType) (loc : Nat) :
    scanSound (C := C) (F := F) ctx loc [] := by
  intro env state next values related run
  simp [BviSem.evaluate] at run
  obtain ⟨rfl, _⟩ := run
  simp [scanExpr.eq_def, tyRel]

/-- The variable case of scan soundness. -/
theorem scanSound_var {C F : Type} (ctx : List ValueType) (loc n : Nat) :
    scanSound (C := C) (F := F) ctx loc [.var n] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.var n) env state next values run
  exact scanExpr_var_sound ctx loc n env state next value related run

/-- A singleton scan that leaves the context unchanged and infers `any` is
sound for any successful BVI evaluation of that expression. -/
theorem scanSound_default {C F : Type} (ctx : List ValueType) (loc : Nat) (e : Bvi.Exp)
    (scan : scanSing ctx loc e = (ctx, .any, false, none)) :
    scanSound (C := C) (F := F) ctx loc [e] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton e env state next values run
  rw [scanExpr_single, scan]
  simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  exact ⟨related, by simp [tyRel]⟩

/-- Expressions whose scan has the source default result satisfy the scan
invariant whenever they evaluate successfully. -/
theorem scanSound_default_cases {C F : Type} (ctx : List ValueType) (loc : Nat) :
    (∀ e, scanSound (C := C) (F := F) ctx loc [.raise e]) ∧
    (∀ xs, scanSound (C := C) (F := F) ctx loc [.return xs]) ∧
    (∀ ticks dest args handler, scanSound (C := C) (F := F) ctx loc [.call ticks dest args handler]) ∧
    (∀ rets ticks dest args body, scanSound (C := C) (F := F) ctx loc [.letCall rets ticks dest args body]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> apply scanSound_default <;> rw [scanSing.eq_def]

/-- The tick case follows from soundness of the expression it evaluates. -/
theorem scanSound_tick {C F : Type} (ctx : List ValueType) (loc : Nat) (body : Bvi.Exp)
    (bodyIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [body]) :
    scanSound (C := C) (F := F) ctx loc [.tick body] := by
  intro env state next values related run
  by_cases clock : state.clock = 0
  · simp [BviSem.evaluate, clock] at run
  ·
    have bodyRun : BviSem.evaluate [body] env (BviSem.decClock 1 state) = (.val values, next) := by
      simpa [BviSem.evaluate, clock] using run
    have sound := bodyIH ctx env (BviSem.decClock 1 state) next values related bodyRun
    rw [scanExpr_single, scanSing.eq_def]
    simpa only [scanExpr_single] using sound

/-- Successful conditional evaluation first evaluates the condition and then
exactly one branch. -/
theorem evaluateIf_success {C F : Type} (condition yes no : Bvi.Exp) (env : List Value)
    (state next : BviSem.BviState C F) (values : List Value)
    (run : BviSem.evaluate [.ifThenElse condition yes no] env state = (.val values, next)) :
    ∃ value middle, BviSem.evaluate [condition] env state = (.val [value], middle) ∧
      ((asBool value = some true ∧ BviSem.evaluate [yes] env middle = (.val values, next)) ∨
       (asBool value = some false ∧ BviSem.evaluate [no] env middle = (.val values, next))) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  cases hcond : BviSem.evaluate [condition] env state with
  | mk result middle =>
    cases result with
    | err error => simp [hcond] at run
    | val vs =>
      obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton condition env state middle vs hcond
      simp only [hcond] at run
      change (match asBool value with
        | none => (.err (.abort .typeError), middle)
        | some true => BviSem.evaluate [yes] env middle
        | some false => BviSem.evaluate [no] env middle) = (.val values, next) at run
      cases test : asBool value with
      | none => simp [test] at run
      | some choice =>
        cases choice with
        | false =>
          refine ⟨value, middle, rfl, Or.inr ⟨test, ?_⟩⟩
          simpa [test] using run
        | true =>
          refine ⟨value, middle, rfl, Or.inl ⟨test, ?_⟩⟩
          simpa [test] using run

/-- The conditional scan is sound when the condition and both branches
satisfy the source induction hypotheses. -/
theorem scanSound_if {C F : Type} (ctx : List ValueType) (loc : Nat) (condition yes no : Bvi.Exp)
    (condIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [condition])
    (yesIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [yes])
    (noIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [no]) :
    scanSound (C := C) (F := F) ctx loc [.ifThenElse condition yes no] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.ifThenElse condition yes no) env state next values run
  obtain ⟨condValue, middle, condRun, branch⟩ := evaluateIf_success condition yes no env state next [value] run
  have condSound := condIH ctx env state middle [condValue] related condRun
  simp only [scanExpr_single, List.mem_singleton, forall_eq, List.map_cons, List.map_nil] at condSound
  let ci := (scanSing ctx loc condition).1
  let y := scanSing ci loc yes
  let n := scanSing ci loc no
  have branchSound : (tyRel env y.1 ∧ valueMatchesType value y.2.1) ∨
      (tyRel env n.1 ∧ valueMatchesType value n.2.1) := by
    rcases branch with ⟨_, yesRun⟩ | ⟨_, noRun⟩
    · have sound := yesIH ci env middle next [value] condSound.1 yesRun
      simp only [scanExpr_single, List.mem_singleton, forall_eq, List.map_cons, List.map_nil] at sound
      left
      exact ⟨sound.1, by simpa [tyRel, valueMatchesType] using sound.2⟩
    · have sound := noIH ci env middle next [value] condSound.1 noRun
      simp only [scanExpr_single, List.mem_singleton, forall_eq, List.map_cons, List.map_nil] at sound
      right
      exact ⟨sound.1, by simpa [tyRel, valueMatchesType] using sound.2⟩
  have sameLength : y.1.length = n.1.length :=
    (scanSing_context_length ci loc yes).trans (scanSing_context_length ci loc no).symm
  have merged := tyRel_decideType y.1 n.1 env ⟨branchSound.imp And.left And.left, sameLength⟩
  have typed := valueMatchesType_ifJoin value y.2.1 n.2.1 (y.2.2.2.orElse fun _ => n.2.2.2)
    (branchSound.imp And.right And.right)
  rw [scanExpr_single, scanSing.eq_def]
  dsimp only
  simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  exact ⟨merged, .cons typed .nil⟩

/-- Successful local-binding evaluation first evaluates the binding list and
then the body in the extended environment. -/
theorem evaluateLet_success {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp) (env : List Value)
    (state next : BviSem.BviState C F) (values : List Value)
    (run : BviSem.evaluate [.let bindings body] env state = (.val values, next)) :
    ∃ bound middle, BviSem.evaluate bindings env state = (.val bound, middle) ∧
      BviSem.evaluate [body] (bound ++ env) middle = (.val values, next) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  cases hbind : BviSem.evaluate bindings env state with
  | mk result middle =>
    cases result with
    | err error => simp [hbind] at run
    | val bound =>
      refine ⟨bound, middle, rfl, ?_⟩
      simpa [hbind] using run

/-- Removing the bound-value prefix from a related extended context leaves
the outer environment and its corresponding context related. -/
theorem tyRel_drop_prefix (bound env : List Value) (types : List ValueType)
    (h : tyRel (bound ++ env) types) : tyRel env (types.drop bound.length) := by
  have dropped := List.forall₂_drop bound.length h
  simpa only [tyRel, List.drop_append_length] using dropped

/-- The local-binding scan is sound when the bindings and body satisfy their
source induction hypotheses. -/
theorem scanSound_let {C F : Type} (ctx : List ValueType) (loc : Nat)
    (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (bindingsIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc bindings)
    (bodyIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [body]) :
    scanSound (C := C) (F := F) ctx loc [.let bindings body] := by
  intro env state next values related run
  obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton (.let bindings body) env state next values run
  obtain ⟨bound, middle, bindRun, bodyRun⟩ := evaluateLet_success bindings body env state next [value] run
  have bindSound := bindingsIH ctx env state middle bound related bindRun
  rw [scanExpr_list] at bindSound
  let scans := scanList ctx loc bindings
  let types := scans.map fun (_, ty, _, _) => ty
  let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
  have lastSound : tyRel env last := by
    cases hlast : scans.getLast? with
    | none => simpa [last, hlast] using related
    | some entry =>
      have sound := bindSound.1 entry (List.mem_of_getLast? hlast)
      obtain ⟨a, b, c, d⟩ := entry
      simpa [last, hlast] using sound
  have extended : tyRel (bound ++ env) (types ++ last) :=
    tyRel_append env last types bound ⟨lastSound, bindSound.2⟩
  have bodySound := bodyIH (types ++ last) (bound ++ env) middle next [value] extended bodyRun
  simp only [scanExpr_single, List.mem_singleton, forall_eq, List.map_cons, List.map_nil] at bodySound
  have dropped := tyRel_drop_prefix bound env (scanSing (types ++ last) loc body).1 bodySound.1
  have boundLength : bound.length = scans.length := by
    rw [BviSem.evaluate_length bindings env state middle bound bindRun]
    exact (scanList_length ctx loc bindings).symm
  rw [boundLength] at dropped
  rw [scanExpr_single, scanSing.eq_def]
  dsimp only
  simp only [List.mem_singleton, forall_eq, List.map_cons, List.map_nil]
  exact ⟨dropped, bodySound.2⟩

/-- Sequential evaluation and context threading preserve scan soundness,
assuming the corresponding induction hypotheses for head and tail. -/
theorem scanSound_cons {C F : Type} (ctx : List ValueType) (loc : Nat) (x : Bvi.Exp) (xs : List Bvi.Exp)
    (headIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc [x])
    (tailIH : ∀ ctx, scanSound (C := C) (F := F) ctx loc xs) :
    scanSound (C := C) (F := F) ctx loc (x :: xs) := by
  intro env state next values related run
  change BviSem.evaluateTuple (x :: xs, env, state) = _ at run
  rw [BviSem.evaluateCons] at run
  cases first : BviSem.evaluate [x] env state with
  | mk result middle =>
    cases result with
    | err error => simp [BviSem.evaluateTuple, first] at run
    | val headValues =>
      obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton x env state middle headValues first
      cases rest : BviSem.evaluate xs env middle with
      | mk tailResult last =>
        cases tailResult with
        | err error => simp [BviSem.evaluateTuple, first, rest] at run
        | val tailValues =>
          simp only [BviSem.evaluateTuple, first, rest, Flapjack.holHd,
            Prod.mk.injEq, SemanticPrimitivesHOL.Result.val.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have headSound := headIH ctx env state middle [value] related first
          simp only [scanExpr_single, List.mem_singleton, forall_eq,
            List.map_cons, List.map_nil] at headSound
          have tailSound := tailIH (scanSing ctx loc x).1 env middle last tailValues headSound.1 rest
          rw [scanExpr_list, scanList.eq_def]
          dsimp only
          rw [← scanExpr_list]
          constructor
          · intro entry mem
            simp only [List.mem_cons] at mem
            rcases mem with rfl | mem
            · exact headSound.1
            · exact tailSound.1 entry mem
          · cases headSound.2 with
            | cons valueSound empty =>
              exact List.Forall₂.cons valueSound tailSound.2

end Flapjack.Compiler.Backend.BviTailrec
