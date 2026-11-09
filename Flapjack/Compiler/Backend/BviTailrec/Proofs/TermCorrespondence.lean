import Flapjack.Compiler.Backend.BviTailrec.Proofs.TermTotal

/-! Agreement of bounded term analysis with the original total tests. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

private theorem optionAnd_sound (first second : Option Bool) (x y result : Bool)
    (firstSound : ∀ b, first = some b → b = x)
    (secondSound : ∀ b, second = some b → b = y)
    (run : (do let b ← first; if !b then pure false else second) = some result) :
    result = (x && y) := by
  cases first with
  | none => simp at run
  | some b =>
    have bx := firstSound b rfl
    cases b with
    | false => simp_all
    | true =>
      cases second with
      | none => simp at run
      | some c =>
        have cy := secondSound c rfl
        simp_all

private theorem termAny_binary_other (fuel : Nat) (ctx : List ValueType) (list : Bool)
    (op : ClosLang.Op) (x y : Exp)
    (notAppend : op ≠ .blockOp .listAppend) (notCons : op ≠ .blockOp (.cons 0)) :
    termAnyFuel (fuel + 1) ctx list (.op op [x, y]) =
      if !list && (isArith op || isRel op) then
        (do let b ← termIntFuel fuel ctx x; if !b then pure false else termIntFuel fuel ctx y)
      else some false := by
  cases op <;> try rfl
  case blockOp block =>
    cases block <;> try rfl
    case cons tag => cases tag <;> simp_all [termAnyFuel, isArith, isRel]
    case listAppend => simp_all

private theorem termAny_total_binary_other (ctx : List ValueType) (list : Bool)
    (op : ClosLang.Op) (x y : Exp)
    (notAppend : op ≠ .blockOp .listAppend) (notCons : op ≠ .blockOp (.cons 0)) :
    termAny ctx list (.op op [x, y]) =
      (!list && (isArith op || isRel op) && termInt ctx x && termInt ctx y) := by
  cases op <;> simp_all [termAny]

/-- Every successful fuel-bounded term analysis agrees with the
corresponding total source test. -/
theorem termFuel_correspondence (fuel : Nat) :
    (∀ ctx expression result, termIntFuel fuel ctx expression = some result → result = termInt ctx expression) ∧
    (∀ ctx list expression result, termAnyFuel fuel ctx list expression = some result → result = termAny ctx list expression) := by
  induction fuel with
  | zero =>
    constructor <;> intros <;> simp_all [termIntFuel, termAnyFuel]
  | succ fuel ih =>
    constructor
    · intro ctx expression result run
      cases expression with
      | op op args =>
        cases args with
        | nil => simpa [termIntFuel, termInt] using run.symm
        | cons x xs =>
          cases xs with
          | nil => simpa [termIntFuel, termInt] using run.symm
          | cons y ys =>
            cases ys with
            | cons z zs => simpa [termIntFuel, termInt] using run.symm
            | nil =>
              by_cases arith : isArith op = true
              · have pairRun : (do let b ← termIntFuel fuel ctx x; if !b then pure false else termIntFuel fuel ctx y) = some result := by
                  simpa [termIntFuel, arith] using run
                have pairEq := optionAnd_sound (termIntFuel fuel ctx x) (termIntFuel fuel ctx y)
                  (termInt ctx x) (termInt ctx y) result (ih.1 ctx x) (ih.1 ctx y) pairRun
                simpa [termInt, arith] using pairEq
              · have arithFalse : isArith op = false := by cases h : isArith op <;> simp_all
                simpa [termIntFuel, termInt, arithFalse] using run.symm
      | _ => simpa [termIntFuel, termInt] using run.symm
    · intro ctx list expression result run
      cases expression with
      | op op args =>
        cases args with
        | nil =>
          cases op <;> try (simpa [termAnyFuel, termAny] using run.symm)
          case blockOp bop =>
            cases bop <;> try (simpa [termAnyFuel, termAny] using run.symm)
            case cons tag => cases tag <;> simpa [termAnyFuel, termAny] using run.symm
        | cons x xs =>
          cases xs with
          | nil => simpa [termAnyFuel, termAny] using run.symm
          | cons y ys =>
            cases ys with
            | cons z zs => simpa [termAnyFuel, termAny] using run.symm
            | nil =>
              by_cases append : op = .blockOp .listAppend
              · subst op
                have pairRun : (do let b ← termAnyFuel fuel ctx true x; if !b then pure false else termAnyFuel fuel ctx true y) = some result := by
                  simpa [termAnyFuel] using run
                have pairEq := optionAnd_sound (termAnyFuel fuel ctx true x) (termAnyFuel fuel ctx true y)
                  (termAny ctx true x) (termAny ctx true y) result (ih.2 ctx true x) (ih.2 ctx true y) pairRun
                simpa [termAny] using pairEq
              · by_cases cons : op = .blockOp (.cons 0)
                · subst op
                  have pairRun : (do let b ← termAnyFuel fuel ctx true x; if !b then pure false else termAnyFuel fuel ctx false y) = some result := by
                    simpa [termAnyFuel] using run
                  have pairEq := optionAnd_sound (termAnyFuel fuel ctx true x) (termAnyFuel fuel ctx false y)
                    (termAny ctx true x) (termAny ctx false y) result (ih.2 ctx true x) (ih.2 ctx false y) pairRun
                  simpa [termAny] using pairEq
                · rw [termAny_binary_other fuel ctx list op x y append cons] at run
                  rw [termAny_total_binary_other ctx list op x y append cons]
                  by_cases enabled : (!list && (isArith op || isRel op)) = true
                  · simp only [enabled, ↓reduceIte] at run
                    have pairEq := optionAnd_sound (termIntFuel fuel ctx x) (termIntFuel fuel ctx y)
                      (termInt ctx x) (termInt ctx y) result (ih.1 ctx x) (ih.1 ctx y) run
                    simpa [enabled] using pairEq
                  · have disabled : (!list && (isArith op || isRel op)) = false := by
                      cases h : (!list && (isArith op || isRel op)) <;> simp_all
                    simpa [disabled] using run.symm
      | _ => simpa [termAnyFuel, termAny] using run.symm

/-- A successful dispatched term test returns the source result. -/
theorem termFuel_eq (fuel : Nat) (ctx : List ValueType) (ty : ValueType)
    (expression : Exp) (result : Bool) (run : termFuel fuel ctx ty expression = some result) :
    result = term ctx ty expression := by
  cases ty with
  | int => exact (termFuel_correspondence fuel).1 ctx expression result run
  | list => exact (termFuel_correspondence fuel).2 ctx true expression result run
  | any => exact (termFuel_correspondence fuel).2 ctx false expression result run

/-- The production retry returns the same answer as the source term test
for every initial fuel value. -/
theorem termBounded_eq (fuel : Nat) (ctx : List ValueType) (ty : ValueType) (expression : Exp) :
    termBounded fuel ctx ty expression = some (term ctx ty expression) := by
  obtain ⟨result, run⟩ := termBounded_succeeds fuel ctx ty expression
  have same : result = term ctx ty expression := by
    cases first : termFuel fuel ctx ty expression with
    | some initial =>
      have initialEq : initial = result := by simpa [termBounded, first] using run
      subst result
      exact termFuel_eq fuel ctx ty expression initial first
    | none =>
      have retry : termFuel (max fuel (expBudget expression + 1)) ctx ty expression = some result := by
        simpa [termBounded, first] using run
      exact termFuel_eq _ ctx ty expression result retry
  simpa [same] using run

/-- For a real accumulator operator, production candidate checking returns
the original CakeML result on the corresponding BVI operation. -/
theorem checkOpFuel_eq (fuel : Nat) (ctx : List ValueType) (assoc : AssocOp)
    (loc : Nat) (args : List Exp) (notNoop : assoc ≠ .noop) :
    checkOpFuel fuel ctx assoc loc args = some (checkOp ctx assoc loc (.op (toOp assoc) args)) := by
  cases args with
  | nil => cases assoc <;> simp_all [checkOpFuel, checkOp, trySwap, opBinArgs, opEq, getBinArgs, toOp]
  | cons x xs =>
    cases xs with
    | nil => cases assoc <;> simp_all [checkOpFuel, checkOp, trySwap, opBinArgs, opEq, getBinArgs, toOp]
    | cons y ys =>
      cases ys with
      | cons z zs => cases assoc <;> simp_all [checkOpFuel, checkOp, trySwap, opBinArgs, opEq, getBinArgs, toOp]
      | nil =>
        cases assoc <;> try contradiction
        all_goals cases hx : isRec loc x <;> cases hy : isRec loc y <;>
          simp [checkOpFuel, checkOp, trySwap, opBinArgs, opEq, getBinArgs,
            toOp, applyOp, termBounded_eq, hx, hy, BEq.beq, instBEqAssocOp.beq, AssocOp.ctorIdx, bne]
        all_goals split <;> rfl

end Flapjack.Compiler.Backend.BviTailrec
