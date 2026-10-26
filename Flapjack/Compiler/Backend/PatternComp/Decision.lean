import Flapjack.Compiler.Backend.PatternSemantics
import Flapjack.Compiler.Backend.PatternExh.Weights

/-! Decision-tree construction in CakeML's pattern compiler. The exhaustiveness
analysis used by `comp` is a separate, not-yet-ported prerequisite. -/
namespace Flapjack.Compiler.Backend.PatternComp
open PatternCommon PatternSemantics

/-- Test whether a row is a nullary constructor pattern. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "is_const_row_def"]
def isConstRow {α : Type} : Pat × α → Bool
  | (.cons _ ps, _) => ps.isEmpty
  | _ => false

/-- Determine whether a pattern or one of its alternatives is `Any`. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "is_Any_def"]
def isAny : Pat → Bool
  | .any => true
  | .or a b => isAny a || isAny b
  | _ => false

/-- Test for a top-level alternative pattern in a row. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "is_Or_row_def"]
def isOrRow {α : Type} : Pat × α → Bool
  | (.or _ _, _) => true
  | _ => false

/-- Keep rows up to and including the first unconditional pattern. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "take_until_Any_def"]
def takeUntilAny {α : Type} : List (Pat × α) → List (Pat × α)
  | [] => []
  | (p, x) :: xs => if isAny p then [(p, x)] else (p, x) :: takeUntilAny xs

/-- Move nullary constructor patterns first only for short rows without `Or`. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "move_const_up_def"]
def moveConstUp {α : Type} (rows : List (Pat × α)) : List (Pat × α) :=
  let rs := takeUntilAny rows
  if 5 ≤ rs.length || rs.any isOrRow then rs
  else rs.filter isConstRow ++ rs.filter (fun row => !isConstRow row)

/-- Replace the last row's pattern with `Any`. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "insert_Any_def"]
def insertAny {α : Type} : List (Pat × α) → List (Pat × α)
  | [] => []
  | [(_, x)] => [(.any, x)]
  | x :: y :: xs => x :: insertAny (y :: xs)

/-- Test whether a decision guard is the literal true guard. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "is_True_def"]
def isTrue : DGuard → Bool
  | .true_ => true
  | _ => false

/-- Simplifying disjunction used during pattern compilation. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "mk_Disj_def"]
def mkDisj (p q : DGuard) : DGuard :=
  if isTrue p || isTrue q then .true_ else .disj p q

/-- Simplifying conjunction used during pattern compilation. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "mk_Conj_def"]
def mkConj (p q : DGuard) : DGuard :=
  if isTrue p then q else if isTrue q then p else .conj p q

/-- Eliminate a decision-tree conditional whose guard is true. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "mk_If_def"]
def mkIf (g : DGuard) (p q : DTree) : DTree :=
  if isTrue g then p else .if_ g p q

/-- Turn a list of indices into a nested decision-tree position. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "get_pos_def"]
def getPos : List Nat → Position
  | [] => .emptyPos
  | n :: ns => .pos n (getPos ns)

mutual
/-- Produce the source decision guard for a pattern and reversed path. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "pat_to_guard_def"]
def patToGuard (path : List Nat) : Pat → DGuard
  | .any => .true_
  | .lit l => .posTest (getPos path.reverse) (.litEq l)
  | .cons none ps => patsToGuard path 0 ps
  | .cons (some (tag, _)) ps =>
      mkConj (.posTest (getPos path.reverse) (.tagLenEq tag ps.length))
        (patsToGuard path 0 ps)
  | .or p q => mkDisj (patToGuard path p) (patToGuard path q)
  | .ref p => patToGuard (0 :: path) p

/-- Guard clauses for consecutive constructor arguments. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "pat_to_guard_def"]
def patsToGuard (path : List Nat) (k : Nat) : List Pat → DGuard
  | [] => .true_
  | [p] => patToGuard (k :: path) p
  | p :: q :: ps => mkConj (patToGuard (k :: path) p) (patsToGuard path (k + 1) (q :: ps))
end

/-- Convert ordered rows into a decision tree with `Fail` as the final leaf. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "pats_to_code_def"]
def patsToCode : List (Pat × Nat) → DTree
  | [] => .fail
  | (p, x) :: rows => mkIf (patToGuard [] p) (.leaf x) (patsToCode rows)

/-- Execute pattern compilation with an explicit exhaustiveness budget.
`none` means the budget was exhausted; proving a total bound and porting
the original `comp` remain open. -/
def compFuel (fuel : Nat) (rows : List (Pat × Nat)) : Option DTree := do
  let rows0 := moveConstUp rows
  let exhaustive ← PatternExh.exhRowsFuel fuel rows0
  pure (patsToCode (if exhaustive then insertAny rows0 else rows0))

end Flapjack.Compiler.Backend.PatternComp
