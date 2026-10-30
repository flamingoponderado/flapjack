import Flapjack.Compiler.Backend.BvlToBvi.CompileOp
import Flapjack.Compiler.Backend.BvlToBvi.Budget
import Flapjack.Compiler.Backend.BviLet.SourceSing
import Flapjack.Misc.AppList
import Lean.Elab.Tactic.Omega

/-! Total source-shaped BVL-to-BVI expression conversion. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

private abbrev AuxTree := AppList (Nat × Nat × Bvi.Exp)

private theorem destLetBudget (exp : Bvl.Exp) :
    listBudget (destLet exp).1 ≤ expBudget exp ∧ expBudget (destLet exp).2 ≤ expBudget exp := by
  cases exp <;> simp [destLet, expBudget, listBudget] <;> omega

/-- Auxiliary code with the original `app_list` carrier. The source entry
point for let propagation equals `compileSing [] 0` by HOL's `compile_exp_eq`. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_aux_def"]
def compileAuxSource {α : Type} (input : Nat × α × Bvi.Exp) : AppList (Nat × α × Bvi.Exp) :=
  let (k, args, body) := input
  .list [(bvlNumStubs + bvlToBviNamespaces * k + 1, args, BviLet.compileSing [] 0 body)]

mutual
/-- Total source-shaped expression conversion. The executed retry agrees for
every initial fuel after flattening the auxiliary tree. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_exps_sing_def"]
def compileSingSource (n : Nat) : Bvl.Exp → Bvi.Exp × AuxTree × Nat
  | .var v => (.var v, .nil, n)
  | .force loc v => (.force (bvlNumStubs + bvlToBviNamespaces * loc) v, .nil, n)
  | .ifThenElse x y z =>
    let (x', a, n1) := compileSingSource n x
    let (y', b, n2) := compileSingSource n1 y
    let (z', c, n3) := compileSingSource n2 z
    (.ifThenElse x' y' z', smartAppend (smartAppend a b) c, n3)
  | .raise x =>
    let (x', aux, n1) := compileSingSource n x
    (.raise x', aux, n1)
  | .tick x =>
    let (x', aux, n1) := compileSingSource n x
    (.tick x', aux, n1)
  | .op op xs =>
    let (xs', aux, n1) := compileListSource n xs
    (compileOp op xs', aux, n1)
  | .call ticks dest xs =>
    let (xs', aux, n1) := compileListSource n xs
    (.call ticks (dest.map fun loc => bvlNumStubs + bvlToBviNamespaces * loc) xs' none, aux, n1)
  | .let xs body =>
    if xs.isEmpty then
      let args := (destLet body).1
      let inner := (destLet body).2
      let (args', a, n1) := compileListSource n args
      let (inner', b, n2) := compileSingSource n1 inner
      (.call 0 (some (bvlNumStubs + bvlToBviNamespaces * n2 + 1)) args' none,
        smartAppend (smartAppend a b) (compileAuxSource (n2, args.length, inner')), n2 + 1)
    else
      let (args, a, n1) := compileListSource n xs
      let (body', b, n2) := compileSingSource n1 body
      (.let args body', smartAppend a b, n2)
  | .handle body handler =>
    let args := (destLet body).1
    let inner := (destLet body).2
    let (args', a, n1) := compileListSource n args
    let (inner', b, n2) := compileSingSource n1 inner
    let (handler', c, n3) := compileSingSource n2 handler
    (.call 0 (some (bvlNumStubs + bvlToBviNamespaces * n3 + 1)) args' (some handler'),
      smartAppend (smartAppend (smartAppend a b) c) (compileAuxSource (n3, args.length, inner')), n3 + 1)
termination_by exp => expBudget exp
decreasing_by
  all_goals try simp only [expBudget]
  all_goals try (have := destLetBudget body)
  all_goals omega

/-- Total source-shaped traversal of an expression list. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_exps_sing_def"]
def compileListSource (n : Nat) : List Bvl.Exp → List Bvi.Exp × AuxTree × Nat
  | [] => ([], .nil, n)
  | x :: xs =>
    let (x', a, n1) := compileSingSource n x
    let (xs', b, n2) := compileListSource n1 xs
    (x' :: xs', smartAppend a b, n2)
termination_by xs => listBudget xs
decreasing_by all_goals simp only [listBudget] <;> omega
end

/-- List conversion produces one BVI expression per BVL expression. This
Flapjack consequence is needed to relate the auxiliary-code arity to the
executed compiler. -/
theorem compileListSource_length (n : Nat) (xs : List Bvl.Exp) :
    (compileListSource n xs).1.length = xs.length := by
  induction xs generalizing n with
  | nil => simp [compileListSource]
  | cons x xs ih =>
    cases hx : compileSingSource n x with
    | mk first rest =>
      cases rest with
      | mk aux next =>
        cases ht : compileListSource next xs with
        | mk compiled rest =>
          cases rest with
          | mk aux' final =>
            have length := ih next
            simp only [ht] at length
            simpa [compileListSource, hx, ht] using congrArg Nat.succ length

end Flapjack.Compiler.Backend.BvlToBvi
