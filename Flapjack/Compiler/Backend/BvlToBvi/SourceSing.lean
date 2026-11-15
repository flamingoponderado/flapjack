module

public import Flapjack.Compiler.Backend.BvlToBvi.CompileOp
public import Flapjack.Compiler.Backend.BvlToBvi.Budget
public import Flapjack.Compiler.Backend.BviLet.SourceList
public import Flapjack.Misc.AppList
public import Flapjack.Misc.ListEl
public import Lean.Elab.Tactic.Omega

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Total source-shaped BVL-to-BVI expression conversion. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

private abbrev AuxTree := AppList (Nat × Nat × Bvi.Exp)

private theorem destLetBudget (exp : Bvl.Exp) :
    listBudget (destLet exp).1 ≤ expBudget exp ∧ expBudget (destLet exp).2 ≤ expBudget exp := by
  cases exp <;> simp [destLet, expBudget, listBudget] <;> omega

/-- Auxiliary code with the original `app_list` carrier and let-optimizer entry point. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_aux_def"]
def compileAuxSource {α : Type} (input : Nat × α × Bvi.Exp) : AppList (Nat × α × Bvi.Exp) :=
  let (k, args, body) := input
  .list [(bvlNumStubs + bvlToBviNamespaces * k + 1, args, BviLet.compileExp body)]

/-- The original list-recursive BVL-to-BVI compiler, including HOL head selection. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_exps_def"]
noncomputable def compileExpsSource (n : Nat) : List Bvl.Exp → List Bvi.Exp × AppList (Nat × Nat × Bvi.Exp) × Nat
  | [] => ([], .nil, n)
  | x :: y :: xs =>
    let (c1, a1, n1) := compileExpsSource n [x]
    let (c2, a2, n2) := compileExpsSource n1 (y :: xs)
    (c1 ++ c2, smartAppend a1 a2, n2)
  | [.var v] => ([.var v], .nil, n)
  | [.ifThenElse x y z] =>
    let (c1, a1, n1) := compileExpsSource n [x]
    let (c2, a2, n2) := compileExpsSource n1 [y]
    let (c3, a3, n3) := compileExpsSource n2 [z]
    ([.ifThenElse (@Flapjack.holHd Bvi.Exp ⟨.var 0⟩ c1) (@Flapjack.holHd Bvi.Exp ⟨.var 0⟩ c2)
      (@Flapjack.holHd Bvi.Exp ⟨.var 0⟩ c3)], smartAppend (smartAppend a1 a2) a3, n3)
  | [.let xs body] =>
    if xs.isEmpty then
      let args := (destLet body).1
      let inner := (destLet body).2
      let (c1, a1, n1) := compileExpsSource n args
      let (c2, a2, n2) := compileExpsSource n1 [inner]
      ([.call 0 (some (bvlNumStubs + bvlToBviNamespaces * n2 + 1)) c1 none],
       smartAppend (smartAppend a1 a2) (compileAuxSource (n2, args.length, @Flapjack.holHd Bvi.Exp ⟨.var 0⟩ c2)), n2 + 1)
    else
      let (c1, a1, n1) := compileExpsSource n xs
      let (c2, a2, n2) := compileExpsSource n1 [body]
      ([.let c1 (@Flapjack.holHd Bvi.Exp ⟨.var 0⟩ c2)], smartAppend a1 a2, n2)
  | [.raise x] =>
    let (c1, a1, n1) := compileExpsSource n [x]
    ([.raise (@Flapjack.holHd Bvi.Exp ⟨.var 0⟩ c1)], a1, n1)
  | [.tick x] =>
    let (c1, a1, n1) := compileExpsSource n [x]
    ([.tick (@Flapjack.holHd Bvi.Exp ⟨.var 0⟩ c1)], a1, n1)
  | [.force loc v] => ([.force (bvlNumStubs + bvlToBviNamespaces * loc) v], .nil, n)
  | [.op op xs] =>
    let (c1, a1, n1) := compileExpsSource n xs
    ([compileOp op c1], a1, n1)
  | [.handle body handler] =>
    let args := (destLet body).1
    let inner := (destLet body).2
    let (c1, a1, n1) := compileExpsSource n args
    let (c2, a2, n2) := compileExpsSource n1 [inner]
    let (c3, a3, n3) := compileExpsSource n2 [handler]
    let aux4 := compileAuxSource (n3, args.length, @Flapjack.holHd Bvi.Exp ⟨.var 0⟩ c2)
    ([.call 0 (some (bvlNumStubs + bvlToBviNamespaces * n3 + 1)) c1
       (some (@Flapjack.holHd Bvi.Exp ⟨.var 0⟩ c3))],
     smartAppend (smartAppend (smartAppend a1 a2) a3) aux4, n3 + 1)
  | [.call ticks dest xs] =>
    let (c1, a1, n1) := compileExpsSource n xs
    ([.call ticks (dest.map fun loc => bvlNumStubs + bvlToBviNamespaces * loc) c1 none], a1, n1)
termination_by xs => listBudget xs
decreasing_by
  all_goals simp only [listBudget, expBudget]
  all_goals try (have := destLetBudget body)
  all_goals try (have := destLetBudget x)
  all_goals try (have positive : 0 < expBudget y := by cases y <;> simp [expBudget] <;> omega)
  all_goals omega

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

/-- The original recursive compiler agrees with the singleton/list implementation. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_exps_sing"]
theorem compileExpsSing :
    (∀ n e, compileExpsSource n [e] =
      let (x, y, z) := compileSingSource n e; ([x], y, z)) ∧
    (∀ n es, compileListSource n es = compileExpsSource n es) := by
  apply compileSingSource.mutual_induct <;>
    intros <;>
    simp_all [compileExpsSource, compileSingSource, compileListSource, Flapjack.holHd, smartAppend]
  all_goals try simp_all (config := { zetaDelta := true })
  case case12 =>
    rename_i n x xs a b c d e f g h j k
    cases xs with
    | nil =>
      simp only [compileExpsSource, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rw [j]
      cases b <;> rfl
    | cons y ys =>
      rw [compileExpsSource, j]
      simp only
      rw [h]
      rfl

/-- The original compiler agrees with the optimized list traversal. This
Flapjack helper selects the second conjunct of the source equivalence. -/
theorem compileExpsSource_eq_list (n : Nat) (xs : List Bvl.Exp) :
    compileExpsSource n xs = compileListSource n xs := (compileExpsSing.2 n xs).symm

/-- List compilation produces one BVI expression per BVL expression. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_exps_LENGTH_lemma"]
theorem compileListSource_length (n : Nat) (xs : List Bvl.Exp) :
    (compileExpsSource n xs).1.length = xs.length := by
  rw [compileExpsSource_eq_list]
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

/-- A compilation result has the same number of input and output expressions. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_exps_LENGTH"]
theorem compileListSource_length_result (n : Nat) (xs : List Bvl.Exp) (ys : List Bvi.Exp)
    (aux : AppList (Nat × Nat × Bvi.Exp)) (n1 : Nat)
    (compiled : compileExpsSource n xs = (ys, aux, n1)) : ys.length = xs.length := by
  have length := compileListSource_length n xs
  simpa [compiled] using length

/-- Compiling one expression produces exactly one BVI expression. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_exps_SING"]
theorem compileListSource_singleton_result (n : Nat) (x : Bvl.Exp) (c : List Bvi.Exp)
    (aux : AppList (Nat × Nat × Bvi.Exp)) (n1 : Nat)
    (compiled : compileExpsSource n [x] = (c, aux, n1)) : ∃ y, c = [y] := by
  have length := compileListSource_length_result n [x] c aux n1 compiled
  cases c with
  | nil => simp at length
  | cons first rest =>
    cases rest with
    | nil => exact ⟨first, rfl⟩
    | cons second rest => simp at length

end Flapjack.Compiler.Backend.BvlToBvi
