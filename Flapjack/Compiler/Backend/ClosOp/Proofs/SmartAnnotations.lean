module

public import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartReduction
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! Source smart-operation annotation and syntactic invariants. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosProps

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem someAppend (xs ys : List Exp) :
    everyFnLocationSome (xs ++ ys) ↔ everyFnLocationSome xs ∧ everyFnLocationSome ys := by
  induction xs with
  | nil => simp [everyFnLocationSome]
  | cons x xs ih => simp [everyFnLocationSome, ih, and_assoc]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem noneAppend (xs ys : List Exp) :
    everyFnVarsNone (xs ++ ys) ↔ everyFnVarsNone xs ∧ everyFnVarsNone ys := by
  induction xs with
  | nil => simp [everyFnVarsNone]
  | cons x xs ih => simp [everyFnVarsNone, ih, and_assoc]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem redSome (xs ys : List Exp) (h : RedRel xs ys) :
    everyFnLocationSome xs ↔ everyFnLocationSome ys := by
  induction h with
  | op n xs ys t op iop i tag t1 t2 s w hr hm ih =>
    simp [everyFnLocationSome, fnLocationSomeExp, ih]
  | nil => rfl
  | refl x => rfl
  | var v t => simp [everyFnLocationSome, fnLocationSomeExp]
  | multi x y zs x1 x2 hx hy ihx ihy =>
    simp_all [everyFnLocationSome, someAppend]
  | letE xs x x1 t hx hy ihx ihy =>
    simp_all [everyFnLocationSome, fnLocationSomeExp]
  | ite t x y z x1 x2 x3 hx hy hz ihx ihy ihz =>
    simp_all [everyFnLocationSome, fnLocationSomeExp, someAppend]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem redNone (xs ys : List Exp) (h : RedRel xs ys) :
    everyFnVarsNone xs ↔ everyFnVarsNone ys := by
  induction h with
  | op n xs ys t op iop i tag t1 t2 s w hr hm ih =>
    simp [everyFnVarsNone, fnVarsNoneExp, ih]
  | nil => rfl
  | refl x => rfl
  | var v t => simp [everyFnVarsNone, fnVarsNoneExp]
  | multi x y zs x1 x2 hx hy ihx ihy =>
    simp_all [everyFnVarsNone, noneAppend]
  | letE xs x x1 t hx hy ihx ihy =>
    simp_all [everyFnVarsNone, fnVarsNoneExp]
  | ite t x y z x1 x2 x3 hx hy hz ihx ihy ihz =>
    simp_all [everyFnVarsNone, fnVarsNoneExp, noneAppend]

/-- Smart operations preserve the function-location annotation predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "every_Fn_SOME_SmartOp"]
theorem smartSome (t : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    everyFnLocationSome [smartOp t op xs] ↔ everyFnLocationSome [.op t op xs] := by
  obtain ⟨ys,h1,h2⟩ := smartRed t op xs
  exact (redSome _ _ h2).trans (redSome _ _ h1).symm

/-- Smart operations preserve absent captured-variable annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "every_Fn_vs_NONE_SmartOp"]
theorem smartNone (t : BackendCommon.Tra) (op : Op) (xs : List Exp)
    (h : everyFnVarsNone xs) : everyFnVarsNone [smartOp t op xs] := by
  obtain ⟨ys,h1,h2⟩ := smartRed t op xs
  apply (redNone _ _ h2).mpr
  apply (redNone _ _ h1).mp
  simpa [everyFnVarsNone, fnVarsNoneExp] using h

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem labelsAppend (xs ys : List Exp) :
    noLabelsList (xs ++ ys) ↔ noLabelsList xs ∧ noLabelsList ys := by
  induction xs with
  | nil => simp [noLabelsList]
  | cons x xs ih => simp [noLabelsList, ih, and_assoc]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem arityAppend (m : Nat) (xs ys : List Exp) :
    obeysMaxAppList m (xs ++ ys) ↔ obeysMaxAppList m xs ∧ obeysMaxAppList m ys := by
  induction xs with
  | nil => simp [obeysMaxAppList]
  | cons x xs ih => simp [obeysMaxAppList, ih, and_assoc]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem redLabels (xs ys : List Exp) (h : RedRel xs ys) :
    noLabelsList xs ↔ noLabelsList ys := by
  induction h with
  | op n xs ys t op iop i tag t1 t2 s w hr hm ih =>
    have hp : ∀ k, op ≠ .label k := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    simp [noLabelsList, noLabels, hp, ih]
  | nil => rfl
  | refl x => rfl
  | var v t => simp [noLabelsList, noLabels]
  | multi x y zs x1 x2 hx hy ihx ihy => simp_all [noLabelsList, labelsAppend]
  | letE xs x x1 t hx hy ihx ihy => simp_all [noLabelsList, noLabels]
  | ite t x y z x1 x2 x3 hx hy hz ihx ihy ihz => simp_all [noLabelsList, noLabels, labelsAppend]

/-- Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem redArity (m : Nat) (xs ys : List Exp) (h : RedRel xs ys) :
    obeysMaxAppList m xs ↔ obeysMaxAppList m ys := by
  induction h with
  | op n xs ys t op iop i tag t1 t2 s w hr hm ih => simp [obeysMaxAppList, obeysMaxApp, ih]
  | nil => rfl
  | refl x => rfl
  | var v t => simp [obeysMaxAppList, obeysMaxApp]
  | multi x y zs x1 x2 hx hy ihx ihy => simp_all [obeysMaxAppList, arityAppend]
  | letE xs x x1 t hx hy ihx ihy => simp_all [obeysMaxAppList, obeysMaxApp]
  | ite t x y z x1 x2 x3 hx hy hz ihx ihy ihz => simp_all [obeysMaxAppList, obeysMaxApp, arityAppend]

/-- Smart operations preserve the absence of label operations. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "no_Labels_SmartOp"]
theorem smartNoLabels (t : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    noLabels (smartOp t op xs) ↔ noLabels (.op t op xs) := by
  obtain ⟨ys,h1,h2⟩ := smartRed t op xs
  have h := (redLabels _ _ h2).trans (redLabels _ _ h1).symm
  simpa [noLabelsList] using h

/-- Smart operations preserve the application-arity limit. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "obeys_max_app_SmartOp"]
theorem smartArity (m : Nat) (t : BackendCommon.Tra) (op : Op) (xs : List Exp)
    (h : ∀ e ∈ xs, obeysMaxApp m e) : obeysMaxApp m (smartOp t op xs) := by
  obtain ⟨ys,h1,h2⟩ := smartRed t op xs
  have hin : obeysMaxAppList m xs := (obeysMaxAppList_iff m xs).mpr h
  have heq := (redArity m _ _ h2).trans (redArity m _ _ h1).symm
  simp [obeysMaxAppList, obeysMaxApp, hin] at heq
  exact heq
end Flapjack.Compiler.Backend.ClosOp
