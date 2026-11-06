import Flapjack.Compiler.Backend.ClosKnown.Inline
import Flapjack.Compiler.Backend.ClosKnown.KnownOp
import Flapjack.Compiler.Backend.ClosFvs
import Flapjack.Compiler.Backend.ClosTicks
import Flapjack.Compiler.Backend.ClosLetop
import Flapjack.Compiler.Backend.ClosOp

/-! Previous fuel-bounded known-function traversal and shared helpers. The
production traversal is in `Total`; full HOL correctness remains unproved. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- Merge value approximations, comparing complete closure bodies. -/
def mergeFuel : Nat → ValApprox → ValApprox → Option ValApprox
  | 0, _, _ => none
  | _ + 1, .impossible, y => some y
  | _ + 1, x, .impossible => some x
  | fuel + 1, .tuple a xs, .tuple b ys => do
      if a != b || xs.length != ys.length then return .other
      pure (.tuple a (← (xs.zip ys).mapM fun (x, y) => mergeFuel fuel x y))
  | _ + 1, .closNoInline a x, .closNoInline b y =>
      some (if a == b && x == y then .closNoInline a x else .other)
  | _ + 1, .clos a x e s, .clos b y f t =>
      some (if a == b && x == y && e == f && s == t then .clos a x e s else .other)
  | _ + 1, .int a, .int b => some (if a == b then .int a else .other)
  | _ + 1, _, _ => some .other

/-- Flapjack infrastructure relating the old checked pair traversal to the
total list helper; there is no separate HOL declaration for the retry. -/
private theorem mergeListHOL_eq_of_mapM_success (fuel : Nat)
    (ih : ∀ a b result, mergeFuel fuel a b = some result → mergeHOL a b = result) :
    ∀ xs ys result, ((xs.zip ys).mapM fun (x, y) => mergeFuel fuel x y) = some result →
      mergeListHOL xs ys = result := by
  intro xs
  induction xs with
  | nil =>
    intro ys result h
    simp at h
    subst result
    simp [mergeListHOL]
  | cons x xs ihxs =>
    intro ys result h
    cases ys with
    | nil =>
      simp at h
      subst result
      simp [mergeListHOL]
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mapM_cons, Option.bind_eq_bind] at h
      cases he : mergeFuel fuel x y with
      | none => simp [he] at h
      | some v =>
        cases ht : (xs.zip ys).mapM (fun (x, y) => mergeFuel fuel x y) with
        | none => simp [he, ht] at h
        | some vs =>
          simp [he, ht] at h
          subst result
          simp [mergeListHOL, ih x y v he, ihxs ys vs ht]

/-- Flapjack infrastructure showing preservation of a successful old merge;
HOL has no fuel-bounded merge to which this theorem could correspond. -/
theorem mergeHOL_eq_of_success : ∀ fuel a b result,
    mergeFuel fuel a b = some result → mergeHOL a b = result := by
  intro fuel
  induction fuel with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    intro a b result h
    cases a <;> cases b <;> simp only [mergeFuel, mergeHOL] at *
    all_goals try { split at h <;> simp_all }
    all_goals try { simp_all }
    case succ.tuple.tuple tag xs tag₂ ys =>
      split at h
      · simp_all <;> grind
      · cases hs : (xs.zip ys).mapM (fun (x, y) => mergeFuel fuel x y) with
        | none => simp [hs] at h
        | some out =>
          have hl := mergeListHOL_eq_of_mapM_success fuel ih xs ys out hs
          simp_all
mutual
/-- Structural fuel bound for one approximation. -/
def approxBudget : ValApprox → Nat
  | .tuple _ xs => 2 + approxListBudget xs
  | _ => 2
termination_by a => sizeOf a
decreasing_by all_goals simp_wf <;> omega

/-- Structural fuel bound for a list of approximations. -/
def approxListBudget : List ValApprox → Nat
  | [] => 2
  | x :: xs => 2 + approxBudget x + approxListBudget xs
termination_by xs => sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

/-- The source merge is total; the fuel parameter is retained for callers of
this checked interface. `mergeHOL_eq_of_success` proves agreement whenever the
former fuel-bounded traversal succeeds. -/
def mergeBounded (_fuel : Nat) (a b : ValApprox) : Option ValApprox :=
  some (mergeHOL a b)

/-- Previous checked operation, retained only for the Flapjack preservation proof;
HOL has no fuel-bounded version of `known_op`. -/
private def knownOpFuelPrevious (fuel : Nat) (op : Op) (args : List ValApprox) (globals : Spt ValApprox) :
    Option (ValApprox × Spt ValApprox) := do
  match op, args with
  | .globOp (.global n), [] => pure ((sptLookup n globals).getD .other, globals)
  | .globOp (.setGlobal n), a :: _ =>
      let value ← match sptLookup n globals with
        | none => pure a
        | some old => mergeBounded fuel old a
      pure (.other, sptInsert n value globals)
  | .blockOp (.cons tag), _ => pure (.tuple tag args, globals)
  | .intOp (.const n), _ => pure (.int n, globals)
  | .memOp .el, [.tuple _ xs, .int i] =>
      pure (if 0 ≤ i && i < Int.ofNat xs.length then (xs[i.toNat]?.getD .other, globals) else (.other, globals))
  | .memOp .el, .impossible :: _ => pure (.impossible, globals)
  | .memOp .el, _ :: .impossible :: _ => pure (.impossible, globals)
  | _, _ => pure (.other, globals)

/-- The checked interface now runs the source total operation directly. -/
def knownOpFuel (_fuel : Nat) (op : Op) (args : List ValApprox) (globals : Spt ValApprox) :
    Option (ValApprox × Spt ValApprox) :=
  some (knownOpHOL op args globals)

/-- Flapjack preservation proof for the former checked implementation; this
fuel-bounded interface has no separate HOL original. -/
theorem knownOpFuel_eq_previous (fuel : Nat) (op : Op) (args : List ValApprox) (globals : Spt ValApprox) :
    knownOpFuel fuel op args globals = knownOpFuelPrevious fuel op args globals := by
  unfold knownOpFuel
  symm
  unfold knownOpFuelPrevious knownOpHOL
  cases op with
  | intOp o => cases o <;> simp
  | blockOp o => cases o <;> simp
  | globOp o => cases o <;> cases args <;> simp [mergeBounded] <;> (try split) <;> simp_all
  | memOp o =>
    cases o <;> try simp
    case el =>
      cases args with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => cases a <;> simp
        | cons b tail =>
          cases tail with
          | nil =>
            cases a <;> cases b <;> simp <;>
              (try split) <;> simp_all
          | cons c tail => cases a <;> cases b <;> simp
  | _ => simp

/-- Insert the source tick sequence, numbering from the supplied trace index. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "mk_Ticks_def"]
def ticks (trace : BackendCommon.Tra) : Nat → Nat → Exp → Exp
  | _, 0, e => e
  | index, n + 1, e => ticks trace (index + 1) n (.tick (BackendCommon.mkCons trace index) e)

/-- Generate non-inlineable approximations for a recursive closure group. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "clos_gen_noinline_def"]
def closGenNoInline {α : Type} (loc index : Nat) : List (Nat × α) → List ValApprox
  | [] => []
  | (arity, _) :: rest =>
      .closNoInline (loc + 2 * index) arity :: closGenNoInline loc (index + 1) rest

def noInline (loc : Nat) (fns : List (Nat × Exp)) : List ValApprox :=
  closGenNoInline loc 0 fns

/-- The source recursion agrees with the previous indexed-list implementation. -/
theorem closGenNoInline_eq_zipIdx {α : Type} (loc index : Nat) (fns : List (Nat × α)) :
    closGenNoInline loc index fns =
      (fns.zipIdx index).map (fun ((arity, _), i) => .closNoInline (loc + 2 * i) arity) := by
  induction fns generalizing index with
  | nil => rfl
  | cons p rest ih =>
    cases p
    simp [closGenNoInline, ih]

/-- Switching to the source recursion preserves the previous executable result. -/
theorem noInline_eq_zip (loc : Nat) (fns : List (Nat × Exp)) :
    noInline loc fns =
      (fns.zip (List.range fns.length)).map
        (fun ((arity, _), i) => .closNoInline (loc + 2 * i) arity) := by
  rw [noInline, closGenNoInline_eq_zipIdx, List.zipIdx_eq_zip_range']
  rw [List.range_eq_range']

end Flapjack.Compiler.Backend.ClosKnown
