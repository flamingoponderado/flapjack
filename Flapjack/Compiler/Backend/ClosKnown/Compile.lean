import Flapjack.Compiler.Backend.ClosKnown.Inline
import Flapjack.Compiler.Backend.ClosKnown.Merge
import Flapjack.Compiler.Backend.ClosFvs
import Flapjack.Compiler.Backend.ClosTicks
import Flapjack.Compiler.Backend.ClosLetop
import Flapjack.Compiler.Backend.ClosOp

/-! Fuel-bounded executable known-function optimization. The source totality
argument and compiler correctness proof remain unported. -/
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

/-- Propagate approximations through original global and constructor operations. -/
def knownOpFuel (fuel : Nat) (op : Op) (args : List ValApprox) (globals : Spt ValApprox) :
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

private def ticks (trace : BackendCommon.Tra) : Nat → Nat → Exp → Exp
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

mutual
  /-- Traverse one closure expression while tracking local and global values. -/
  def knownFuel : Nat → Config → Exp → List ValApprox → Spt ValApprox →
      Option (Exp × ValApprox × Spt ValApprox)
    | 0, _, _, _, _ => none
    | fuel + 1, c, e, env, globals => do
      match e with
      | .var t v => pure (.var t v, env[v]?.getD .other, globals)
      | .ifThenElse t x y z =>
          let (x, _, globals) ← knownFuel fuel c x env globals
          let (y, a, globals) ← knownFuel fuel c y env globals
          let (z, b, globals) ← knownFuel fuel c z env globals
          pure (.ifThenElse t x y z, ← mergeBounded fuel a b, globals)
      | .let t xs body =>
          let (xs, globals) ← knownListFuel fuel c xs env globals
          let (body, a, globals) ← knownFuel fuel c body (xs.map Prod.snd ++ env) globals
          pure (.let t (xs.map Prod.fst) body, a, globals)
      | .raise t x =>
          let (x, _, globals) ← knownFuel fuel c x env globals
          pure (.raise t x, .impossible, globals)
      | .tick t x =>
          let (x, a, globals) ← knownFuel fuel c x env globals
          pure (.tick t x, a, globals)
      | .handle t x y =>
          let (x, a, globals) ← knownFuel fuel c x env globals
          let (y, b, globals) ← knownFuel fuel c y (.other :: env) globals
          pure (.handle t x y, ← mergeBounded fuel a b, globals)
      | .call t n dest xs =>
          let (xs, globals) ← knownListFuel fuel c xs env globals
          pure (.call t n dest (xs.map Prod.fst), .other, globals)
      | .op t op xs =>
          let (xs, globals) ← knownListFuel fuel c xs env globals
          let (a, globals) ← knownOpFuel fuel op (xs.map Prod.snd).reverse globals
          let args := xs.map Prod.fst
          let result ← match op, a with
            | .globOp (.global _), .int i => pure (.op t (.intOp (.const i)) args)
            | .globOp (.global _), .tuple tag [] => pure (.op t (.blockOp (.cons tag)) args)
            | _, _ => ClosOp.smartFuel fuel t op args
          pure (result, a, globals)
      | .app t loc x xs =>
          let (xs, globals) ← knownListFuel fuel c xs env globals
          let (x', a, globals) ← knownFuel fuel c x env globals
          match ← decideInlineFuel fuel c a loc xs.length with
          | .nothing => pure (.app t loc x' (xs.map Prod.fst), .other, globals)
          | .annotate loc => pure (.app t (some loc) x' (xs.map Prod.fst), .other, globals)
          | .letInline body =>
              let (body, result, _) ← knownFuel fuel (decInlineFactor c) body (xs.map Prod.snd) globals
              let args := xs.map Prod.fst
              let args := if ClosLang.pure x then args else args ++ [x']
              pure (.let (BackendCommon.mkCons t 0) args (ticks t 1 xs.length body), result, globals)
      | .fn name loc _ arity body =>
          let (body', _, globals) ← knownFuel fuel c body (List.replicate arity .other ++ env) globals
          let approx ← match loc with
            | none => pure .other
            | some loc => closApproxFuel fuel c.inlineMaxBodySize loc arity body
          pure (.fn name loc none arity body', approx, globals)
      | .letrec names loc _ fns body =>
          let clos := match loc with
            | none => List.replicate fns.length ValApprox.other
            | some loc => noInline loc fns
          let fns' ← fns.mapM fun (arity, e) => do
            let (e, _, _) ← knownFuel fuel c e (List.replicate arity .other ++ clos ++ env) globals
            pure (arity, e)
          let (body, a, globals) ← knownFuel fuel c body (clos ++ env) globals
          pure (.letrec names loc none fns' body, a, globals)

  /-- Traverse expressions in source order, threading global approximations. -/
  def knownListFuel : Nat → Config → List Exp → List ValApprox → Spt ValApprox →
      Option (List (Exp × ValApprox) × Spt ValApprox)
    | _, _, [], _, globals => some ([], globals)
    | 0, _, _ :: _, _, _ => none
    | fuel + 1, c, x :: xs, env, globals => do
      let (x, a, globals) ← knownFuel fuel c x env globals
      let (xs, globals) ← knownListFuel fuel c xs env globals
      pure ((x, a) :: xs, globals)
end

/-- Retry traversal with a structural bound when inlining is disabled. -/
def knownListBounded (fuel : Nat) (c : Config) (xs : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : Option (List (Exp × ValApprox) × Spt ValApprox) :=
  match knownListFuel fuel c xs env globals with
  | some result => some result
  | none =>
    if c.inlineFactor = 0 then
      knownListFuel (max fuel (ClosLang.listBudget xs + 1)) c xs env globals
    else none

/-- Apply free-variable cleanup, approximation, tick removal and let-op cleanup. -/
def compileFuel (fuel : Nat) (config : Option Config) (es : List Exp) : Option (Option Config × List Exp) := do
  match config with
  | none => pure (none, es)
  | some c =>
      let es ← es.mapM (ClosFvs.removeBounded fuel 0)
      let (es, globals) ← knownListBounded fuel c es [] .ln
      let es ← es.mapM fun (e, _) => do
        let e ← ClosTicks.removeBounded fuel e
        ClosLetop.compileBounded fuel e
      pure (some { c with valApproxSpt := globals }, es)

/-- Incremental known-function optimization retains the incoming global
approximations, resets the inline factor, and discards incoming auxiliary
code when enabled. Failure remains explicit when bounded inlining runs out of
fuel. This checked implementation still needs HOL correspondence review. -/
def compileIncFuel (fuel : Nat) (config : Option Config)
    (program : List Exp × List (Nat × Nat × Exp)) :
    Option (Option Config × (List Exp × List (Nat × Nat × Exp))) := do
  let previousGlobals := optionValApproxSpt config
  match config with
  | none => pure (none, program)
  | some c =>
      let es ← program.1.mapM (ClosFvs.removeBounded fuel 0)
      let static := { resetInlineFactor c with valApproxSpt := .ln }
      let (es, globals) ← knownListBounded fuel static es [] previousGlobals
      let es ← es.mapM fun (e, _) => do
        let e ← ClosTicks.removeBounded fuel e
        ClosLetop.compileBounded fuel e
      pure (optionUpdValSpt globals config, (es, []))

end Flapjack.Compiler.Backend.ClosKnown
