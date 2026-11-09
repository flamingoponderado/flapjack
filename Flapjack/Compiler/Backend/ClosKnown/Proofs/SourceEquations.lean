module

public import Flapjack.Compiler.Backend.ClosKnown.Total

@[expose] public section

/-! Source-shaped equations for the executed known-function traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- The default is unreachable when used on the result of a singleton
traversal, by `knownListTotal_length`. It makes the source's `HD` explicit in
these Flapjack review equations. -/
def knownSourceHead (xs : List (Exp × ValApprox)) : Exp × ValApprox :=
  xs.headD (.var BackendCommon.orphanTrace 0, .other)

/-- Source-shaped conditional traversal equation, for reviewing the complete
HOL definition; this equation is Flapjack infrastructure. -/
theorem knownListTotal_if (c : Config) (t : BackendCommon.Tra) (x y z : Exp)
    (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.ifThenElse t x y z] env g =
      let (ea1, g) := knownListTotal c [x] env g
      let (ea2, g) := knownListTotal c [y] env g
      let (ea3, g) := knownListTotal c [z] env g
      let (e1, _) := knownSourceHead ea1
      let (e2, a2) := knownSourceHead ea2
      let (e3, a3) := knownSourceHead ea3
      ([(.ifThenElse t e1 e2 e3, mergeHOL a2 a3)], g) := by
  cases hx : knownExprTotal c x env g with
  | mk xe rest =>
    rcases rest with ⟨xa, xg⟩
    cases hy : knownExprTotal c y env xg with
    | mk ye rest =>
      rcases rest with ⟨ya, yg⟩
      cases hz : knownExprTotal c z env yg with
      | mk ze rest =>
        rcases rest with ⟨za, zg⟩
        simp [knownListTotal_single, knownExprTotal, hx, hy, hz, knownSourceHead]

/-- Source-shaped let traversal equation; Flapjack review infrastructure. -/
theorem knownListTotal_let (c : Config) (t : BackendCommon.Tra) (xs : List Exp) (body : Exp)
    (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.let t xs body] env g =
      let (ea1, g) := knownListTotal c xs env g
      let (ea2, g) := knownListTotal c [body] (ea1.map Prod.snd ++ env) g
      let (e2, a2) := knownSourceHead ea2
      ([(.let t (ea1.map Prod.fst) e2, a2)], g) := by
  cases hx : knownListTotal c xs env g with
  | mk eas g1 =>
    cases hb : knownExprTotal c body (eas.map Prod.snd ++ env) g1 with
    | mk be rest =>
      rcases rest with ⟨ba, bg⟩
      simp [knownListTotal_single, knownExprTotal, hx, hb, knownSourceHead]

/-- Source-shaped primitive-operation traversal equation; Flapjack review
infrastructure. -/
theorem knownListTotal_op (c : Config) (t : BackendCommon.Tra) (op : Op) (xs : List Exp)
    (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.op t op xs] env g =
      let (ea1, g) := knownListTotal c xs env g
      let (a, g) := knownOpHOL op (ea1.map Prod.snd).reverse g
      let e := match op, a with
        | .globOp (.global _), .int i => .op t (.intOp (.const i)) (ea1.map Prod.fst)
        | .globOp (.global _), .tuple tag [] => .op t (.blockOp (.cons tag)) (ea1.map Prod.fst)
        | _, _ => ClosOp.smartOp t op (ea1.map Prod.fst)
      ([(e, a)], g) := by
  cases hx : knownListTotal c xs env g with
  | mk eas g1 =>
    cases ho : knownOpHOL op (eas.map Prod.snd).reverse g1 with
    | mk a g2 =>
      simp [knownListTotal_single, knownExprTotal, hx, ho, smartTotal_eq_smartOp]
      split <;> split <;> simp_all

/-- Source-shaped application traversal, including original argument length,
inline body and evaluation order. Flapjack review infrastructure. -/
theorem knownListTotal_app (c : Config) (t : BackendCommon.Tra) (loc : Option Nat)
    (x : Exp) (xs : List Exp) (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.app t loc x xs] env g =
      let (ea2, g) := knownListTotal c xs env g
      let (ea1, g) := knownListTotal c [x] env g
      let (e1, a1) := knownSourceHead ea1
      match decideInlineHOL c a1 loc xs.length with
      | .nothing => ([(.app t loc e1 (ea2.map Prod.fst), .other)], g)
      | .annotate newLoc => ([(.app t (some newLoc) e1 (ea2.map Prod.fst), .other)], g)
      | .letInline body =>
        let (eabody, _) := knownListTotal (decInlineFactor c) [body] (ea2.map Prod.snd) g
        let (ebody, abody) := knownSourceHead eabody
        let args := if pure x then ea2.map Prod.fst else ea2.map Prod.fst ++ [e1]
        ([(.let (BackendCommon.mkCons t 0) args (ticks t 1 xs.length ebody), abody)], g) := by
  cases hs : knownListTotal c xs env g with
  | mk eas g1 =>
    have len := knownListTotal_length c xs env g
    rw [hs] at len
    simp only at len
    cases hx : knownExprTotal c x env g1 with
    | mk e rest =>
      rcases rest with ⟨a, g2⟩
      cases hd : decideInlineHOL c a loc xs.length with
      | nothing =>
        simp [knownListTotal_single, knownExprTotal, hs, hx, knownSourceHead, len, hd]
        split <;> simp_all
      | annotate target =>
        simp [knownListTotal_single, knownExprTotal, hs, hx, knownSourceHead, len, hd]
        split <;> simp_all
      | letInline body =>
        cases hb : knownExprTotal (decInlineFactor c) body (eas.map Prod.snd) g2 with
        | mk ebody rest =>
          rcases rest with ⟨abody, g3⟩
          simp [knownListTotal_single, knownExprTotal, hs, hx, knownSourceHead, len, hd, hb]
          split <;> simp_all

/-- Source-shaped recursive-group traversal, with each body starting from the
same incoming global tree. Flapjack review infrastructure. -/
theorem knownFunsTotal_source (c : Config) (fns : List (Nat × Exp))
    (clos env : List ValApprox) (g : Spt ValApprox) :
    knownFunsTotal c fns clos env g = fns.map (fun (n, e) =>
      (n, (knownSourceHead (knownListTotal c [e] (List.replicate n .other ++ clos ++ env) g).1).1)) := by
  induction fns with
  | nil => simp [knownFunsTotal]
  | cons f fns ih =>
    rcases f with ⟨n, e⟩
    cases he : knownExprTotal c e (List.replicate n .other ++ clos ++ env) g with
    | mk ee rest =>
      rcases rest with ⟨a, g1⟩
      simp [knownFunsTotal, knownListTotal_single, knownSourceHead, ih]

/-- Source-shaped recursive-closure traversal equation. Flapjack review
infrastructure. -/
theorem knownListTotal_letrec (c : Config) (names : List Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vs : Option (List Nat)) (fns : List (Nat × Exp)) (body : Exp)
    (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.letrec names loc vs fns body] env g =
      let clos := match loc with
        | none => List.replicate fns.length ValApprox.other
        | some n => closGenNoInline n 0 fns
      let newFns := fns.map (fun (n, e) =>
        (n, (knownSourceHead (knownListTotal c [e] (List.replicate n .other ++ clos ++ env) g).1).1))
      let (ea1, g) := knownListTotal c [body] (clos ++ env) g
      let (e1, a1) := knownSourceHead ea1
      ([(.letrec names loc none newFns e1, a1)], g) := by
  cases loc with
  | none =>
    cases hb : knownExprTotal c body (List.replicate fns.length .other ++ env) g with
    | mk be rest =>
      rcases rest with ⟨ba, bg⟩
      simp [knownListTotal_single, knownExprTotal, hb, knownSourceHead, knownFunsTotal_source]
  | some loc =>
    cases hb : knownExprTotal c body (closGenNoInline loc 0 fns ++ env) g with
    | mk be rest =>
      rcases rest with ⟨ba, bg⟩
      simp [knownListTotal_single, knownExprTotal, hb, knownSourceHead, knownFunsTotal_source, noInline]

/-- Source-shaped raise traversal equation; Flapjack review infrastructure. -/
theorem knownListTotal_raise (c : Config) (t : BackendCommon.Tra) (x : Exp)
    (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.raise t x] env g =
      let (ea, g) := knownListTotal c [x] env g
      ([(.raise t (knownSourceHead ea).1, .impossible)], g) := by
  cases hx : knownExprTotal c x env g with
  | mk e rest =>
    rcases rest with ⟨a, g1⟩
    simp [knownListTotal_single, knownExprTotal, hx, knownSourceHead]

/-- Source-shaped tick traversal equation; Flapjack review infrastructure. -/
theorem knownListTotal_tickSource (c : Config) (t : BackendCommon.Tra) (x : Exp)
    (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.tick t x] env g =
      let (ea, g) := knownListTotal c [x] env g
      let (e, a) := knownSourceHead ea
      ([(.tick t e, a)], g) := by
  cases hx : knownExprTotal c x env g with
  | mk e rest =>
    rcases rest with ⟨a, g1⟩
    simp [knownListTotal_single, knownExprTotal, hx, knownSourceHead]

/-- Source-shaped exception-handler traversal equation; Flapjack review infrastructure. -/
theorem knownListTotal_handle (c : Config) (t : BackendCommon.Tra) (x y : Exp)
    (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.handle t x y] env g =
      let (ea1, g) := knownListTotal c [x] env g
      let (ea2, g) := knownListTotal c [y] (.other :: env) g
      let (e1, a1) := knownSourceHead ea1
      let (e2, a2) := knownSourceHead ea2
      ([(.handle t e1 e2, mergeHOL a1 a2)], g) := by
  cases hx : knownExprTotal c x env g with
  | mk e1 rest =>
    rcases rest with ⟨a1, g1⟩
    cases hy : knownExprTotal c y (.other :: env) g1 with
    | mk e2 rest =>
      rcases rest with ⟨a2, g2⟩
      simp [knownListTotal_single, knownExprTotal, hx, hy, knownSourceHead]

/-- Source-shaped direct-call traversal equation; Flapjack review infrastructure. -/
theorem knownListTotal_call (c : Config) (t : BackendCommon.Tra) (ticks dest : Nat)
    (xs : List Exp) (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.call t ticks dest xs] env g =
      let (ea, g) := knownListTotal c xs env g
      ([(.call t ticks dest (ea.map Prod.fst), .other)], g) := by
  cases hx : knownListTotal c xs env g with
  | mk eas g1 => simp [knownListTotal_single, knownExprTotal, hx]

/-- Source-shaped closure traversal equation; Flapjack review infrastructure. -/
theorem knownListTotal_fn (c : Config) (name : Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vs : Option (List Nat)) (arity : Nat) (body : Exp)
    (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c [.fn name loc vs arity body] env g =
      let (ea, g) := knownListTotal c [body] (List.replicate arity .other ++ env) g
      let e := (knownSourceHead ea).1
      let a := match loc with
        | none => ValApprox.other
        | some n => closApproxHOL c.inlineMaxBodySize n arity body
      ([(.fn name loc none arity e, a)], g) := by
  cases hb : knownExprTotal c body (List.replicate arity .other ++ env) g with
  | mk e rest =>
    rcases rest with ⟨a, g1⟩
    cases loc <;> simp [knownListTotal_single, knownExprTotal, hb, knownSourceHead]

end Flapjack.Compiler.Backend.ClosKnown
