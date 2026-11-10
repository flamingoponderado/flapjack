module

public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartTotal
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineDecrease

@[expose] public section
/-! Total known-function traversal with a lexicographic termination measure.
The list traversal implements the source recursion through mutually recursive
expression and recursive-group helpers. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- Run the checked smart constructor at a fixed initial fuel. Its retry
result is independent of that fuel, as proved below. Flapjack infrastructure,
not a separately tagged HOL definition. -/
def smartTotal (t : BackendCommon.Tra) (op : Op) (xs : List Exp) : Exp :=
  (ClosOp.smartFuel 0 t op xs).get (by
    obtain ⟨value, h⟩ := ClosOp.smartFuel_succeeds 0 t op xs
    simp [h])


mutual
 /-- Traverse one expression using the source termination measure. This helper
 has no separate HOL declaration. -/
 def knownExprTotal (c : Config) (e : Exp) (env : List ValApprox) (globals : Spt ValApprox) :
     Exp × ValApprox × Spt ValApprox :=
  match e with
  | .var t v => (.var t v, env[v]?.getD .other, globals)
  | .ifThenElse t x y z =>
      let (x, _, globals) := knownExprTotal c x env globals
      let (y, a, globals) := knownExprTotal c y env globals
      let (z, b, globals) := knownExprTotal c z env globals
      (.ifThenElse t x y z, mergeHOL a b, globals)
  | .let t xs body =>
      let (xs, globals) := knownListTotal c xs env globals
      let (body, a, globals) := knownExprTotal c body (xs.map Prod.snd ++ env) globals
      (.let t (xs.map Prod.fst) body, a, globals)
  | .raise t x =>
      let (x, _, globals) := knownExprTotal c x env globals
      (.raise t x, .impossible, globals)
  | .tick t x =>
      let (x, a, globals) := knownExprTotal c x env globals
      (.tick t x, a, globals)
  | .handle t x y =>
      let (x, a, globals) := knownExprTotal c x env globals
      let (y, b, globals) := knownExprTotal c y (.other :: env) globals
      (.handle t x y, mergeHOL a b, globals)
  | .call t n dest xs =>
      let (xs, globals) := knownListTotal c xs env globals
      (.call t n dest (xs.map Prod.fst), .other, globals)
  | .op t op xs =>
      let (xs, globals) := knownListTotal c xs env globals
      let (a, globals) := knownOpHOL op (xs.map Prod.snd).reverse globals
      let args := xs.map Prod.fst
      let result := match op, a with
        | .globOp (.global _), .int i => .op t (.intOp (.const i)) args
        | .globOp (.global _), .tuple tag [] => .op t (.blockOp (.cons tag)) args
        | _, _ => smartTotal t op args
      (result, a, globals)
  | .app t loc x xs =>
      let (xs, globals) := knownListTotal c xs env globals
      let (x2, a, globals) := knownExprTotal c x env globals
      match _hd : decideInlineHOL c a loc xs.length with
      | .nothing => (.app t loc x2 (xs.map Prod.fst), .other, globals)
      | .annotate loc => (.app t (some loc) x2 (xs.map Prod.fst), .other, globals)
      | .letInline body =>
          let (body, result, _) := knownExprTotal (decInlineFactor c) body (xs.map Prod.snd) globals
          let args := xs.map Prod.fst
          let args := if ClosLang.pure x then args else args ++ [x2]
          (.let (BackendCommon.mkCons t 0) args (ticks t 1 xs.length body), result, globals)
  | .fn name loc _ arity body =>
      let (body2, _, globals) := knownExprTotal c body (List.replicate arity .other ++ env) globals
      let approx := match loc with
        | none => .other
        | some loc => closApproxHOL c.inlineMaxBodySize loc arity body
      (.fn name loc none arity body2, approx, globals)
  | .letrec names loc _ fns body =>
      let clos := match loc with
        | none => List.replicate fns.length ValApprox.other
        | some loc => noInline loc fns
      let fns2 := knownFunsTotal c fns clos env globals
      let (body, a, globals) := knownExprTotal c body (clos ++ env) globals
      (.letrec names loc none fns2 body, a, globals)
 termination_by (c.inlineFactor, sizeOf e)
 decreasing_by
   all_goals simp_wf
   all_goals try omega
   all_goals
     have hp := decideInlineLetInline c _ _ _ _ _hd
     simp only [decInlineFactor]
     omega

 /-- Traverse a list in source order while threading global approximations.
 The source-shaped equations are checked in `Proofs.SourceEquations`; its
 singleton-head defaults are unreachable by `knownListTotal_length`. -/
 @[hol "cakeml/compiler/backend/clos_knownScript.sml" "known_def"]
 def knownListTotal (c : Config) (xs : List Exp) (env : List ValApprox) (globals : Spt ValApprox) :
     List (Exp × ValApprox) × Spt ValApprox :=
  match xs with
  | [] => ([], globals)
  | x :: xs =>
      let (x, a, globals) := knownExprTotal c x env globals
      let (xs, globals) := knownListTotal c xs env globals
      ((x, a) :: xs, globals)
 termination_by (c.inlineFactor, sizeOf xs)
 decreasing_by all_goals (simp_wf; omega)

 /-- Traverse recursive function bodies in order without threading their
 resulting globals. Flapjack infrastructure with no separate HOL declaration. -/
 def knownFunsTotal (c : Config) (fns : List (Nat × Exp)) (clos env : List ValApprox)
     (globals : Spt ValApprox) : List (Nat × Exp) :=
  match fns with
  | [] => []
  | (arity, body) :: fns =>
      let (body, _, _) := knownExprTotal c body (List.replicate arity .other ++ clos ++ env) globals
      (arity, body) :: knownFunsTotal c fns clos env globals
 termination_by (c.inlineFactor, sizeOf fns)
 decreasing_by all_goals (simp_wf; omega)
end

/-- The source traversal preserves the number of expressions. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "known_LENGTH"]
theorem knownListTotal_length (c : Config) (xs : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : (knownListTotal c xs env globals).1.length = xs.length := by
  induction xs generalizing globals with
  | nil => simp [knownListTotal]
  | cons x xs ih =>
    rw [knownListTotal]
    cases hx : knownExprTotal c x env globals with
    | mk xe rest =>
      rcases rest with ⟨xa, xg⟩
      cases hs : knownListTotal c xs env xg with
      | mk ys yg =>
        have length := ih xg
        rw [hs] at length
        simp_all

/-- The result of the known-function traversal has the input length. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "known_LENGTH_EQ_E"]
theorem knownListTotal_length_eq (c : Config) (xs : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox) (out : List (Exp × ValApprox)) (final : Spt ValApprox)
    (run : knownListTotal c xs env globals = (out, final)) : out.length = xs.length := by
  have length := knownListTotal_length c xs env globals
  simpa [run] using length

/-- The checked smart constructor is the source-shaped total smart operation.
This is Flapjack infrastructure for reviewing the executed traversal. -/
theorem smartTotal_eq_smartOp (t : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    smartTotal t op xs = ClosOp.smartOp t op xs := by
  simp [smartTotal, ClosOp.smartFuel]

/-- A singleton traversal returns precisely the expression traversal's pair.
This is Flapjack infrastructure with no separate HOL declaration. -/
theorem knownListTotal_single (c : Config) (e : Exp) (env : List ValApprox)
    (globals : Spt ValApprox) :
    knownListTotal c [e] env globals =
      let (e', a, g') := knownExprTotal c e env globals
      ([(e', a)], g') := by
  cases h : knownExprTotal c e env globals with
  | mk e' rest =>
    rcases rest with ⟨a, g'⟩
    simp [knownListTotal, h]

/-- The source's multi-element recursion first processes the head and then
threads its globals through the remaining nonempty list. This is Flapjack
infrastructure for the source list equation. -/
theorem knownListTotal_cons_cons (c : Config) (x y : Exp) (xs : List Exp)
    (env : List ValApprox) (globals : Spt ValApprox) :
    knownListTotal c (x :: y :: xs) env globals =
      let (first, g1) := knownListTotal c [x] env globals
      let (rest, g2) := knownListTotal c (y :: xs) env g1
      (first ++ rest, g2) := by
  cases h : knownExprTotal c x env globals with
  | mk e rest =>
    rcases rest with ⟨a, g⟩
    simp only [knownListTotal, h]
    cases knownListTotal c (y :: xs) env g
    rfl

/-- The traversed list has one element whenever the input has one element.
This is Flapjack infrastructure with no separate HOL declaration. -/
theorem knownListTotal_single_result (c : Config) (e : Exp) (env : List ValApprox)
    (g0 g : Spt ValApprox) (result : List (Exp × ValApprox))
    (h : knownListTotal c [e] env g0 = (result, g)) :
    ∃ e' a, result = [(e', a)] := by
  rw [knownListTotal_single] at h
  cases hx : knownExprTotal c e env g0 with
  | mk e' rest =>
    rcases rest with ⟨a, g'⟩
    simp only [hx, Prod.mk.injEq] at h
    exact ⟨e', a, h.1.symm⟩

/-- Variable traversal uses the environment approximation when in range and
the source default otherwise. This is Flapjack traversal infrastructure. -/
theorem knownListTotal_var (c : Config) (t : BackendCommon.Tra) (index : Nat)
    (env : List ValApprox) (globals : Spt ValApprox) :
    knownListTotal c [.var t index] env globals =
      ([(.var t index, env[index]?.getD .other)], globals) := by
  simp [knownListTotal, knownExprTotal]

end Flapjack.Compiler.Backend.ClosKnown
