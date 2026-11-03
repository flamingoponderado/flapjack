import Flapjack.Compiler.Backend.ClosKnown.Fuel
import Flapjack.Compiler.Backend.ClosOp.Proofs.FuelStable
import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineDecrease
/-! Total Flapjack known-function traversal with a lexicographic termination
measure. This is not yet tagged as HOL `known_def`: complete correspondence of
the smart-operation helper to the source remains to be established. -/
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
 /-- Traverse one expression using the source termination measure. This is
 Flapjack infrastructure until full HOL correspondence is proved. -/
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

 /-- Traverse a list in order while threading global approximations. This is
 Flapjack infrastructure until full HOL correspondence is proved. -/
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

/-- The total list traversal preserves the number of expressions. This is a
Flapjack infrastructure fact; it is not yet a port of HOL `known_LENGTH`
because correspondence of the complete traversal remains to be proved. -/
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

/-- All checked smart-constructor fuels return the selected total result.
Flapjack retry infrastructure; no separate HOL theorem. -/
theorem smartFuel_eq_smartTotal (fuel : Nat) (t : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    ClosOp.smartFuel fuel t op xs = some (smartTotal t op xs) := by
  rw [ClosOp.smartFuel_independent fuel 0]
  unfold smartTotal
  exact (Option.some_get _).symm

/-- Relate checked recursive-group traversal to its total counterpart.
Flapjack proof infrastructure; no separate HOL theorem. -/
private theorem mapFuns_matches (fuel : Nat)
    (iexp : ∀ c e env globals result, knownFuel fuel c e env globals = some result →
      result = knownExprTotal c e env globals)
    (c : Config) (fns : List (Nat × Exp)) (clos env : List ValApprox) (globals : Spt ValApprox)
    (result : List (Nat × Exp))
    (h : fns.mapM (fun (arity, e) => do
      let (e, _, _) ← knownFuel fuel c e (List.replicate arity ValApprox.other ++ (clos ++ env)) globals
      pure (arity, e)) = some result) : result = knownFunsTotal c fns clos env globals := by
  induction fns generalizing result with
  | nil => simpa [knownFunsTotal] using h.symm
  | cons p ps ih =>
    rcases p with ⟨arity, body⟩
    cases hx : knownFuel fuel c body (List.replicate arity ValApprox.other ++ (clos ++ env)) globals with
    | none => simp [hx] at h
    | some val =>
      rcases val with ⟨be, ba, bg⟩
      cases ht : ps.mapM (fun (arity, e) => do
          let (e, _, _) ← knownFuel fuel c e (List.replicate arity ValApprox.other ++ (clos ++ env)) globals
          pure (arity, e)) with
      | none =>
        change (ps.mapM (fun p => (knownFuel fuel c p.2
          (List.replicate p.1 ValApprox.other ++ (clos ++ env)) globals).bind
            (fun z => some (p.1, z.1)))) = none at ht
        simp [hx, ht] at h
      | some tail =>
        have et := ih tail ht
        change (ps.mapM (fun p => (knownFuel fuel c p.2
          (List.replicate p.1 ValApprox.other ++ (clos ++ env)) globals).bind
            (fun z => some (p.1, z.1)))) = some tail at ht
        have ex := iexp c body (List.replicate arity ValApprox.other ++ (clos ++ env)) globals _ hx
        simp [hx, ht] at h
        rw [knownFunsTotal]
        simp only [List.append_assoc]
        rw [← ex]
        dsimp only
        rw [← et]
        exact h.symm

/-- Every successful checked traversal agrees with the total traversal, for
all expressions, environments, globals and inline factors. This relates
Flapjack implementations and is not a HOL correctness theorem. -/
theorem knownFuel_matches_total (fuel : Nat) :
    (∀ c e env globals result, knownFuel fuel c e env globals = some result →
      result = knownExprTotal c e env globals) ∧
    (∀ c xs env globals result, knownListFuel fuel c xs env globals = some result →
      result = knownListTotal c xs env globals) := by
  induction fuel with
  | zero =>
    constructor
    · intro c e env globals result h
      simp [knownFuel] at h
    · intro c xs env globals result h
      cases xs with
      | nil => simpa [knownListFuel, knownListTotal] using h.symm
      | cons x xs => simp [knownListFuel] at h
  | succ fuel ih =>
    rcases ih with ⟨iexp, ilist⟩
    constructor
    · intro c e env globals result h
      cases e with
      | var t v => simpa [knownFuel, knownExprTotal] using h.symm
      | raise t x =>
        cases hx : knownFuel fuel c x env globals with
        | none => simp [knownFuel, hx] at h
        | some val =>
          rcases val with ⟨xe, xa, xg⟩
          have ex := iexp c x env globals _ hx
          simp [knownFuel, hx] at h
          rw [knownExprTotal, ← ex]
          exact h.symm
      | tick t x =>
        cases hx : knownFuel fuel c x env globals with
        | none => simp [knownFuel, hx] at h
        | some val =>
          rcases val with ⟨xe, xa, xg⟩
          have ex := iexp c x env globals _ hx
          simp [knownFuel, hx] at h
          rw [knownExprTotal, ← ex]
          exact h.symm
      | handle t x y =>
        cases hx : knownFuel fuel c x env globals with
        | none => simp [knownFuel, hx] at h
        | some val =>
          rcases val with ⟨xe, xa, xg⟩
          cases hy : knownFuel fuel c y (.other :: env) xg with
          | none => simp [knownFuel, hx, hy] at h
          | some val =>
            rcases val with ⟨ye, ya, yg⟩
            have ex := iexp c x env globals _ hx
            have ey := iexp c y (.other :: env) xg _ hy
            simp [knownFuel, hx, hy, mergeBounded] at h
            rw [knownExprTotal, ← ex]
            dsimp only
            rw [← ey]
            exact h.symm
      | «let» t xs body =>
        cases hx : knownListFuel fuel c xs env globals with
        | none => simp [knownFuel, hx] at h
        | some val =>
          rcases val with ⟨ys, xg⟩
          cases hb : knownFuel fuel c body (ys.map Prod.snd ++ env) xg with
          | none => simp [knownFuel, hx, hb] at h
          | some val =>
            rcases val with ⟨be, ba, bg⟩
            have ex := ilist c xs env globals _ hx
            have eb := iexp c body (ys.map Prod.snd ++ env) xg _ hb
            simp [knownFuel, hx, hb] at h
            rw [knownExprTotal, ← ex]
            dsimp only
            rw [← eb]
            exact h.symm
      | call t n dest xs =>
        cases hx : knownListFuel fuel c xs env globals with
        | none => simp [knownFuel, hx] at h
        | some val =>
          rcases val with ⟨ys, xg⟩
          have ex := ilist c xs env globals _ hx
          simp [knownFuel, hx] at h
          rw [knownExprTotal, ← ex]
          exact h.symm
      | ifThenElse t x y z =>
        cases hx : knownFuel fuel c x env globals with
        | none => simp [knownFuel, hx] at h
        | some val =>
          rcases val with ⟨xe, xa, xg⟩
          cases hy : knownFuel fuel c y env xg with
          | none => simp [knownFuel, hx, hy] at h
          | some val =>
            rcases val with ⟨ye, ya, yg⟩
            cases hz : knownFuel fuel c z env yg with
            | none => simp [knownFuel, hx, hy, hz] at h
            | some val =>
              rcases val with ⟨ze, za, zg⟩
              have ex := iexp c x env globals _ hx
              have ey := iexp c y env xg _ hy
              have ez := iexp c z env yg _ hz
              simp [knownFuel, hx, hy, hz, mergeBounded] at h
              rw [knownExprTotal, ← ex]
              dsimp only
              rw [← ey]
              dsimp only
              rw [← ez]
              exact h.symm
      | fn name loc vs arity body =>
        cases hb : knownFuel fuel c body (List.replicate arity .other ++ env) globals with
        | none => simp [knownFuel, hb] at h
        | some val =>
          rcases val with ⟨be, ba, bg⟩
          have eb := iexp c body (List.replicate arity .other ++ env) globals _ hb
          cases loc <;> simp [knownFuel, hb, closApproxFuel] at h <;>
            rw [knownExprTotal, ← eb] <;> simp_all
      | op t op xs =>
        cases hx : knownListFuel fuel c xs env globals with
        | none => simp [knownFuel, hx] at h
        | some val =>
          rcases val with ⟨ys, xg⟩
          have ex := ilist c xs env globals _ hx
          simp [knownFuel, hx, knownOpFuel, smartFuel_eq_smartTotal] at h
          rw [knownExprTotal, ← ex]
          dsimp only
          cases hk : knownOpHOL op (ys.map Prod.snd).reverse xg with
          | mk a g =>
            simp [hk] at h ⊢
            split at h <;> simp_all
      | app t loc x xs =>
        cases hs : knownListFuel fuel c xs env globals with
        | none => simp [knownFuel, hs] at h
        | some val =>
          rcases val with ⟨ys, sg⟩
          cases hx : knownFuel fuel c x env sg with
          | none => simp [knownFuel, hs, hx] at h
          | some val =>
            rcases val with ⟨xe, xa, xg⟩
            have es := ilist c xs env globals _ hs
            have ex := iexp c x env sg _ hx
            rw [knownExprTotal, ← es]
            dsimp only
            rw [← ex]
            dsimp only
            cases hd : decideInlineHOL c xa loc ys.length with
            | nothing =>
              simp [knownFuel, hs, hx, decideInlineFuel, hd] at h
              simp
              exact h.symm
            | annotate target =>
              simp [knownFuel, hs, hx, decideInlineFuel, hd] at h
              simp
              exact h.symm
            | letInline body =>
              cases hb : knownFuel fuel (decInlineFactor c) body (ys.map Prod.snd) xg with
              | none => simp [knownFuel, hs, hx, decideInlineFuel, hd, hb] at h
              | some val =>
                rcases val with ⟨be, ba, bg⟩
                have eb := iexp (decInlineFactor c) body (ys.map Prod.snd) xg _ hb
                simp [knownFuel, hs, hx, decideInlineFuel, hd, hb] at h
                dsimp only
                rw [← eb]
                dsimp only
                exact h.symm
      | letrec names loc vs fns body =>
        let clos := match loc with
          | none => List.replicate fns.length ValApprox.other
          | some loc => noInline loc fns
        simp only [knownFuel, List.append_assoc] at h
        change (do
          let fns2 ← fns.mapM (fun (arity, e) => do
            let (e, _, _) ← knownFuel fuel c e (List.replicate arity ValApprox.other ++ (clos ++ env)) globals
            pure (arity, e))
          let (body2, a, g) ← knownFuel fuel c body (clos ++ env) globals
          pure (Exp.letrec names loc none fns2 body2, a, g)) = some result at h
        cases hf : fns.mapM (fun (arity, e) => do
            let (e, _, _) ← knownFuel fuel c e (List.replicate arity ValApprox.other ++ (clos ++ env)) globals
            pure (arity, e)) with
        | none =>
          change (fns.mapM (fun p => (knownFuel fuel c p.2
            (List.replicate p.1 ValApprox.other ++ (clos ++ env)) globals).bind
              (fun z => some (p.1, z.1)))) = none at hf
          simp [hf] at h
        | some fs =>
          have ef := mapFuns_matches fuel iexp c fns clos env globals fs hf
          change (fns.mapM (fun p => (knownFuel fuel c p.2
            (List.replicate p.1 ValApprox.other ++ (clos ++ env)) globals).bind
              (fun z => some (p.1, z.1)))) = some fs at hf
          cases hb : knownFuel fuel c body (clos ++ env) globals with
          | none => simp [hf, hb] at h
          | some val =>
            rcases val with ⟨be, ba, bg⟩
            have eb := iexp c body (clos ++ env) globals _ hb
            simp [hf, hb] at h
            rw [knownExprTotal.eq_def]
            change result = (let fs := knownFunsTotal c fns clos env globals
              let (body2, a, g) := knownExprTotal c body (clos ++ env) globals
              (Exp.letrec names loc none fs body2, a, g))
            rw [← ef, ← eb]
            exact h.symm
    · intro c xs env globals result h
      cases xs with
      | nil => simpa [knownListFuel, knownListTotal] using h.symm
      | cons x xs =>
        cases hx : knownFuel fuel c x env globals with
        | none => simp [knownListFuel, hx] at h
        | some val =>
          rcases val with ⟨xe, xa, xg⟩
          cases hs : knownListFuel fuel c xs env xg with
          | none => simp [knownListFuel, hx, hs] at h
          | some val =>
            rcases val with ⟨es, eg⟩
            have ex := iexp c x env globals _ hx
            have esame := ilist c xs env xg _ hs
            simp [knownListFuel, hx, hs] at h
            rw [knownListTotal, ← ex]
            dsimp only
            rw [← esame]
            exact h.symm

end Flapjack.Compiler.Backend.ClosKnown
