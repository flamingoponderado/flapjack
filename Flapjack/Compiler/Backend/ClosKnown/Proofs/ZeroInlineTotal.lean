import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineTotal
import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineDecrease
import Flapjack.Compiler.Backend.ClosKnown.Proofs.OperationTotal
import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartTotal
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Total
import Flapjack.Compiler.Backend.ClosTicks.Proofs.Total
import Flapjack.Compiler.Backend.ClosLetop.Proofs.Total

/-! Structural totality of the executable known-closure traversal when
inlining is disabled. This is not a HOL correctness theorem. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

theorem knownFuel_zeroInline_succeeds (fuel : Nat) :
    (∀ c e env globals, c.inlineFactor = 0 → expBudget e < fuel →
      ∃ result, knownFuel fuel c e env globals = some result) ∧
    (∀ c xs env globals, c.inlineFactor = 0 → listBudget xs < fuel →
      ∃ result, knownListFuel fuel c xs env globals = some result) := by
  induction fuel with
  | zero => constructor <;> intros <;> omega
  | succ fuel ih =>
    rcases ih with ⟨iexp, ilist⟩
    constructor
    · intro c e env globals hz bound
      cases e with
      | var t v => exact ⟨_, rfl⟩
      | raise t x =>
        have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨x', a, g⟩, hx⟩ := iexp c x env globals hz bx
        exact ⟨_, by simp [knownFuel, hx]; rfl⟩
      | tick t x =>
        have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨x', a, g⟩, hx⟩ := iexp c x env globals hz bx
        exact ⟨_, by simp [knownFuel, hx]; rfl⟩
      | ifThenElse t x y z =>
        have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
        have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
        have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨x', a, gx⟩, hx⟩ := iexp c x env globals hz bx
        obtain ⟨⟨y', b, gy⟩, hy⟩ := iexp c y env gx hz by'
        obtain ⟨⟨z', d, gz⟩, hzt⟩ := iexp c z env gy hz bz
        obtain ⟨merged, hm⟩ := mergeBounded_succeeds fuel b d
        exact ⟨_, by simp [knownFuel, hx, hy, hzt, hm]; rfl⟩
      | handle t x y =>
        have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
        have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨x', a, gx⟩, hx⟩ := iexp c x env globals hz bx
        obtain ⟨⟨y', b, gy⟩, hy⟩ := iexp c y (.other :: env) gx hz by'
        obtain ⟨merged, hm⟩ := mergeBounded_succeeds fuel a b
        exact ⟨_, by simp [knownFuel, hx, hy, hm]; rfl⟩
      | «let» t xs body =>
        have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨xs', gx⟩, hx⟩ := ilist c xs env globals hz bs
        obtain ⟨⟨body', a, gb⟩, hb⟩ := iexp c body (xs'.map Prod.snd ++ env) gx hz bb
        exact ⟨_, by simp [knownFuel, hx, hb]; rfl⟩
      | call t n dest xs =>
        have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨xs', gx⟩, hx⟩ := ilist c xs env globals hz bs
        exact ⟨_, by simp [knownFuel, hx]; rfl⟩
      | op t op xs =>
        have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨xs', gx⟩, hx⟩ := ilist c xs env globals hz bs
        obtain ⟨⟨a, ga⟩, ha⟩ := knownOpFuel_succeeds fuel op (xs'.map Prod.snd).reverse gx
        obtain ⟨result, hs⟩ := ClosOp.smartFuel_succeeds fuel t op (xs'.map Prod.fst)
        simp [knownFuel, hx, ha]
        repeat' (first | split | exact ⟨_, by simp [hs]; rfl⟩)
      | app t loc x xs =>
        have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
        have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨xs', gx⟩, hx⟩ := ilist c xs env globals hz bs
        obtain ⟨⟨x', a, ga⟩, ha⟩ := iexp c x env gx hz bx
        obtain ⟨decision, hd⟩ := decideInlineFuel_succeeds fuel c a loc xs'.length
        cases decision with
        | nothing => exact ⟨_, by simp [knownFuel, hx, ha, hd]; rfl⟩
        | annotate target => exact ⟨_, by simp [knownFuel, hx, ha, hd]; rfl⟩
        | letInline body =>
          have positive := inlineFactor_positive_of_letInline fuel c a loc xs'.length body hd
          omega
      | fn name loc vs arity body =>
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        obtain ⟨⟨body', a, gb⟩, hb⟩ := iexp c body (List.replicate arity .other ++ env) globals hz bb
        cases loc with
        | none => exact ⟨_, by simp [knownFuel, hb]; rfl⟩
        | some loc =>
          obtain ⟨approx, ha⟩ := closApproxFuel_succeeds fuel c.inlineMaxBodySize loc arity body
          exact ⟨_, by simp [knownFuel, hb, ha]; rfl⟩
      | letrec names loc vs fns body =>
        have bf : funsBudget fns < fuel := by simp_all [expBudget] <;> omega
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        let clos := match loc with
          | none => List.replicate fns.length ValApprox.other
          | some loc => noInline loc fns
        obtain ⟨fns', hf⟩ := mapM_succeeds fns (fun p => do
          let (e, _, _) ← knownFuel fuel c p.2 (List.replicate p.1 .other ++ (clos ++ env)) globals
          pure (p.1, e)) (by
            intro p hp
            obtain ⟨arity, e⟩ := p
            have be : expBudget e < fuel := by
              have := fun_member_budget_lt fns arity e hp
              omega
            obtain ⟨⟨e', a, g⟩, he⟩ := iexp c e (List.replicate arity .other ++ (clos ++ env)) globals hz be
            exact ⟨_, by simp [he]; rfl⟩)
        obtain ⟨⟨body', a, gb⟩, hb⟩ := iexp c body (clos ++ env) globals hz bb
        refine ⟨(.letrec names loc none fns' body', a, gb), ?_⟩
        simp only [knownFuel, List.append_assoc]
        change (do
          let fns' ← fns.mapM (fun (p : Nat × Exp) => do
            let (e, _, _) ← knownFuel fuel c p.2 (List.replicate p.1 ValApprox.other ++ (clos ++ env)) globals
            pure (p.1, e))
          let (body', a, gb) ← knownFuel fuel c body (clos ++ env) globals
          pure (Exp.letrec names loc none fns' body', a, gb)) = _
        rw [hf]
        simp [hb]
    · intro c xs env globals hz bound
      cases xs with
      | nil => exact ⟨_, rfl⟩
      | cons x xs =>
        have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
        have bs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
        obtain ⟨⟨x', a, gx⟩, hx⟩ := iexp c x env globals hz bx
        obtain ⟨⟨xs', gs⟩, hs⟩ := ilist c xs env gx hz bs
        exact ⟨_, by simp [knownListFuel, hx, hs]; rfl⟩

/-- The production retry succeeds whenever inlining is disabled. -/
theorem knownListBounded_zeroInline_succeeds (fuel : Nat) (c : Config) (xs : List Exp)
    (env : List ValApprox) (globals : Spt ValApprox) (hz : c.inlineFactor = 0) :
    ∃ result, knownListBounded fuel c xs env globals = some result := by
  cases h : knownListFuel fuel c xs env globals with
  | some result => exact ⟨result, by simp [knownListBounded, h]⟩
  | none =>
    have bound : listBudget xs < max fuel (listBudget xs + 1) := by omega
    obtain ⟨result, done⟩ := (knownFuel_zeroInline_succeeds _).2 c xs env globals hz bound
    exact ⟨result, by simp [knownListBounded, h, hz, done]⟩

/-- A successful first traversal is returned unchanged. -/
theorem knownListBounded_eq_of_success (fuel : Nat) (c : Config) (xs : List Exp)
    (env : List ValApprox) (globals : Spt ValApprox) (result : List (Exp × ValApprox) × Spt ValApprox)
    (h : knownListFuel fuel c xs env globals = some result) :
    knownListBounded fuel c xs env globals = some result := by
  simp [knownListBounded, h]

/-- The complete executable known-closure pass succeeds when inlining is disabled. -/
theorem compileFuel_zeroInline_succeeds (fuel : Nat) (c : Config) (es : List Exp)
    (hz : c.inlineFactor = 0) :
    ∃ result, compileFuel fuel (some c) es = some result := by
  obtain ⟨prepared, hp⟩ := mapM_succeeds es (ClosFvs.removeBounded fuel 0) (by
    intro e _; exact ClosFvs.removeBounded_succeeds fuel 0 e)
  obtain ⟨⟨known, globals⟩, hk⟩ := knownListBounded_zeroInline_succeeds fuel c prepared [] .ln hz
  obtain ⟨finished, hf⟩ := mapM_succeeds known (fun p => do
    let e ← ClosTicks.removeBounded fuel p.1
    ClosLetop.compileBounded fuel e) (by
      intro p _
      obtain ⟨e, a⟩ := p
      obtain ⟨unticked, hu⟩ := ClosTicks.removeBounded_succeeds fuel e
      obtain ⟨result, hr⟩ := ClosLetop.compileBounded_succeeds fuel unticked
      exact ⟨result, by simp [hu, hr]⟩)
  change known.mapM (fun p => (ClosTicks.removeBounded fuel p.1).bind
    (ClosLetop.compileBounded fuel)) = some finished at hf
  exact ⟨(some { c with valApproxSpt := globals }, finished), by
    simp [compileFuel, hp, hk, hf]⟩

end Flapjack.Compiler.Backend.ClosKnown
