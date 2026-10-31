import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Integer
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply
import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply

/-! Integer primitive correspondence for the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- A source integer can only be related to the same target integer. -/
theorem vRel_number_inv {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {n : Int} {target : BvlSem.Value} (related : vRel maxApp f refs code (.number n) target) :
    target = .number n := by
  cases related with
  | number => rfl
  | closure _ closure => cases closure
  | partialClosure _ _ _ _ _ added _ closure => cases closure <;> simp [addArgs] at added

/-- Related lists of source numbers contain exactly the corresponding target
numbers. -/
theorem vRel_numbers_inv {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (numbers : List Int) (target : List BvlSem.Value)
    (related : List.Forall₂ (vRel maxApp f refs code) (numbers.map ClosSem.Value.number) target) :
    target = numbers.map BvlSem.Value.number := by
  induction numbers generalizing target with
  | nil => cases related; rfl
  | cons n rest ih =>
    cases related with
    | cons head tail =>
      have headEq := vRel_number_inv head
      have tailEq := ih _ tail
      simp [headEq, tailEq]

/-- Boolean constants retain their value relation through tag translation. -/
theorem vRel_bool {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)} (b : Bool) :
    vRel maxApp f refs code (ClosSem.boolValue b) (BvlSem.boolValue b) := by
  cases b <;> exact .block .nil

/-- Successful integer primitives on numeric arguments produce related values. -/
theorem doIntApp_numbers_rel {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (op : ClosLang.IntOp) (args : List Int) :
    match ClosSem.doIntApp op (args.map ClosSem.Value.number),
        BvlSem.doIntApp op (args.map BvlSem.Value.number) with
    | none, none => True
    | some source, some target => vRel maxApp f refs code source target
    | _, _ => False := by
  cases op <;> cases args with
  | nil => simp [ClosSem.doIntApp, BvlSem.doIntApp, vRel.number]
  | cons a args =>
    cases args with
    | nil =>
      simp only [List.map, ClosSem.doIntApp, BvlSem.doIntApp] <;>
        (try split_ifs) <;> first | exact True.intro | exact vRel_bool _
    | cons b args =>
      cases args <;> simp only [List.map, ClosSem.doIntApp, BvlSem.doIntApp] <;>
        (try split_ifs) <;> first | exact True.intro | exact vRel.number _ | exact vRel_bool _

/-- Related numeric arguments yield related results whenever the source
integer primitive succeeds. -/
theorem doIntApp_related_numbers {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (op : ClosLang.IntOp) (args : List Int) (targets : List BvlSem.Value)
    (related : List.Forall₂ (vRel maxApp f refs code) (args.map ClosSem.Value.number) targets)
    (source : ClosSem.Value)
    (success : ClosSem.doIntApp op (args.map ClosSem.Value.number) = some source) :
    ∃ target, BvlSem.doIntApp op targets = some target ∧ vRel maxApp f refs code source target := by
  have targetEq := vRel_numbers_inv args targets related
  subst targets
  have results := doIntApp_numbers_rel (maxApp := maxApp) (f := f) (refs := refs) (code := code) op args
  rw [success] at results
  cases targetRun : BvlSem.doIntApp op (args.map BvlSem.Value.number) with
  | none => simp [targetRun] at results
  | some target => exact ⟨target, rfl, by simpa [targetRun] using results⟩

/-- A successful integer operation can only receive numeric arguments. -/
theorem doIntApp_success_args (op : ClosLang.IntOp) (args : List ClosSem.Value)
    (result : ClosSem.Value) (success : ClosSem.doIntApp op args = some result) :
    ∃ numbers : List Int, args = numbers.map ClosSem.Value.number := by
  cases args with
  | nil => exact ⟨[], rfl⟩
  | cons a args =>
    cases args with
    | nil =>
      cases a <;> cases op <;> simp_all [ClosSem.doIntApp]
      all_goals exact ⟨[_], rfl⟩
    | cons b args =>
      cases args with
      | nil =>
        cases a <;> cases b <;> cases op <;> simp_all [ClosSem.doIntApp]
        all_goals exact ⟨[_, _], rfl⟩
      | cons c rest => cases op <;> simp [ClosSem.doIntApp] at success

/-- Successful integer operations preserve the value relation for arbitrary
related argument lists. -/
theorem doIntApp_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (op : ClosLang.IntOp) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (related : List.Forall₂ (vRel maxApp f refs code) args targets)
    (source : ClosSem.Value) (success : ClosSem.doIntApp op args = some source) :
    ∃ target, BvlSem.doIntApp op targets = some target ∧ vRel maxApp f refs code source target := by
  obtain ⟨numbers, rfl⟩ := doIntApp_success_args op args source success
  exact doIntApp_related_numbers op numbers targets related source success

/-- A successful integer dispatch preserves both states and produces related
values. This is a component of the ordinary-operation simulation, not the
full closure-to-BVL correctness theorem. -/
theorem doApp_integer_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (op : ClosLang.IntOp) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (source : ClosSem.Value)
    (success : ClosSem.doApp (.intOp op) args s = .val (source, next)) :
    ∃ target, BvlSem.doApp (.intOp op) targets t = .val (target, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code source target := by
  cases run : ClosSem.doIntApp op args with
  | none => simp [ClosSem.doApp, ClosSem.applyNumeric, run] at success
  | some value =>
    simp [ClosSem.doApp, ClosSem.applyNumeric, run] at success
    obtain ⟨rfl, rfl⟩ := success
    obtain ⟨target, targetRun, valueRel⟩ := doIntApp_related op args targets related value run
    exact ⟨target, by simp [BvlSem.doApp, BvlSem.applyNumeric, targetRun], rfl, valueRel⟩

end Flapjack.Compiler.Backend.ClosToBvl
