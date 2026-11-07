import Flapjack.Compiler.Backend.BviTmc.Proofs.ClockHypothesis

/-! Safety of bindings produced by recursive-call extraction. -/
namespace Flapjack.Compiler.Backend.BviTmc.ExtractionSafety
open BviTmc Bvi

private theorem weight_append (xs ys : List Bvi.Exp) :
    BviSem.expsWeight (xs ++ ys) = BviSem.expsWeight xs + BviSem.expsWeight ys := by
  induction xs with
  | nil => simp [BviSem.expsWeight]
  | cons x xs ih => simp [BviSem.expsWeight, ih, Nat.add_assoc]

mutual
/-- Flapjack infrastructure: extraction from a safe expression produces
only safe bindings. The corresponding local HOL conjunct remains to be
reviewed against its inferred carrier and statement. -/
theorem extractOne_safe (n loc tag : Nat) (e : Bvi.Exp) (bs : List Bvi.Exp) (kind : Sum (List Nat) CallBlock)
    (run : extractOneSource n loc tag e = some (bs, kind)) (safe : noMutcons e) :
    ∀ x ∈ bs, noMutcons x := by
  cases e with
  | call ticks dest args handler =>
    simp only [extractOneSource, callToBlockSource] at run
    split at run
    next =>
      cases h : bind 0 args with
      | mk indices last =>
        simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨eq, _⟩ := run
        subst bs
        intro x member
        rw [noMutcons.eq_def] at safe
        dsimp only at safe
        exact safe.1 ⟨x, member⟩
    next => simp at run
  | op op args =>
    cases op with
    | blockOp block =>
      cases block with
      | cons childTag =>
        simp only [extractOneSource] at run
        cases h : extractListSource n loc childTag args with
        | none => simp [h] at run
        | some pair =>
          obtain ⟨bindings, extractedKind⟩ := pair
          cases extractedKind with
          | inl vars =>
            simp only [h] at run
            split at run <;> simp_all
            rcases run with ⟨rfl, _⟩
            simpa using safe
          | inr child =>
            simp only [noMutcons] at safe
            have childSafe := extractList_safe n loc childTag args bindings (.inr child) h
              (fun x member => safe.2 ⟨x, member⟩)
            simp only [h, Option.some.injEq, Prod.mk.injEq] at run
            obtain ⟨rfl, _⟩ := run
            exact childSafe
      | _ => simp only [extractOneSource] at run; split at run <;> simp_all; rcases run with ⟨rfl, _⟩; simpa using safe
    | _ => simp only [extractOneSource] at run; split at run <;> simp_all; rcases run with ⟨rfl, _⟩; simpa using safe
  | _ => simp only [extractOneSource] at run; split at run <;> simp_all; rcases run with ⟨rfl, _⟩; simpa using safe
termination_by expBudget e
decreasing_by all_goals simp_all [expBudget]

/-- Flapjack infrastructure: extraction from a safe argument list produces
only safe bindings. -/
theorem extractList_safe (n loc tag : Nat) (args bs : List Bvi.Exp) (kind : Sum (List Nat) CallBlock)
    (run : extractListSource n loc tag args = some (bs, kind)) (safe : ∀ x ∈ args, noMutcons x) :
    ∀ x ∈ bs, noMutcons x := by
  cases args with
  | nil => simp [extractListSource] at run; simp_all
  | cons x xs =>
    cases xs with
    | nil =>
      apply extractOne_safe n loc tag x bs kind (by simpa [extractListSource] using run)
      exact safe x (by simp)
    | cons y ys =>
      simp only [extractListSource] at run
      cases tail : extractListSource n loc tag (y :: ys) with
      | none => simp [tail] at run
      | some pair =>
        obtain ⟨tailBs, tailKind⟩ := pair
        have tailSafe := extractList_safe n loc tag (y :: ys) tailBs tailKind tail
          (fun x member => safe x (by simp [member]))
        cases tailKind with
        | inl vars =>
          cases first : extractOneSource n loc tag x with
          | none => simp [tail, first] at run
          | some pair =>
            obtain ⟨firstBs, firstKind⟩ := pair
            have firstSafe := extractOne_safe n loc tag x firstBs firstKind first (safe x (by simp))
            cases firstKind with
            | inl indices =>
              simp only [tail, first] at run
              split at run <;> simp_all
              rcases run with ⟨rfl, _⟩
              intro item member
              rcases List.mem_append.mp member with member | member
              · exact firstSafe item member
              · exact tailSafe item member
            | inr firstCb =>
              cases firstCb with
              | rCall ticks args => simp [tail, first] at run
              | callBlock t left child right =>
                cases left with
                | cons a rest => simp [tail, first] at run
                | nil =>
                  cases right with
                  | cons a rest => simp [tail, first] at run
                  | nil =>
                    simp only [tail, first, Option.some.injEq, Prod.mk.injEq] at run
                    rcases run with ⟨rfl, _⟩
                    intro item member
                    rcases List.mem_append.mp member with member | member
                    · exact firstSafe item member
                    · exact tailSafe item member
        | inr cb =>
          cases cb with
          | rCall ticks vars => simp [tail, shiftBlock] at run
          | callBlock t left child right =>
            simp only [tail, shiftBlock, Option.some.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            intro item member
            rcases List.mem_cons.mp member with rfl | member
            · exact safe item (by simp)
            · exact tailSafe item member
termination_by listBudget args
decreasing_by all_goals simp_all only [listBudget]; omega
end

mutual
/-- Flapjack infrastructure: extraction from one expression produces a
binding list whose structural weight is at most that expression's weight
plus its list constructor. -/
theorem extractOne_weight (n loc tag : Nat) (e : Bvi.Exp) (bs : List Bvi.Exp)
    (kind : Sum (List Nat) CallBlock) (run : extractOneSource n loc tag e = some (bs, kind)) :
    BviSem.expsWeight bs ≤ BviSem.expWeight e + 1 := by
  cases e with
  | call ticks dest args handler =>
    simp only [extractOneSource, callToBlockSource] at run
    split at run
    next condition =>
      cases h : bind 0 args with
      | mk indices last =>
        simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨eq, _⟩ := run
        subst bs
        rcases condition with ⟨_, rfl⟩
        simp [BviSem.expWeight]
        omega
    next => simp at run
  | op op args =>
    cases op with
    | blockOp block =>
      cases block with
      | cons childTag =>
        simp only [extractOneSource] at run
        cases h : extractListSource n loc childTag args with
        | none => simp [h] at run
        | some pair =>
          obtain ⟨bindings, extractedKind⟩ := pair
          cases extractedKind with
          | inl vars =>
            simp only [h] at run
            split at run <;> simp_all
            rcases run with ⟨rfl, _⟩
            simp [BviSem.expsWeight]
            omega
          | inr child =>
            have bound := extractList_weight n loc childTag args bindings (.inr child) h
            simp only [h, Option.some.injEq, Prod.mk.injEq] at run
            obtain ⟨rfl, _⟩ := run
            simp only [BviSem.expWeight]
            omega
      | _ => simp only [extractOneSource] at run; split at run <;> simp_all; rcases run with ⟨rfl, _⟩; simp [BviSem.expsWeight]; omega
    | _ => simp only [extractOneSource] at run; split at run <;> simp_all; rcases run with ⟨rfl, _⟩; simp [BviSem.expsWeight]; omega
  | _ => simp only [extractOneSource] at run; split at run <;> simp_all; rcases run with ⟨rfl, _⟩; simp [BviSem.expsWeight]; omega
termination_by expBudget e
decreasing_by all_goals simp_all [expBudget]

/-- Flapjack infrastructure: extracted list bindings do not exceed the
source argument list's structural weight. -/
theorem extractList_weight (n loc tag : Nat) (args bs : List Bvi.Exp) (kind : Sum (List Nat) CallBlock)
    (run : extractListSource n loc tag args = some (bs, kind)) :
    BviSem.expsWeight bs ≤ BviSem.expsWeight args := by
  cases args with
  | nil => simp [extractListSource] at run; simp_all [BviSem.expsWeight]
  | cons x xs =>
    cases xs with
    | nil =>
      have bound := extractOne_weight n loc tag x bs kind (by simpa [extractListSource] using run)
      simp [BviSem.expsWeight]
      omega
    | cons y ys =>
      simp only [extractListSource] at run
      cases tail : extractListSource n loc tag (y :: ys) with
      | none => simp [tail] at run
      | some pair =>
        obtain ⟨tailBs, tailKind⟩ := pair
        have tailBound := extractList_weight n loc tag (y :: ys) tailBs tailKind tail
        cases tailKind with
        | inl vars =>
          cases first : extractOneSource n loc tag x with
          | none => simp [tail, first] at run
          | some pair =>
            obtain ⟨firstBs, firstKind⟩ := pair
            have firstBound := extractOne_weight n loc tag x firstBs firstKind first
            cases firstKind with
            | inl indices =>
              simp only [tail, first] at run
              split at run <;> simp_all
              rcases run with ⟨rfl, _⟩
              simp only [weight_append, BviSem.expsWeight] at *
              omega
            | inr firstCb =>
              cases firstCb with
              | rCall ticks args => simp [tail, first] at run
              | callBlock t left child right =>
                cases left with
                | cons a rest => simp [tail, first] at run
                | nil =>
                  cases right with
                  | cons a rest => simp [tail, first] at run
                  | nil =>
                    simp only [tail, first, Option.some.injEq, Prod.mk.injEq] at run
                    rcases run with ⟨rfl, _⟩
                    simp only [weight_append, BviSem.expsWeight] at *
                    omega
        | inr cb =>
          cases cb with
          | rCall ticks vars => simp [tail, shiftBlock] at run
          | callBlock t left child right =>
            simp only [tail, shiftBlock, Option.some.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            simp only [BviSem.expsWeight] at *
            omega
termination_by listBudget args
decreasing_by all_goals simp_all only [listBudget]; omega
end

/-- Flapjack infrastructure: successful top-level recursive-call extraction
preserves the no-mutable-allocation property of every generated binding.
The exact HOL theorem remains untagged pending its carrier review. -/
theorem toBlock_safe (n loc : Nat) (e : Bvi.Exp) (bs : List Bvi.Exp) (cb : CallBlock)
    (run : toBlockSource n loc e = some (bs, cb)) (safe : noMutcons e) :
    ∀ x ∈ bs, noMutcons x := by
  rcases toBlock_cases n loc e bs cb run with ⟨tag, args, left, child, right, rfl, rfl⟩ |
    ⟨ticks, args, vars, rfl, rfl⟩
  · simp only [toBlockSource] at run
    cases h : extractListSource n loc tag args with
    | none => simp [h] at run
    | some pair =>
      obtain ⟨bindings, kind⟩ := pair
      cases kind with
      | inl vs => simp [h] at run
      | inr block =>
        simp only [h, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, _⟩ := run
        rw [noMutcons.eq_def] at safe
        dsimp only at safe
        exact extractList_safe n loc tag args bindings (.inr block) h (fun x member => safe.2 ⟨x, member⟩)
  · simp only [toBlockSource, callToBlockSource] at run
    split at run
    next =>
      cases h : bind 0 args with
      | mk indices last =>
        simp only [h, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨eq, _⟩ := run
        subst bs
        rw [noMutcons.eq_def] at safe
        dsimp only at safe
        intro x member
        exact safe.1 ⟨x, member⟩
    next => simp at run

/-- Flapjack infrastructure: top-level extraction strictly decreases the BVI
structural weight. Source review is required before tagging the HOL theorem. -/
theorem toBlock_weight (n loc : Nat) (e : Bvi.Exp) (bs : List Bvi.Exp) (cb : CallBlock)
    (run : toBlockSource n loc e = some (bs, cb)) : BviSem.expsWeight bs < BviSem.expWeight e := by
  rcases toBlock_cases n loc e bs cb run with ⟨tag, args, left, child, right, rfl, rfl⟩ |
    ⟨ticks, args, vars, rfl, rfl⟩
  · simp only [toBlockSource] at run
    cases h : extractListSource n loc tag args with
    | none => simp [h] at run
    | some pair =>
      obtain ⟨bindings, kind⟩ := pair
      cases kind with
      | inl vs => simp [h] at run
      | inr block =>
        have bound := extractList_weight n loc tag args bindings (.inr block) h
        simp only [h, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, _⟩ := run
        simp only [BviSem.expWeight]
        omega
  · simp only [toBlockSource, callToBlockSource] at run
    split at run
    next =>
      cases h : bind 0 args with
      | mk indices last =>
        simp only [h, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨eq, _⟩ := run
        subst bs
        simp [BviSem.expWeight]
    next => simp at run

/-- Flapjack infrastructure: the extracted singleton case follows from the
same-clock smaller-list induction and the smaller-clock singleton induction.
The full induction and the remaining expression cases are still separate. -/
theorem evaluate_extracted_from_structural_induction {C F : Type} (loc : Nat) (cb : CallBlock)
    (e : Bvi.Exp) (bindings : List Bvi.Exp) (source : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (env1 env2 : List BvlSem.Value) (opt : Bool)
    (f : HolFiniteMapExact Nat Nat) (result : BviSem.BviResult) (final : BviSem.BviState (Nat × C) F)
    (run : BviSem.evaluate [e] env1 source = (result, final))
    (extracted : toBlockSource env1.length loc e = some (bindings, cb))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons e)
    (environments : envRel opt f env1 env2) (_states : stateRel f source target)
    (listIH : ∀ xs, BviSem.expsWeight xs < BviSem.expWeight e → (∀ x ∈ xs, noMutcons x) →
      ∀ r mid, BviSem.evaluate xs env1 source = (r, mid) → r ≠ .err (.abort .typeError) →
        ListSimulation.Core xs env2 f target r mid)
    (clockIH : ClockHypothesis.SmallerClockIH (C := C) (F := F) source.clock) :
    ClockHypothesis.SingletonPost e source target env1 env2 opt f loc result final := by
  have bindingsIH : ∀ r mid, BviSem.evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → ListSimulation.Core bindings env2 f target r mid :=
    listIH bindings (toBlock_weight env1.length loc e bindings cb extracted)
      (toBlock_safe env1.length loc e bindings cb extracted safe)
  exact ClockHypothesis.evaluate_extracted_from_smaller_clock loc cb e bindings source target env1 env2 opt f
    result final run extracted notTypeError environments bindingsIH clockIH

end Flapjack.Compiler.Backend.BviTmc.ExtractionSafety
