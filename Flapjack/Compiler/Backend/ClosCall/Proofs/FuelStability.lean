import Flapjack.Compiler.Backend.ClosCall.Proofs.GroupClosed
import Flapjack.Compiler.Backend.ClosCall.Proofs.Total

/-! Stability of the bounded direct-call traversal. These are
Flapjack-specific adapter lemmas, not HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang

private def OptionRefines {α : Type} (x y : Option α) : Prop :=
  ∀ value, x = some value → y = some value

private theorem optionRefines_bind {α β : Type} (x y : Option α) (f h : α → Option β)
    (input : OptionRefines x y) (next : ∀ a, OptionRefines (f a) (h a)) :
    OptionRefines (x.bind f) (y.bind h) := by
  intro result run
  cases hx : x with
  | none => simp [hx] at run
  | some a =>
    have hy := input a hx
    have hf : f a = some result := by simpa [hx] using run
    simpa [hy] using next a result hf

private theorem optionRefines_refl {α : Type} (x : Option α) : OptionRefines x x := by
  intro _ h
  exact h

private theorem callsFuel_step_refines (fuel : Nat) :
    (∀ e state, OptionRefines (callsFuel fuel e state) (callsFuel (fuel + 1) e state)) ∧
    (∀ es state, OptionRefines (callsListFuel fuel es state) (callsListFuel (fuel + 1) es state)) := by
  induction fuel with
  | zero =>
    constructor
    · intro e state result run
      simp [callsFuel] at run
    · intro es state
      cases es <;> simp [callsListFuel, OptionRefines]
  | succ fuel ih =>
    obtain ⟨ihE, ihL⟩ := ih
    constructor
    · intro e state
      cases e <;> simp only [callsFuel]
      case var trace index => exact optionRefines_refl _
      case ifThenElse trace x y z =>
        apply optionRefines_bind _ _ _ _ (ihE x state)
        intro p
        apply optionRefines_bind _ _ _ _ (ihE y p.2)
        intro q
        apply optionRefines_bind _ _ _ _ (ihE z q.2)
        intro r
        exact optionRefines_refl _
      case «let» trace xs body =>
        apply optionRefines_bind _ _ _ _ (ihL xs state)
        intro p
        apply optionRefines_bind _ _ _ _ (ihE body p.2)
        intro q
        exact optionRefines_refl _
      case raise trace body =>
        apply optionRefines_bind _ _ _ _ (ihE body state)
        intro x
        exact optionRefines_refl _
      case tick trace body =>
        apply optionRefines_bind _ _ _ _ (ihE body state)
        intro x
        exact optionRefines_refl _
      case handle trace x y =>
        apply optionRefines_bind _ _ _ _ (ihE x state)
        intro p
        apply optionRefines_bind _ _ _ _ (ihE y p.2)
        intro q
        exact optionRefines_refl _
      case call trace ticks dest xs =>
        apply optionRefines_bind _ _ _ _ (ihL xs state)
        intro p
        exact optionRefines_refl _
      case op trace operation xs =>
        apply optionRefines_bind _ _ _ _ (ihL xs state)
        intro p
        exact optionRefines_refl _
      case app trace loc x xs =>
        apply optionRefines_bind _ _ _ _ (ihL xs state)
        intro p
        apply optionRefines_bind _ _ _ _ (ihE x p.2)
        intro q
        exact optionRefines_refl _
      case fn name loc ws arity body =>
        apply optionRefines_bind _ _ _ _ (ihE body (insertEach (loc.getD 0) 1 state))
        intro p
        rw [closedFuel_independent fuel (fuel + 1) (Exp.fn name loc ws arity p.1)]
        apply optionRefines_bind _ _ _ _ (optionRefines_refl _)
        intro closed
        cases closed with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          change OptionRefines
            ((callsFuel fuel body state).bind fun p => some (Exp.fn name loc ws arity p.1, p.2))
            ((callsFuel (fuel + 1) body state).bind fun p => some (Exp.fn name loc ws arity p.1, p.2))
          apply optionRefines_bind _ _ _ _ (ihE body state)
          intro q
          exact optionRefines_refl _
        | true => exact optionRefines_refl _
      case letrec names loc ws fns body =>
        apply optionRefines_bind _ _ _ _ (ihL (fns.map Prod.snd) (insertEach (loc.getD 0) fns.length state))
        intro p
        have checks := groupClosedFuel_independent fuel (fuel + 1) fns p.1
        simp only [groupClosedFuel] at checks
        rw [checks]
        apply optionRefines_bind _ _ _ _ (optionRefines_refl _)
        intro closed
        cases closed with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          apply optionRefines_bind _ _ _ _ (ihL (fns.map Prod.snd) state)
          intro q
          apply optionRefines_bind _ _ _ _ (ihE body q.2)
          intro r
          exact optionRefines_refl _
        | true =>
          simp only [↓reduceIte]
          apply optionRefines_bind _ _ _ _ (ihE body (codeList (loc.getD 0) ((fns.map Prod.fst).zip p.1) p.2))
          intro q
          exact optionRefines_refl _
    · intro es state
      cases es <;> simp only [callsListFuel]
      case nil => exact optionRefines_refl _
      case cons x xs =>
        apply optionRefines_bind _ _ _ _ (ihE x state)
        intro p
        apply optionRefines_bind _ _ _ _ (ihL xs p.2)
        intro q
        exact optionRefines_refl _

/-- Increasing traversal fuel preserves any successful expression result.
This is Flapjack-specific infrastructure for the bounded adapter. -/
theorem callsFuel_success_mono (fuel extra : Nat) (e : Exp) (state : State) (result : Exp × State)
    (run : callsFuel fuel e state = some result) :
    callsFuel (fuel + extra) e state = some result := by
  induction extra with
  | zero => simpa using run
  | succ extra ih =>
    simpa only [Nat.add_succ] using (callsFuel_step_refines (fuel + extra)).1 e state result ih

/-- Increasing traversal fuel preserves any successful list result. This is
Flapjack-specific infrastructure for the bounded adapter. -/
theorem callsListFuel_success_mono (fuel extra : Nat) (es : List Exp) (state : State)
    (result : List Exp × State) (run : callsListFuel fuel es state = some result) :
    callsListFuel (fuel + extra) es state = some result := by
  induction extra with
  | zero => simpa using run
  | succ extra ih =>
    simpa only [Nat.add_succ] using (callsFuel_step_refines (fuel + extra)).2 es state result ih

/-- Successful direct-call list traversals agree even when run at different
fuel values. This is Flapjack-specific adapter infrastructure. -/
theorem callsListFuel_success_agree (left right : Nat) (es : List Exp) (state : State)
    (x y : List Exp × State) (hx : callsListFuel left es state = some x)
    (hy : callsListFuel right es state = some y) : x = y := by
  have leftHigh : callsListFuel (left + right) es state = some x :=
    callsListFuel_success_mono left right es state x hx
  have rightHigh : callsListFuel (left + right) es state = some y := by
    simpa [Nat.add_comm] using callsListFuel_success_mono right left es state y hy
  rw [leftHigh] at rightHigh
  exact Option.some.inj rightHigh

/-- Every successful bounded traversal is a successful raw traversal at
either the requested fuel or the structural retry fuel. This is
Flapjack-specific adapter infrastructure. -/
theorem callsListBounded_success_run (fuel : Nat) (es : List Exp) (state : State)
    (result : List Exp × State) (run : callsListBounded fuel es state = some result) :
    ∃ actualFuel, callsListFuel actualFuel es state = some result := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es state with
  | none =>
    exact ⟨max fuel (listBudget es + 1), by simpa [first] using run⟩
  | some value =>
    have eq : value = result := by simpa [first] using run
    subst value
    exact ⟨fuel, first⟩

/-- The production retry wrapper returns the same result for every initial
fuel. This is Flapjack-specific adapter infrastructure. -/
theorem callsListBounded_independent (left right : Nat) (es : List Exp) (state : State) :
    callsListBounded left es state = callsListBounded right es state := by
  obtain ⟨x, hx⟩ := callsListBounded_succeeds left es state
  obtain ⟨y, hy⟩ := callsListBounded_succeeds right es state
  obtain ⟨leftFuel, leftRun⟩ := callsListBounded_success_run left es state x hx
  obtain ⟨rightFuel, rightRun⟩ := callsListBounded_success_run right es state y hy
  have eq := callsListFuel_success_agree leftFuel rightFuel es state x y leftRun rightRun
  simp [hx, hy, eq]

end Flapjack.Compiler.Backend.ClosCall
