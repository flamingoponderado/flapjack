module

public import Flapjack.Compiler.Backend.ClosMti
public import Flapjack.Compiler.Backend.ClosLang.GeneratedSize

@[expose] public section

/-! Size and monotonicity lemmas for argument and application collection. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang

/-- Collecting function arguments never increases the combined size. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "collect_args_size"]
theorem collect_args_size (maxApp numArgs : Nat) (e : Exp) (numArgs' : Nat) (e' : Exp)
    (run : (numArgs', e') = collectArgs maxApp numArgs e) :
    numArgs' + expSizeHOL e' ≤ numArgs + expSizeHOL e := by
  revert numArgs e numArgs' e' run
  refine collectArgs.induct maxApp (fun numArgs e => ∀ numArgs' e',
    (numArgs', e') = collectArgs maxApp numArgs e →
      numArgs' + expSizeHOL e' ≤ numArgs + expSizeHOL e) ?_ ?_ ?_
  · intro numArgs t more body cond ih numArgs' e' run
    simp only [collectArgs, cond, if_true] at run
    have step := ih numArgs' e' run
    simp only [expSizeHOL]
    omega
  · intro numArgs t more body cond numArgs' e' run
    simp only [collectArgs, cond, if_false, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    omega
  · intro numArgs e other numArgs' e' run
    simp only [collectArgs] at run
    obtain ⟨rfl, rfl⟩ := run
    omega

/-- Collecting function arguments never decreases the argument count. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "collect_args_more"]
theorem collect_args_more (maxApp numArgs : Nat) (e : Exp) (numArgs' : Nat) (e' : Exp)
    (run : (numArgs', e') = collectArgs maxApp numArgs e) : numArgs ≤ numArgs' := by
  revert numArgs e numArgs' e' run
  refine collectArgs.induct maxApp (fun numArgs e => ∀ numArgs' e',
    (numArgs', e') = collectArgs maxApp numArgs e → numArgs ≤ numArgs') ?_ ?_ ?_
  · intro numArgs t more body cond ih numArgs' e' run
    simp only [collectArgs, cond, if_true] at run
    have step := ih numArgs' e' run
    omega
  · intro numArgs t more body cond numArgs' e' run
    simp only [collectArgs, cond, if_false, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    omega
  · intro numArgs e other numArgs' e' run
    simp only [collectArgs] at run
    obtain ⟨rfl, rfl⟩ := run
    omega

/-- A zero argument count is only reported for a zero starting count. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "collect_args_zero"]
theorem collect_args_zero (maxApp numArgs : Nat) (e : Exp) (e' : Exp)
    (run : collectArgs maxApp numArgs e = (0, e')) : numArgs = 0 := by
  revert numArgs e e' run
  refine collectArgs.induct maxApp (fun numArgs e => ∀ e',
    collectArgs maxApp numArgs e = (0, e') → numArgs = 0) ?_ ?_ ?_
  · intro numArgs t more body cond ih e' run
    simp only [collectArgs, cond, if_true] at run
    have step := ih e' run
    omega
  · intro numArgs t more body cond e' run
    simp only [collectArgs, cond, if_false, Prod.mk.injEq] at run
    obtain ⟨zero, _⟩ := run
    omega
  · intro numArgs e other e' run
    simp only [collectArgs] at run
    obtain ⟨zero, _⟩ := run
    omega

/-- Argument lists concatenate additively under the generated list size. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "exp3_size_append"]
theorem exp3_size_append (es1 es2 : List Exp) :
    expListSizeHOL (es1 ++ es2) = expListSizeHOL es1 + expListSizeHOL es2 := by
  induction es1 with
  | nil => simp [expListSizeHOL]
  | cons e rest ih =>
    simp only [List.cons_append, expListSizeHOL, ih]
    omega

/-- Collecting nested applications never decreases the argument count. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "collect_apps_more"]
theorem collect_apps_more (maxApp : Nat) (args : List Exp) (e : Exp) (args' : List Exp)
    (e' : Exp) (run : (args', e') = collectApps maxApp args e) :
    args.length ≤ args'.length := by
  revert args e args' e' run
  refine collectApps.induct maxApp (fun args e => ∀ args' e',
    (args', e') = collectApps maxApp args e → args.length ≤ args'.length) ?_ ?_ ?_
  · intro args t body more cond ih args' e' run
    simp only [collectApps, cond, if_true] at run
    have step := ih args' e' run
    simp only [List.length_append] at step
    omega
  · intro args t body more cond args' e' run
    simp only [collectApps, cond, if_false, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    omega
  · intro args e other args' e' run
    simp only [collectApps] at run
    obtain ⟨rfl, rfl⟩ := run
    omega

/-- Collecting nested applications never increases the combined size. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "collect_apps_size"]
theorem collect_apps_size (maxApp : Nat) (args : List Exp) (e : Exp) (args' : List Exp)
    (e' : Exp) (run : (args', e') = collectApps maxApp args e) :
    expListSizeHOL args' + expSizeHOL e' ≤ expListSizeHOL args + expSizeHOL e := by
  revert args e args' e' run
  refine collectApps.induct maxApp (fun args e => ∀ args' e',
    (args', e') = collectApps maxApp args e →
      expListSizeHOL args' + expSizeHOL e' ≤ expListSizeHOL args + expSizeHOL e) ?_ ?_ ?_
  · intro args t body more cond ih args' e' run
    simp only [collectApps, cond, if_true] at run
    have step := ih args' e' run
    rw [exp3_size_append] at step
    simp only [expSizeHOL] at ⊢
    omega
  · intro args t body more cond args' e' run
    simp only [collectApps, cond, if_false, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    omega
  · intro args e other args' e' run
    simp only [collectApps] at run
    obtain ⟨rfl, rfl⟩ := run
    omega

end Flapjack.Compiler.Backend.ClosMti
