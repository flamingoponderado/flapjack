module

public import Flapjack.Compiler.Backend.SourceLet

@[expose] public section

/-! Proof prerequisites for the source let-lifting pass. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.AstHOL

/-- Successful successive lifting preserves the already accumulated
declarations as a prefix, in source order. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "lift_lets_is_prefix"]
theorem liftLets_isPrefix (sofar : List Dec) (d : Dec) (first : List Dec) (last : Dec)
    (lifted : liftLets sofar d = some (first, last)) : sofar.reverse <+: first := by
  induction sofar, d using liftLets.induct generalizing first last with
  | case1 sofar d d1 d2 step ih =>
    apply (List.prefix_append sofar.reverse [d1]).trans
    rw [liftLets.eq_def, step] at lifted
    simpa only [List.reverse_cons] using ih first last lifted
  | case2 sofar d step empty =>
    rw [liftLets.eq_def, step] at lifted
    simp [empty] at lifted
  | case3 sofar d step nonempty =>
    rw [liftLets.eq_def, step] at lifted
    simp only [nonempty] at lifted
    obtain ⟨rfl, _⟩ := lifted
    exact ⟨[], by simp⟩

/-- Module and local declarations are traversed recursively by the pass;
they cannot themselves start a sequence of lifted lets. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "lift_lets_mod_local"]
theorem liftLets_mod_local :
    (∀ ds1 ds2, liftLets [] (.dlocal ds1 ds2) = none) ∧
      (∀ mn ds, liftLets [] (.dmod mn ds) = none) := by
  constructor <;> intro <;> intro <;> simp [liftLets.eq_def, liftLet]

end Flapjack.Compiler.Backend.SourceLet
