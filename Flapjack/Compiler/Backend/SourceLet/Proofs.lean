import Flapjack.Compiler.Backend.SourceLet

/-! Proof prerequisites for the source let-lifting pass. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.AstHOL

/-- Successful successive lifting preserves the already accumulated
declarations as a prefix, in source order. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "lift_lets_is_prefix"]
theorem liftLets_isPrefix (sofar : List Dec) (d : Dec) (first : List Dec) (last : Dec)
    (lifted : liftLets sofar d = some (first, last)) : sofar.reverse <+: first := by
  induction sofar, d using liftLets.induct generalizing first last with
  | case1 sofar l p x y ih =>
    apply (List.prefix_append sofar.reverse [.dlet l .pany x]).trans
    simpa only [List.reverse_cons] using ih first last (by simpa only [liftLets] using lifted)
  | case2 sofar l p v x y ih =>
    apply (List.prefix_append sofar.reverse [.dlet l (.pvar v) x]).trans
    simpa only [List.reverse_cons] using ih first last (by simpa only [liftLets] using lifted)
  | case3 sofar l p fs x ih =>
    apply (List.prefix_append sofar.reverse [.dletrec l fs]).trans
    simpa only [List.reverse_cons] using ih first last (by simpa only [liftLets] using lifted)
  | case4 sofar d empty h1 h2 h3 =>
    cases d <;> simp_all [liftLets]
  | case5 sofar d nonempty h1 h2 h3 =>
    cases d <;> simp_all [liftLets]

/-- Module and local declarations are traversed recursively by the pass;
they cannot themselves start a sequence of lifted lets. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "lift_lets_mod_local"]
theorem liftLets_mod_local :
    (∀ ds1 ds2, liftLets [] (.dlocal ds1 ds2) = none) ∧
      (∀ mn ds, liftLets [] (.dmod mn ds) = none) := by
  constructor <;> intro <;> intro <;> simp [liftLets]

end Flapjack.Compiler.Backend.SourceLet
