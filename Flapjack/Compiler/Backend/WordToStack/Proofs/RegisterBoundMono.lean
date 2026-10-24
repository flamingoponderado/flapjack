import Flapjack.Compiler.Backend.StackProps.RegisterBounds

namespace Flapjack.WordToStackProofs
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Internal instruction calculation from the original reg_bound_mono proof;
HOL proves it by constructor cases inside that theorem, without a separate name. -/
private theorem instBoundMono {width : Nat} [NeZero width]
    (instruction : HolInst width) (k k' : Nat)
    (bounded : regBoundInst instruction k) (le : k ≤ k') :
    regBoundInst instruction k' := by
  cases instruction with
  | arith a =>
      cases a <;> try (rename_i op d s ri; cases ri)
      all_goals simp_all [regBoundInst] <;> omega
  | mem op d addr =>
      cases addr
      simp_all [regBoundInst] <;> omega
  | fp f =>
      cases f <;> simp_all [regBoundInst] <;> omega
  | skip => trivial
  | const _ _ => simp_all [regBoundInst] <;> omega

/-- Full original native program register-bound monotonicity. The original
return-dependent handler branch is preserved; no guard on ignored handlers,
stack offsets, allocation counts, word width or target evaluation is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "reg_bound_mono" (words_as_type_indexed_bitvec)]
theorem regBoundMono {width : Nat} [NeZero width]
    (program : HolProg width) (k k' : Nat)
    (bounded : regBound program k) (le : k ≤ k') : regBound program k' := by
  set_option tactic.fun_induction.unfolding false in
    fun_induction regBound program k with
    | case11 _ _ right => cases right <;> grind only [regBound, instBoundMono]
    | case15 returns target handler bound ih =>
        rcases returns with _ | ⟨body, register, l1, l2⟩ <;>
          rcases handler with _ | ⟨continuation, h1, h2⟩ <;>
          cases target <;> grind only [regBound, instBoundMono]
    | case27 program => cases program <;> grind only [regBound]
    | _ => grind only [regBound, instBoundMono]

end Flapjack.WordToStackProofs
