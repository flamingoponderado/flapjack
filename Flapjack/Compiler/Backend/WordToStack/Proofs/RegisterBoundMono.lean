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
  | skip => trivial
  | const _ _ => simp_all [regBoundInst] <;> omega

/-- Full original native program register-bound monotonicity. The original
return-dependent handler branch is preserved; no guard on ignored handlers,
stack offsets, allocation counts, word width or target evaluation is added. -/
theorem regBoundMono {width : Nat} [NeZero width]
    (program : HolProg width) (k k' : Nat)
    (bounded : regBound program k) (le : k ≤ k') : regBound program k' := by
  cases program with
  | seq first second =>
      exact ⟨regBoundMono first k k' bounded.1 le,
        regBoundMono second k k' bounded.2 le⟩
  | loop body => exact regBoundMono body k k' bounded le
  | ite cmp register right first second =>
      have firstSafe := regBoundMono first k k' bounded.2.2.1 le
      have secondSafe := regBoundMono second k k' bounded.2.2.2 le
      cases right <;> simp_all [regBound] <;> omega
  | call returns target handler =>
      cases target with
      | inl label =>
          cases returns with
          | none => simp_all [regBound] <;> omega
          | some record =>
              match hRet : record with
              | (body,register,l1,l2) =>
                  unfold regBound at bounded
                  have bodySafe := regBoundMono body k k' bounded.2.1 le
                  cases handler with
                  | none => simp_all [regBound] <;> omega
                  | some record =>
                      match hHandle : record with
                      | (body,l1,l2) =>
                          have handlerSafe := regBoundMono body k k' bounded.2.2.2 le
                          simp_all [regBound] <;> omega
      | inr register =>
          cases returns with
          | none => simp_all [regBound] <;> omega
          | some record =>
              match hRet : record with
              | (body,register,l1,l2) =>
                  unfold regBound at bounded
                  have bodySafe := regBoundMono body k k' bounded.2.1 le
                  cases handler with
                  | none => simp_all [regBound] <;> omega
                  | some record =>
                      match hHandle : record with
                      | (body,l1,l2) =>
                          have handlerSafe := regBoundMono body k k' bounded.2.2.2 le
                          simp_all [regBound] <;> omega
  | inst i => exact instBoundMono i k k' bounded le
  | _ => simp_all [regBound] <;> omega
termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end Flapjack.WordToStackProofs
