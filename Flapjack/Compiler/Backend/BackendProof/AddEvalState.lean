module

public import Flapjack.Compiler.Backend.Backend.IncProgs
public import Flapjack.Compiler.Backend.SourceEval.Proofs
public import Flapjack.Misc.PredSet

@[expose] public section

/-! backendProofScript.sml 2910-2928 and 3050-3059: installing the optional
evaluation compiler instance in the initial source state, and its
well-formedness condition. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.SourceEval.Proofs

/-- Exact HOL `add_eval_state_def` (`backendProofScript.sml:2910-2914`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "add_eval_state_def"]
noncomputable def addEvalState {β σ : Type} :
    Option (CompilerInstance β) → State σ → State σ
  | none, s0 => s0
  | some ci, s0 => { s0 with evalState := some (mkInitEvalState ci) }

/-- Exact HOL `add_eval_state_ffi` (`backendProofScript.sml:2916-2920`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "add_eval_state_ffi"]
theorem addEvalState_ffi {β σ : Type} (optEv : Option (CompilerInstance β)) (s0 : State σ) :
    (addEvalState optEv s0).ffi = s0.ffi := by
  cases optEv <;> rfl

/-- Exact HOL `opt_eval_config_wf_def` (`backendProofScript.sml:2923-2928`).
`INJ ci.config_v UNIV UNIV` is the reviewed `holInj` on full sets. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "opt_eval_config_wf_def"
  (words_as_type_indexed_bitvec)]
def optEvalConfigWf {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config) :
    Option (CompilerInstance Flapjack.Compiler.Backend.Backend.Config) → Prop
  | some ci => ci.compilerFun = compileIncProgsForEval asmConf ∧
      holInj ci.configV (fun _ => True) (fun _ => True) ∧ ci.initState = c'
  | none => True

open Classical in
/-- Exact HOL `config_wf_abs_conc` (`backendProofScript.sml:3050-3059`). HOL's
`cfg ∈ dom` is the predicate application `dom cfg`, decided classically. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "config_wf_abs_conc"
  (words_as_type_indexed_bitvec)]
theorem configWf_absConc {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (ci : CompilerInstance Flapjack.Compiler.Backend.Backend.Config)
    (dom : Flapjack.Compiler.Backend.Backend.Config → Prop)
    (cfg : Flapjack.Compiler.Backend.Backend.Config) :
    optEvalConfigWf asmConf c' (some ci) →
      vFunAbs dom ci.configV (ci.configV cfg) = if dom cfg then some cfg else none := by
  intro ⟨_, hinj, _⟩
  have key : ∀ x, (ci.configV x = ci.configV cfg ∧ dom x) ↔ (x = cfg ∧ dom cfg) := by
    intro x
    constructor
    · rintro ⟨he, hd⟩
      have := hinj.2 x cfg ⟨trivial, trivial⟩ he
      subst this; exact ⟨rfl, hd⟩
    · rintro ⟨rfl, hd⟩; exact ⟨rfl, hd⟩
  unfold vFunAbs holOptionSome
  split_ifs with h1 h2 h2
  · obtain ⟨-, hc⟩ := (key _).1 (Classical.choose_spec h1)
    rw [((key _).1 (Classical.choose_spec h1)).1]
  · exact absurd ((key _).1 (Classical.choose_spec h1)).2 h2
  · exact absurd ⟨cfg, (key cfg).2 ⟨rfl, h2⟩⟩ h1
  · rfl

end Flapjack.Compiler.Backend.BackendProof
