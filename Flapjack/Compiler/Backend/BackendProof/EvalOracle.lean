module

public import Flapjack.Compiler.Backend.BackendProof.CakeOracConfigEqs
public import Flapjack.Compiler.Backend.BackendProof.ConfigTuple
public import Flapjack.Misc.PredSet

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 2880-2908: helper facts for the evaluation-oracle
part of the top-level correctness proof. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.Backend
open Flapjack.Compiler.Backend.BackendDefs Flapjack.Compiler.Backend.BackendProps

/-- Exact HOL `FST_SND_EQ` (`backendProofScript.sml:2880-2885`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "FST_SND_EQ"]
theorem fst_snd_eq {α β : Type} (x : α × β) (y : α) (z : β) :
    (x.1 = y ∧ x.2 = z ↔ x = (y, z)) ∧ (x.2 = z ∧ x.1 = y ↔ x = (y, z)) := by
  obtain ⟨a, b⟩ := x
  simp [and_comm]

/-- Exact HOL `PERMUTE_IMP_LINV` (`backendProofScript.sml:2887-2893`, `[local]`).
`f PERMUTES 𝕌(:α)` (`BIJ f UNIV UNIV`) is `Function.Bijective f`, and `LINV f
UNIV` is the reviewed `holLinv` on the full set, whose `Nonempty α` instance
renders HOL `THE` on the unspecified case. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "PERMUTE_IMP_LINV"
  (total_function_inhabitants := [α])]
theorem permute_imp_linv {α : Type} [Nonempty α] (f : α → α) :
    Function.Bijective f → ∀ x y : α, y = holLinv f (fun _ => True) x ↔ x = f y := by
  intro hf x y
  have hinv : ∀ z, f (holLinv f (fun _ => True) z) = z := apply_holLinv_of_surjective hf.2
  constructor
  · rintro rfl; exact (hinv x).symm
  · rintro rfl
    exact (holLinvDef f (fun _ => True) (fun _ => True)
      ⟨fun _ _ => trivial, fun _ _ _ he => hf.1 he⟩ y trivial).symm

/-- Exact HOL `state_co_inc_compile_has_flat_comp` (`backendProofScript.sml:2895-2908`):
under a successful compilation, the incremental source compiler factors into
`inc_compile_prog` followed by pattern compilation at the initial pattern
configuration. HOL `MAP` is `List.map`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "state_co_inc_compile_has_flat_comp" (words_as_type_indexed_bitvec)]
theorem stateCo_incCompile_hasFlatComp {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (f : List AstHOL.Dec → List AstHOL.Dec)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (g : BackendProgs width → (Nat × Nat) × List AstHOL.Dec) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') →
    stateCo (fun (c : SourceToFlat.Config) ((envId, decs) : (Nat × Nat) × List AstHOL.Dec) =>
        SourceToFlat.incCompile envId c (f decs))
      (cakeOrac asmConf c' src configTuple1 g) =
      pureCo (List.map (FlatPattern.compileDec c.sourceConf.patternCfg)) ∘
        stateCo (fun (c : SourceToFlat.Config) ((envId, decs) : (Nat × Nat) × List AstHOL.Dec) =>
            SourceToFlat.incCompileProg envId c (f decs))
          (cakeOrac asmConf c' src configTuple1 g) := by
  intro h
  funext n
  have hpat := (cakeOrac_configEqs asmConf c prog b bm c' src n h).1
  have e : cakeOrac asmConf c' src configTuple1 g n =
      (configTuple1 (cakeConfigs asmConf c' src n),
        g (compileIncProgs true asmConf (cakeConfigs asmConf c' src n) (src n)).2) := by
    rcases hp : compileIncProgs true asmConf (cakeConfigs asmConf c' src n) (src n) with ⟨a, b⟩
    simp only [cakeOrac, hp]
  simp only [Function.comp_apply, stateCo, pureCo, e]
  rcases hg : g (compileIncProgs true asmConf (cakeConfigs asmConf c' src n) (src n)).2 with
    ⟨envId, decs⟩
  simp only [configTuple1, SourceToFlat.incCompile]
  rcases hi : SourceToFlat.incCompileProg envId (cakeConfigs asmConf c' src n).sourceConf (f decs)
    with ⟨next, program⟩
  have hnext : next.patternCfg = (cakeConfigs asmConf c' src n).sourceConf.patternCfg := by
    simp only [SourceToFlat.incCompileProg] at hi
    rw [← (Prod.mk.inj hi).1]
  simp only [hnext, hpat]

end Flapjack.Compiler.Backend.BackendProof
