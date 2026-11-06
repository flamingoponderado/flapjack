import Flapjack.Compiler.Backend.BackendProps.Pure
import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
import Flapjack.Compiler.Backend.Semantics.FlatSem
import Flapjack.Misc.ShiftSeq

/-! FlatPattern's dynamic-compiler configuration relation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.BackendProps

/-- Source and target installation configurations agree on the downstream
compiler and oracle after applying the pattern pass. Full evaluator and pass
correspondence remains pending review. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "install_conf_rel_def"]
def installConfRel {C : Type} (cfg : Config) (source target : FlatSem.InstallConfig C) : Prop :=
  target.compileOracle = pureCo (List.map (compileDec cfg)) ∘ source.compileOracle ∧
  source.compile = pureCc (List.map (compileDec cfg)) target.compile

/-- Shifting both related oracles preserves the relation. This Flapjack lemma
supports dynamic installation; it has no separate HOL declaration. -/
theorem installConfRel_shift {C : Type} (cfg : Config) (source target : FlatSem.InstallConfig C)
    (offset : Nat) (related : installConfRel cfg source target) :
    installConfRel cfg { source with compileOracle := Flapjack.holShiftSeq offset source.compileOracle }
      { target with compileOracle := Flapjack.holShiftSeq offset target.compileOracle } := by
  rcases related with ⟨oracle, compiler⟩
  constructor
  · funext i
    exact congrFun oracle (i + offset)
  · exact compiler

end Flapjack.Compiler.Backend.FlatPattern
