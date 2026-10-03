import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Backend.LabToTarget.GoodCode
import Flapjack.Compiler.Backend.LabProps.CodeSafety

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm

/-- Full initial compiler-oracle contract. The oracle returns the concrete,
word-free source Config, whose labels genuinely have natural-number leaves.
Every index satisfies both code invariants; index zero retains all three
initial-configuration equalities. The unused zero-index code component is
retained in the pair destructuring. This proof-layer predicate introduces no
successful compilation or desired target-state premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compiler_oracle_ok_def"
  (words_as_type_indexed_bitvec)]
def compilerOracleOk {width : Nat} [NeZero width]
    (coracle : Nat → Config × LabProgHOL width) (initLabs : Spt (Spt Nat))
    (initPos : Nat) (c : AsmConfigExact width) (ffis : List HolFfiName) : Prop :=
  (∀ k, let (cfg, code) := coracle k;
    goodCode c cfg.labels code ∧ LabProps.noShareMemInst code) ∧
  (let (cfg, _) := coracle 0;
    cfg.labels = initLabs ∧ cfg.pos = initPos ∧ cfg.ffiNames = some ffis)

end Flapjack.Compiler.Backend.LabToTarget
