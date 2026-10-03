import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Backend.LabToTarget.GoodCode
import Flapjack.Compiler.Backend.LabProps.CodeSafety
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect
import Flapjack.Misc.GoodDimindex

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

/-- Complete machine-configuration contract, with the original dimension,
encoder simulation, four pointer/length register guards, exact optional link
register fallback, and encoding invariant. State and projection carriers remain
independent. The imported encoderCorrect inherits the reviewed FP real-rendering
assumption of SOUNDNESS item8; this definition performs no real rendering itself.
The dimension clause is retained separately from intrinsic word positivity. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "mc_conf_ok_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mcConfOk {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) : Prop :=
  goodDimindex width ∧
  Flapjack.Compiler.Encoders.AsmProps.encoderCorrect mc.target ∧
  asmRegOkExact mc.ptrReg mc.target.config = true ∧
  asmRegOkExact mc.lenReg mc.target.config = true ∧
  asmRegOkExact mc.ptr2Reg mc.target.config = true ∧
  asmRegOkExact mc.len2Reg mc.target.config = true ∧
  asmRegOkExact (match mc.target.config.linkReg with | none => 0 | some n => n)
    mc.target.config = true ∧
  encOk mc.target.config

end Flapjack.Compiler.Backend.LabToTarget
