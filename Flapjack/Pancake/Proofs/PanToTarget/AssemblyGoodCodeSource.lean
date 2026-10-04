import Flapjack.Pancake.Proofs.PanToTarget.AssemblyGoodCode
import Flapjack.Pancake.Proofs.PanToWord.CompileProgInstOkLess
import Flapjack.Pancake.Proofs.PanToTarget

namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.BackendProof Flapjack.Pancake.PanLang

/-- Source-premise discharge of stage A2 of the original top proof (1376–1428).
The actual WordToWord/WordToStack equations identify the intermediate values
produced by the top compiler. Instruction validity and both zero-offset guards
are derived internally from the original source good-code guard and backend
configuration. This is Flapjack proof factoring of an intermediate HOL proof
step, with no separately named HOL declaration; it is deliberately untagged.
The final top theorem must still derive these intermediate compiler equations
from its own full compile equation, and assemble the remaining semantic stages. -/
theorem panToTargetGoodCodeFromSource {width : Nat} [NeZero width] {S Q β : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat))) (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × StackLang.HolProg width))
    (hcfg : backendConfigOk mc.target.config c) (hgood : goodDimindex width)
    (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hsource : pancakeGoodCodeHOL panCode = true) :
    LabToTarget.goodCode mc.target.config (.ln : Spt (Spt β))
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p) := by
  have hinst := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hao, -, hbo, -⟩ := hcfg
    have ⟨hz8, hm8z⟩ := good_dimindex_0w_8w hgood
    exact PanToWord.panToWordEveryInstOkLess mc.target.config panCode _ rfl
      (hbo 0 ⟨hm8z, hz8⟩) hao hsource
  exact panToTargetGoodCode c mc panCode col wprog bitmaps wconf fs p
    hcfg hgood hisa hwtw hwts hnodup hinst

/-- Stage A2 using only the original source/configuration hypotheses.
Both backend intermediate tuples are computed internally, so no intermediate
success equation or instruction-validity premise is required. This is an
unnamed step of the HOL top proof rather than a separate HOL declaration.
The final top theorem still relates this lab program to its full compile result
and composes the semantic and resource stages. -/
theorem panToTargetGoodCodeSource {width : Nat} [NeZero width] {S Q β : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (panCode : List (DeclHOL width))
    (hcfg : backendConfigOk mc.target.config c) (hgood : goodDimindex width)
    (hisa : mc.target.config.isa ≠ .ag32)
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hsource : pancakeGoodCodeHOL panCode = true) :
    let wordResult := WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode)
    let stackResult := WordToStack.Native.compileNative mc.target.config false wordResult.2
    LabToTarget.goodCode mc.target.config (.ln : Spt (Spt β))
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset stackResult.2.2.2) := by
  dsimp only
  cases hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) with
  | mk col wprog =>
    cases hwts : WordToStack.Native.compileNative mc.target.config false wprog with
    | mk bitmaps rest =>
      rcases rest with ⟨wconf, fs, p⟩
      exact panToTargetGoodCodeFromSource c mc panCode col wprog bitmaps wconf fs p
        hcfg hgood hisa hwtw hwts hnodup hsource

end Flapjack.Pancake.Proofs.PanToTarget
