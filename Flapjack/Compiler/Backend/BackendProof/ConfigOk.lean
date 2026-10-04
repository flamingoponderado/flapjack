import Mathlib.Logic.Function.Defs
import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig
import Flapjack.Compiler.Backend.DataToWord.ConfOk
import Flapjack.Compiler.Backend.DataToWord.MaxHeapLimit
import Flapjack.Compiler.Backend.BackendCommon.BvlStubs
import Flapjack.Compiler.Backend.StackNames.NamesOk
import Flapjack.Compiler.Backend.StackNames.OperandNames
import Flapjack.Compiler.Backend.StackProps.FixedNames
import Flapjack.Compiler.Backend.StackRemove.StoreAddress

/-! backendProofScript.sml: `backend_config_ok_def`, the backend-configuration
hypothesis of the Pancake top-level correctness theorem
(`pan_to_targetProof$pan_to_target_compile_semantics`). -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackNames

/-- Exact HOL `backendProof$backend_config_ok_def` (`backendProofScript.sml:53-86`),
conjunct for conjunct. HOL word `≤` is signed `word_le` (`BitVec.sle`), `n2w` is
`BitVec.ofNat`, `dimindex (:'a)` is `width`, `f PERMUTES UNIV` (`BIJ f UNIV UNIV`)
is `Function.Bijective`, the `addr/hw/byte_offset_ok` overloads are the reviewed
`asm*OffsetOkExact`, `OPTION_ALL P o` is the `none ↦ True` match and `EVERY` is
membership quantification. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "backend_config_ok_def"
  (words_as_type_indexed_bitvec)]
def backendConfigOk {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) : Prop :=
  c.sourceConf = Flapjack.Compiler.Backend.Backend.primSrcConfig ∧
  0 < c.closConf.maxApp ∧
  c.bvlConf.nextName2 = bvlNumStubs + 2 ∧
  asmConf.avoidRegs.length + 13 ≤ asmConf.regCount ∧
  c.labConf.pos = 0 ∧
  c.labConf.labels = .ln ∧
  DataToWord.confOk width c.dataConf ∧
  (c.dataConf.hasLongdiv = true → asmConf.isa = .x86_64) ∧
  (c.dataConf.hasDiv = true →
    asmConf.isa = .armv8 ∨ asmConf.isa = .mips ∨ asmConf.isa = .riscv) ∧
  (c.dataConf.hasFpTern = true ↔ asmConf.isa = .armv7 ∧ 2 < asmConf.fpRegCount) ∧
  (c.dataConf.hasFpOps = true ↔ 1 < asmConf.fpRegCount) ∧
  StackRemove.maxStackAlloc ≤ 2 * DataToWord.maxHeapLimit width c.dataConf - 1 ∧
  c.stackConf.perfCalls = false ∧
  asmAddrOffsetOkExact asmConf 0 = true ∧
  asmHwOffsetOkExact asmConf 0 = true ∧
  (∀ w : BitVec width, (-8 : BitVec width).sle w = true ∧ w.sle 8 = true →
    asmByteOffsetOkExact asmConf w = true) ∧
  asmConf.validImm (.inl .add) 8 = true ∧
  asmConf.validImm (.inl .add) 4 = true ∧
  asmConf.validImm (.inl .add) 1 = true ∧
  asmConf.validImm (.inl .sub) 1 = true ∧
  (match c.labConf.ffiNames with
    | none => True
    | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s) ∧
  Function.Bijective (findNameSpt c.stackConf.regNames) ∧
  namesOkSptHOL c.stackConf.regNames asmConf.regCount asmConf.avoidRegs ∧
  StackProps.fixedNames c.stackConf.regNames asmConf ∧
  (∀ s, asmAddrOffsetOkExact asmConf (StackRemove.storeOffset s) = true) ∧
  (∀ s, asmHwOffsetOkExact asmConf (StackRemove.storeOffset s) = true) ∧
  (∀ n, n ≤ StackRemove.maxStackAlloc →
    asmConf.validImm (.inl .sub) (BitVec.ofNat width (n * (width / 8))) = true ∧
    asmConf.validImm (.inl .add) (BitVec.ofNat width (n * (width / 8))) = true)

end Flapjack.Compiler.Backend.BackendProof
