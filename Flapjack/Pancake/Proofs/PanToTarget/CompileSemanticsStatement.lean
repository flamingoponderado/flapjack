import Flapjack.Pancake.Proofs.PanToTarget
import Flapjack.Pancake.Proofs.PanToTarget.PanInstalled
import Flapjack.Compiler.Backend.BackendProof.ConfigOk
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.BackendProof.ReadLimits
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.Compiler.Backend.Semantics.TargetSem.MachineSem
import Flapjack.SemanticsProps.Implements
import Flapjack.Pancake.Semantics.PanSem.Semantics
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact

/-!
# The `pan_to_target_compile_semantics` statement (draft interface)

The full hypothesis list and conclusion of
`cakeml/pancake/proofs/pan_to_targetProofScript.sml:1257-1300`
(`pan_to_target_compile_semantics`) over the reviewed Lean carriers, stated as an
untagged proposition so that the final assembly can be developed against a fixed
interface. It is not a port of the theorem and carries no `@[hol]` tag.

As in HOL, `pan_installed` receives `s.memaddrs` and `s.sh_memaddrs` directly: the
reviewed `panInstalled` takes its two `'a word set` parameters on the same predicate
carrier as `PanSemStateFiniteExact`'s `memaddrs`/`shMemaddrs`.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL

/-- The hypotheses and conclusion of `pan_to_target_compile_semantics`, in HOL order. -/
def PanToTargetCompileSemanticsStatement {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (pan_code : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stack_max : Option Nat) (s : PanSemStateFiniteExact width σ) (ffi : HolFfiState σ)
    (ms : S) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec width)
    (cbspace data_sp : Nat) (start : MlS) : Prop :=
  let getReg := mc.target.getReg ms
  compileProgMax c mc pan_code = (some (bytes, bitmaps, c'), stack_max) ∧
  pancakeGoodCodeHOL pan_code = true ∧
  distinctParamsHOL (functionsHOL pan_code) ∧
  ((functionsHOL pan_code).map Prod.fst).Nodup ∧
  s.code = HolFiniteMapExact.empty ∧
  s.locals = HolFiniteMapExact.empty ∧
  s.globals = HolFiniteMapExact.empty ∧
  sizeOfEidsHOL pan_code < 2 ^ width ∧
  s.eshapes = HolFiniteMapExact.empty ∧
  backendConfigOk mc.target.config c ∧ LabToTarget.mcConfOk mc ∧
  mcInitOk mc.target.config c mc ∧ mc.target.config.isa ≠ .ag32 ∧
  (0 : BitVec width) < getReg mc.lenReg ∧
  globals_size =
    (let dec_shs := decShapesHOL pan_code
     let struct_ctxt := decsStcnamesHOLExact (width := width) [] pan_code
     (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
  getReg mc.lenReg < getReg mc.ptr2Reg ∧
  getReg mc.lenReg = s.baseAddr ∧
  globalsAllocatableHOL s pan_code ∧
  heap_len = (getReg mc.ptr2Reg + -1 * s.baseAddr).toNat / (width / 8) ∧
  s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heap_len -
    BitVec.ofNat width (globals_size * width / 8) ∧
  globals_size ≤ heap_len ∧
  s.memaddrs = StackRemove.addresses (getReg mc.lenReg) (heap_len - globals_size) ∧
  holAligned (wordShiftAmount width + 1) (getReg mc.ptr2Reg + -1 * getReg mc.lenReg) = true ∧
  adj_ptr2 = getReg mc.lenReg +
    StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ∧
  adj_ptr4 = getReg mc.len2Reg -
    StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ∧
  adj_ptr2 ≤ getReg mc.ptr2Reg ∧
  getReg mc.ptr2Reg ≤ adj_ptr4 ∧
  (getReg mc.ptr2Reg + -1 * getReg mc.lenReg).toNat ≤
    (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) ∧
  (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) <
    2 ^ width ∧
  s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
  (match c.labConf.ffiNames with
    | none => True
    | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s) ∧
  panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
    (heapRegs c.stackConf.regNames) mc c'.labConf.shmemExtra ms
    (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
  start = ofString "main" ∧
  PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail →
  ∀ b, machineSemHOL mc ffi ms b →
    extendWithResourceLimitPrimeHOL
      (optionLt stack_max (some (readLimits mc.target.config c mc ms).1))
      (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start pan_code) b

end Flapjack.Pancake.Proofs.PanToTarget
