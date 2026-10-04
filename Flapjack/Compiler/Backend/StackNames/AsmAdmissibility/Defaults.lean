import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.StackNames.NamesOk
import Flapjack.Compiler.Backend.StackProps.FixedNames
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.ProgramValidity

namespace Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang

/-- Flapjack-only helper collecting constructors whose target admissibility
clause is True. Its selector premise is extra infrastructure, so this helper
has no HOL tag. The concrete cases below discharge that selector internally
and retain exactly HOL's three original guards. -/
theorem stackNamesCompStackAsmOk_Default {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width) (p : HolProg width)
    (hCase : match p with
      | .inst _ | .opCurrHeap _ _ _ | .shMemOp _ _ _ | .codeBufferWrite _ _
      | .raise _ | .ret _ | .seq _ _ | .ite _ _ _ _ _ | .loop _ | .call _ _ _ => False
      | _ => True)
    (_h : stackAsmName config p ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names p) := by
  cases p <;> simp_all [progCompHOL, stackAsmOkExact]

/-- HOL comp_ind Skip case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Skip {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)

    (h : stackAsmName config (.skip) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.skip)) := by
  exact stackNamesCompStackAsmOk_Default names config (.skip) True.intro h

/-- HOL comp_ind Get case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Get {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (destination : Nat) (store : StoreName)
    (h : stackAsmName config (.get destination store) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.get destination store)) := by
  exact stackNamesCompStackAsmOk_Default names config (.get destination store) True.intro h

/-- HOL comp_ind Set case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Set {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (store : StoreName) (source : Nat)
    (h : stackAsmName config (.set store source) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.set store source)) := by
  exact stackNamesCompStackAsmOk_Default names config (.set store source) True.intro h

/-- HOL comp_ind JumpLower case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_JumpLower {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (left right target : Nat)
    (h : stackAsmName config (.jumpLower left right target) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.jumpLower left right target)) := by
  exact stackNamesCompStackAsmOk_Default names config (.jumpLower left right target) True.intro h

/-- HOL comp_ind Alloc case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Alloc {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (words : Nat)
    (h : stackAsmName config (.alloc words) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.alloc words)) := by
  exact stackNamesCompStackAsmOk_Default names config (.alloc words) True.intro h

/-- HOL comp_ind StoreConsts case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_StoreConsts {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (source bitmap : Nat) (stub : Option Nat)
    (h : stackAsmName config (.storeConsts source bitmap stub) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.storeConsts source bitmap stub)) := by
  exact stackNamesCompStackAsmOk_Default names config (.storeConsts source bitmap stub) True.intro h

/-- HOL comp_ind Break case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Break {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (label : Nat)
    (h : stackAsmName config (.break label) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.break label)) := by
  exact stackNamesCompStackAsmOk_Default names config (.break label) True.intro h

/-- HOL comp_ind Continue case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Continue {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (label : Nat)
    (h : stackAsmName config (.continue label) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.continue label)) := by
  exact stackNamesCompStackAsmOk_Default names config (.continue label) True.intro h

/-- HOL comp_ind FFI case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_FFI {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (function : Flapjack.Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength returnAddress : Nat)
    (h : stackAsmName config (.ffi function configuration configurationLength array arrayLength returnAddress) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.ffi function configuration configurationLength array arrayLength returnAddress)) := by
  exact stackNamesCompStackAsmOk_Default names config (.ffi function configuration configurationLength array arrayLength returnAddress) True.intro h

/-- HOL comp_ind Tick case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Tick {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)

    (h : stackAsmName config (.tick) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.tick)) := by
  exact stackNamesCompStackAsmOk_Default names config (.tick) True.intro h

/-- HOL comp_ind LocValue case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_LocValue {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (destination label entry : Nat)
    (h : stackAsmName config (.locValue destination label entry) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.locValue destination label entry)) := by
  exact stackNamesCompStackAsmOk_Default names config (.locValue destination label entry) True.intro h

/-- HOL comp_ind Install case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Install {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (codeBuffer codeLength dataBuffer dataLength returnAddress : Nat)
    (h : stackAsmName config (.install codeBuffer codeLength dataBuffer dataLength returnAddress) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.install codeBuffer codeLength dataBuffer dataLength returnAddress)) := by
  exact stackNamesCompStackAsmOk_Default names config (.install codeBuffer codeLength dataBuffer dataLength returnAddress) True.intro h

/-- HOL comp_ind DataBufferWrite case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_DataBufferWrite {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (address value : Nat)
    (h : stackAsmName config (.dataBufferWrite address value) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.dataBufferWrite address value)) := by
  exact stackNamesCompStackAsmOk_Default names config (.dataBufferWrite address value) True.intro h

/-- HOL comp_ind RawCall case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_RawCall {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (target : Nat)
    (h : stackAsmName config (.rawCall target) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.rawCall target)) := by
  exact stackNamesCompStackAsmOk_Default names config (.rawCall target) True.intro h

/-- HOL comp_ind StackAlloc case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_StackAlloc {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (words : Nat)
    (h : stackAsmName config (.stackAlloc words) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.stackAlloc words)) := by
  exact stackNamesCompStackAsmOk_Default names config (.stackAlloc words) True.intro h

/-- HOL comp_ind StackFree case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_StackFree {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (words : Nat)
    (h : stackAsmName config (.stackFree words) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.stackFree words)) := by
  exact stackNamesCompStackAsmOk_Default names config (.stackFree words) True.intro h

/-- HOL comp_ind StackStore case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_StackStore {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (offset register : Nat)
    (h : stackAsmName config (.stackStore offset register) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.stackStore offset register)) := by
  exact stackNamesCompStackAsmOk_Default names config (.stackStore offset register) True.intro h

/-- HOL comp_ind StackStoreAny case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_StackStoreAny {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (register offsetRegister : Nat)
    (h : stackAsmName config (.stackStoreAny register offsetRegister) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.stackStoreAny register offsetRegister)) := by
  exact stackNamesCompStackAsmOk_Default names config (.stackStoreAny register offsetRegister) True.intro h

/-- HOL comp_ind StackLoad case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_StackLoad {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (offset register : Nat)
    (h : stackAsmName config (.stackLoad offset register) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.stackLoad offset register)) := by
  exact stackNamesCompStackAsmOk_Default names config (.stackLoad offset register) True.intro h

/-- HOL comp_ind StackLoadAny case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_StackLoadAny {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (register offsetRegister : Nat)
    (h : stackAsmName config (.stackLoadAny register offsetRegister) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.stackLoadAny register offsetRegister)) := by
  exact stackNamesCompStackAsmOk_Default names config (.stackLoadAny register offsetRegister) True.intro h

/-- HOL comp_ind StackGetSize case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_StackGetSize {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (register : Nat)
    (h : stackAsmName config (.stackGetSize register) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.stackGetSize register)) := by
  exact stackNamesCompStackAsmOk_Default names config (.stackGetSize register) True.intro h

/-- HOL comp_ind StackSetSize case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_StackSetSize {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (register : Nat)
    (h : stackAsmName config (.stackSetSize register) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.stackSetSize register)) := by
  exact stackNamesCompStackAsmOk_Default names config (.stackSetSize register) True.intro h

/-- HOL comp_ind BitmapLoad case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_BitmapLoad {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (destination address : Nat)
    (h : stackAsmName config (.bitmapLoad destination address) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.bitmapLoad destination address)) := by
  exact stackNamesCompStackAsmOk_Default names config (.bitmapLoad destination address) True.intro h

/-- HOL comp_ind Halt case with exactly the original three guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Halt {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (register : Nat)
    (h : stackAsmName config (.halt register) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.halt register)) := by
  exact stackNamesCompStackAsmOk_Default names config (.halt register) True.intro h

end Flapjack.Compiler.Backend.StackNames
