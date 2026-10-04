import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.FfiHOL

/-!
# Exact targetSem carriers

Counterpart of `cakeml/compiler/backend/semantics/targetSemScript.sml`'s
`machine_result` and `machine_config` datatypes, together with the
`target` record they embed from
`cakeml/compiler/encoders/asm/asmPropsScript.sml:44-56`.

* `machine_result = Halt outcome | Error | TimeOut` — `outcome` is the
  reviewed `HolOutcome` (`ffiScript.sml:83`).
* `machine_config` is the same record as HOL: program/shared address sets are
  rendered as predicates `BitVec width → Prop` (HOL's `'a word set`); note
  that some existing Flapjack machine carriers render domains as
  `BitVec width → Bool`, so a later relation between the two renderings needs
  a Prop/Bool conversion that is not part of this module.  `word8` is
  `BitVec 8`, `ffi` names are `HolFfiName`, and `addr` is the exact `HolAddr`.

The embedded `target` record (and `target_state_rel`) lives in the asmProps
counterpart `Flapjack/Compiler/Encoders/AsmProps/Target.lean`.

This module supplies carriers only: no evaluator, no `target_state_rel`, and no
`good_init_state`. Those remain separate dependencies.
-/

namespace Flapjack

open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `Datatype: machine_result = Halt outcome | Error | TimeOut`
    (`cakeml/compiler/backend/semantics/targetSemScript.sml:14-17`). -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "machine_result"]
inductive MachineResult where
  | halt (outcome : HolOutcome)
  | error
  | timeOut

/-- Exact HOL `Datatype: machine_config = <| prog_addresses : ('a word) set ;
    shared_addresses : ('a word) set ; ffi_entry_pcs : ('a word) list ;
    ffi_names : ffiname list ; ptr_reg : num ; len_reg : num ; ptr2_reg : num ;
    len2_reg : num ; ffi_interfer : num -> num # word8 list # 'b -> 'b ;
    callee_saved_regs : num list ; next_interfer : num -> 'b -> 'b ;
    halt_pc : 'a word ; ccache_pc : 'a word ;
    ccache_interfer : num -> 'a word # 'a word # 'b -> 'b ;
    target : ('a,'b,'c) target ;
    mmio_info : (num # (word8 # 'a addr # num # 'a word)) list |>` (field order
    preserved; `cakeml/compiler/backend/semantics/targetSemScript.sml:18-45`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
structure MachineConfig (width : Nat) [NeZero width] (state : Type) (projection : Type) where
  progAddresses : BitVec width → Prop
  sharedAddresses : BitVec width → Prop
  ffiEntryPcs : List (BitVec width)
  ffiNames : List HolFfiName
  ptrReg : Nat
  lenReg : Nat
  ptr2Reg : Nat
  len2Reg : Nat
  ffiInterfer : Nat → Nat × List (BitVec 8) × state → state
  calleeSavedRegs : List Nat
  nextInterfer : Nat → state → state
  haltPc : BitVec width
  ccachePc : BitVec width
  ccacheInterfer : Nat → BitVec width × BitVec width × state → state
  target : HolAsmTarget width state projection
  mmioInfo : List (Nat × (BitVec 8 × HolAddr width × Nat × BitVec width))

end Flapjack
