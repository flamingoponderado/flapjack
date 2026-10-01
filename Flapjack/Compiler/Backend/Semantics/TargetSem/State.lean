import Flapjack.Compiler.Encoders.Asm
import Flapjack.FfiHOL

/-!
# Exact targetSem carriers

Counterpart of `cakeml/compiler/backend/semantics/targetSemScript.sml`'s
`machine_result` and `machine_config` datatypes, together with the
`target` record they embed from
`cakeml/compiler/encoders/asm/asmPropsScript.sml:44-56`.

* `machine_result = Halt outcome | Error | TimeOut` — `outcome` is the
  reviewed `HolOutcome` (`ffiScript.sml:83`).
* `target` is the polymorphic target-configuration record whose `config` field
  uses the exact `AsmConfigExact`, and whose `'b`/`'c` state/projection
  parameters stay polymorphic.
* `machine_config` is the same record as HOL: program/shared address sets are
  rendered as predicates `BitVec width → Prop` (matching the existing
  `memaddrs`/`mdomain` rendering), `word8` as `BitVec 8`, `ffi` names as
  `HolFfiName`, and `addr` as the exact `HolAddr`.

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

/-- Exact HOL `Datatype: target = <| config : 'a asm_config ; next : 'b -> 'b ;
    get_pc : 'b -> 'a word ; get_reg : 'b -> num -> 'a word ;
    get_fp_reg : 'b -> num -> word64 ; get_byte : 'b -> 'a word -> word8 ;
    state_ok : 'b -> bool ; proj : 'a word set -> 'b -> 'c |>`
    (`cakeml/compiler/encoders/asm/asmPropsScript.sml:44-56`).

    `'a word` is rendered as `BitVec width` with the reviewed `[NeZero width]`
    discharge; the state parameter `'b` and projection parameter `'c` are kept
    polymorphic.  `config` is the exact reviewed `AsmConfigExact`. -/
@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "target"
  (words_as_type_indexed_bitvec)]
structure HolAsmTarget (width : Nat) [NeZero width] (state : Type) (projection : Type) where
  config : AsmConfigExact width
  next : state → state
  getPc : state → BitVec width
  getReg : state → Nat → BitVec width
  getFpReg : state → Nat → BitVec 64
  getByte : state → BitVec width → BitVec 8
  stateOk : state → Bool
  proj : (BitVec width → Prop) → state → projection

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
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "machine_config"
  (words_as_type_indexed_bitvec)]
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
