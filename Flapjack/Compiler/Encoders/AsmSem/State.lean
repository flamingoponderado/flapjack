import Flapjack.Compiler.Encoders.Asm

/-!
# Exact asmSem state carrier

Counterpart of `cakeml/compiler/encoders/asm/asmSemScript.sml:12-23`
(`asm_state`).  This is the machine-state carrier on which `targetSem`'s
`good_init_state` is stated.

`'a word` is rendered as `BitVec width` ([NeZero width]); `word8` as
`BitVec 8`; `word64` as `BitVec 64`; `reg` as `Nat`; `('a word) set` as the
predicate rendering `BitVec width → Prop` (note that some existing Flapjack
machine carriers render domains as `BitVec width → Bool`; that is a different
translation and a conversion relation is not part of this module).  This
module supplies no evaluator and no `target_configured`/`good_init_state`.
-/

namespace Flapjack

open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `Datatype: asm_state = <| regs : num -> 'a word ;
    fp_regs : num -> word64 ; mem : 'a word -> word8 ;
    mem_domain : 'a word set ; pc : 'a word ; lr : reg ; align : num ;
    be : bool ; failed : bool |>` (`cakeml/compiler/encoders/asm/asmSemScript.sml:12-23`),
    field order preserved. -/
structure AsmState (width : Nat) [NeZero width] where
  regs : Nat → BitVec width
  /-- Compatibility field for existing state relations; integer execution never accesses it. -/
  fpRegs : Nat → BitVec 64
  mem : BitVec width → BitVec 8
  memDomain : BitVec width → Prop
  pc : BitVec width
  lr : Nat
  align : Nat
  be : Bool
  failed : Bool

end Flapjack
