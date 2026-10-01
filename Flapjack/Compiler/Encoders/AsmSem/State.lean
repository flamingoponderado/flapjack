import Flapjack.Compiler.Backend.Semantics.TargetSem.State

/-!
# Exact asmSem state carrier and asmProps target-state relation

Counterparts of `cakeml/compiler/encoders/asm/asmSemScript.sml:12-23`
(`asm_state`) and `cakeml/compiler/encoders/asm/asmPropsScript.sml:58-64`
(`target_state_rel`).  These are the machine-state carriers on which
`targetSem`'s `good_init_state` is stated.

`'a word` is rendered as `BitVec width` ([NeZero width]); `word8` as
`BitVec 8`; `word64` as `BitVec 64`; `reg` as `Nat`; `('a word) set` as the
existing predicate rendering `BitVec width → Prop`.  This module supplies no
evaluator and no `target_configured`/`good_init_state`.
-/

namespace Flapjack

open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `Datatype: asm_state = <| regs : num -> 'a word ;
    fp_regs : num -> word64 ; mem : 'a word -> word8 ;
    mem_domain : 'a word set ; pc : 'a word ; lr : reg ; align : num ;
    be : bool ; failed : bool |>` (`cakeml/compiler/encoders/asm/asmSemScript.sml:12-23`),
    field order preserved. -/
@[hol "cakeml/compiler/encoders/asm/asmSemScript.sml" "asm_state"
  (words_as_type_indexed_bitvec)]
structure AsmState (width : Nat) [NeZero width] where
  regs : Nat → BitVec width
  fpRegs : Nat → BitVec 64
  mem : BitVec width → BitVec 8
  memDomain : BitVec width → Prop
  pc : BitVec width
  lr : Nat
  align : Nat
  be : Bool
  failed : Bool

/-- Exact HOL `target_state_rel t s ms <=> t.state_ok ms /\ t.get_pc ms = s.pc
    /\ (!a. a IN s.mem_domain ==> t.get_byte ms a = s.mem a)
    /\ (!i. i < t.config.reg_count /\ ~MEM i t.config.avoid_regs ==>
          t.get_reg ms i = s.regs i)
    /\ (!i. i < t.config.fp_reg_count ==> t.get_fp_reg ms i = s.fp_regs i)`
    (`cakeml/compiler/encoders/asm/asmPropsScript.sml:58-64`), argument order
    `t s ms` preserved over the exact `HolAsmTarget`/`AsmState` carriers. -/
@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "target_state_rel_def"
  (words_as_type_indexed_bitvec)]
def targetStateRel {width : Nat} [NeZero width] {state projection : Type}
    (t : HolAsmTarget width state projection) (s : AsmState width) (ms : state) : Prop :=
  t.stateOk ms = true ∧
    t.getPc ms = s.pc ∧
    (∀ a, s.memDomain a → t.getByte ms a = s.mem a) ∧
    (∀ i, i < t.config.regCount ∧ t.config.avoidRegs.contains i = false →
      t.getReg ms i = s.regs i) ∧
    (∀ i, i < t.config.fpRegCount → t.getFpReg ms i = s.fpRegs i)

end Flapjack
