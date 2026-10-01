import Flapjack.Compiler.Encoders.Asm
import Flapjack.Compiler.Encoders.AsmSem.State

/-!
# Exact asmProps target record and target-state relation

Counterpart of `cakeml/compiler/encoders/asm/asmPropsScript.sml`'s `target`
record (`:44-56`) and `target_state_rel` (`:58-64`).

`'a word` is rendered as `BitVec width` with the reviewed `[NeZero width]`
discharge; the machine-state parameter `'b`/`state` and projection parameter
`'c`/`projection` stay polymorphic; `word64` is `BitVec 64`; `word8` is
`BitVec 8`; `('a word) set` is the predicate rendering `BitVec width → Prop`.
Note that several existing Flapjack machine carriers (e.g. WordSem/Lab)
render their domains as `BitVec width → Bool`; those are a different
translation, so a later relation converting between them is not part of this
module and remains to be proved.  `config` is the exact reviewed
`AsmConfigExact`.  This module supplies no evaluator.
-/

namespace Flapjack

open Flapjack.Compiler.Encoders.Asm

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
