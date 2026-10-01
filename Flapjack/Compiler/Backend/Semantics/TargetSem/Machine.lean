import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Encoders.AsmSem.State
import Flapjack.Pancake.Semantics.LoopSem

/-!
# Exact targetSem machine predicates

Counterpart of the small definitions in
`cakeml/compiler/backend/semantics/targetSemScript.sml` that sit on top of the
`machine_config`/`target` carriers from `TargetSem/State.lean`:

* `code_loaded_def` (`:238-243`),
* `target_configured_def` (`:247-261`),
* `get_reg_value_def` (`:263-266`).

`read_bytearray` is the reviewed tagged `readBytearrayWordHOL`
(`Flapjack/Pancake/Semantics/LoopSem.lean`, HOL `misc$read_bytearray_def`),
with `word8` rendered as `BitVec 8`.

The HOL `machine_config`/`asm_state` address sets are rendered as predicates
`BitVec width → Prop` (the carriers' reviewed translation); membership is
therefore decided classically inside `codeLoaded`, not exposed as a translation
binder. This module supplies no evaluator and no `machine_sem`/`good_init_state`.
-/

namespace Flapjack

open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `get_reg_value_def`
    (`cakeml/compiler/backend/semantics/targetSemScript.sml:263-266`):
    `get_reg_value NONE w _ = w` / `get_reg_value (SOME v) _ f = f v`.
    HOL leaves both the key and the value type fully generic, so this is
    polymorphic in both, with no word qualifier. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "get_reg_value_def"]
def getRegValue {key value : Type} (argument : Option key) (fallback : value)
    (lookup : key → value) : value :=
  match argument with
  | none => fallback
  | some register => lookup register

/-- Exact HOL `code_loaded_def`
    (`cakeml/compiler/backend/semantics/targetSemScript.sml:238-243`):
    `read_bytearray (mc.target.get_pc ms) (LENGTH bytes)
       (\a. if a IN mc.prog_addresses then SOME (mc.target.get_byte ms a) else NONE)
     = SOME bytes`. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "code_loaded_def"
  (words_as_type_indexed_bitvec)]
noncomputable def codeLoaded {width : Nat} [NeZero width] {state projection : Type}
    (bytes : List (BitVec 8)) (mc : MachineConfig width state projection) (ms : state) :
    Prop :=
  open Classical in
  readBytearrayWordHOL (byteWidth := 8) (mc.target.getPc ms) bytes.length
    (fun address =>
      if mc.progAddresses address then some (mc.target.getByte ms address) else none) =
    some bytes

/-- Exact HOL `target_configured_def`
    (`cakeml/compiler/backend/semantics/targetSemScript.sml:247-261`): the
    assembler state `t` is compatible with the machine configuration
    `mc_conf`. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "target_configured_def"
  (words_as_type_indexed_bitvec)]
def targetConfigured {width : Nat} [NeZero width] {state projection : Type}
    (t : AsmState width) (mcConf : MachineConfig width state projection) : Prop :=
  t.failed = false ∧
    t.be = mcConf.target.config.bigEndian ∧
    t.align = mcConf.target.config.codeAlignment ∧
    t.memDomain = mcConf.progAddresses ∧
    (match mcConf.target.config.linkReg with
     | none => True
     | some register => t.lr = register)

end Flapjack
