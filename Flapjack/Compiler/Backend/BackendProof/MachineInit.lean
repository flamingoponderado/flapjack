import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Backend.StackNames.OperandNames
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory
import Flapjack.Misc.Alignment
import Flapjack.Misc.Bit
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.WordList
import Flapjack.Misc.SetSep

/-! backendProofScript.sml: the machine-initialisation predicates and small
word lemmas used by the Pancake top-level correctness theorem
(`pan_to_targetProof$pan_to_target_compile_semantics`). HOL's `find_name` is
the `tlookup` overload of stack_names, rendered `findNameSpt`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackNames

/-- Exact HOL `backendProof$mc_init_ok_def` (`backendProofScript.sml:113-131`):
the three heap registers 2, 3, 4 (offset by `reg_count - (LENGTH avoid_regs + 5)`)
are callee saved, `find_name` maps 0-4 to the link/ptr/len/ptr2/len2 registers,
the data endianness is the target's, the link register is distinct from the four
pointer registers and not callee saved, and `asm_conf` is the target
configuration. HOL's `EVERY` over `[2;3;4]` is a membership quantifier and its
`case link_reg of NONE => 0 | SOME n => n` is kept as a match. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "mc_init_ok_def"
  (words_as_type_indexed_bitvec)]
def mcInitOk {width : Nat} [NeZero width] {state projection : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (mc : MachineConfig width state projection) : Prop :=
  let link := match mc.target.config.linkReg with
    | none => 0
    | some n => n
  (∀ r ∈ [2, 3, 4], findNameSpt c.stackConf.regNames
      (r + mc.target.config.regCount - (mc.target.config.avoidRegs.length + 5)) ∈
        mc.calleeSavedRegs) ∧
  findNameSpt c.stackConf.regNames 4 = mc.len2Reg ∧
  findNameSpt c.stackConf.regNames 3 = mc.ptr2Reg ∧
  findNameSpt c.stackConf.regNames 2 = mc.lenReg ∧
  findNameSpt c.stackConf.regNames 1 = mc.ptrReg ∧
  findNameSpt c.stackConf.regNames 0 = link ∧
  c.dataConf.be = mc.target.config.bigEndian ∧
  link ≠ mc.lenReg ∧
  link ≠ mc.ptrReg ∧
  link ≠ mc.len2Reg ∧
  link ≠ mc.ptr2Reg ∧
  link ∉ mc.calleeSavedRegs ∧
  asmConf = mc.target.config

/-- Exact HOL `backendProof$heap_regs_def` (`backendProofScript.sml:170-173`):
`heap_regs reg_names = (find_name reg_names 2, find_name reg_names 4)`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "heap_regs_def"]
def heapRegs (regNames : Spt Nat) : Nat × Nat :=
  (findNameSpt regNames 2, findNameSpt regNames 4)

/-- Full original byte_aligned_MOD (`backendProofScript.sml:39-47`): under
`good_dimindex`, every byte-aligned word is a multiple of the word size in
bytes. HOL's set membership `x ∈ byte_aligned` is the Bool predicate. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "byte_aligned_MOD"
  (words_as_type_indexed_bitvec)]
theorem byteAlignedMOD {width : Nat} [NeZero width] (good : goodDimindex width) :
    ∀ x : BitVec width, holByteAligned x = true → x.toNat % (width / 8) = 0 := by
  intro x hx
  have hp : 2 ^ holLOG2 (width / 8) = width / 8 := by
    rcases good with h | h <;> subst h
    · rw [holLOG2_eq_log2 (by decide)]; decide
    · rw [holLOG2_eq_log2 (by decide)]; decide
  simp only [holByteAligned, holAligned, decide_eq_true_eq, holAlign_eq_div] at hx
  have ht := congrArg BitVec.toNat hx
  rw [BitVec.toNat_ofNat] at ht
  have hle : x.toNat / 2 ^ holLOG2 (width / 8) * 2 ^ holLOG2 (width / 8) ≤ x.toNat :=
    Nat.div_mul_le_self _ _
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle x.isLt)] at ht
  rw [← hp, ← ht, Nat.mul_mod_left]

/-- Full original word_list_exists_imp (`backendProofScript.sml:300-306`):
an address-range domain with the original size bound and good dimension
carries a word list over any memory function. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "word_list_exists_imp"
  (words_as_type_indexed_bitvec)]
theorem wordListExistsImp {width : Nat} [NeZero width] {β : Type}
    (dm : BitVec width → Prop) (a : BitVec width) (n : Nat) (m1 : BitVec width → β)
    (h : dm = StackRemove.addresses a n ∧ width / 8 * n < 2 ^ width ∧ goodDimindex width) :
    Misc.wordListExists a n (SetSep.fun2Set (m1, dm)) := by
  obtain ⟨rfl, bound, good⟩ := h
  exact StackRemove.Proofs.WordListMemory.wordListExistsAddresses m1 n a ⟨bound, good⟩

end Flapjack.Compiler.Backend.BackendProof
