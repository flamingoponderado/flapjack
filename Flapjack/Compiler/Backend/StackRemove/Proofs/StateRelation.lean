import Flapjack.Compiler.Backend.StackRemove.Proofs.CodeRelation
import Flapjack.Compiler.Backend.StackRemove.Proofs.Memory
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordStore
import Flapjack.Compiler.Backend.StackRemove.ProgComp
import Flapjack.Compiler.Backend.Semantics.StackSem.State
import Flapjack.Misc.WordList
import Flapjack.Misc.GoodDimindex

/-! Complete native StackRemove state relation. Both states use the evaluator's
existing StackSem carrier, including canonical finite maps and Spt code. HOL
sets are predicates; Boolean state domains denote their true entries. The
compile configuration and FFI host remain independently quantified. -/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack

/-- Canonical codec for the imported evaluator state; no duplicate carrier or
assumed representation relation is introduced. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original relation, including compile/oracle transport, every flag and
shared field, all bounds and register conditions, and the five separated heap
assertions. The source's local num_stubs means stackNumStubs, not wordNumStubs.
No successful evaluation, finite memory domain, heap representation, or stack
safety hypothesis is substituted for a conjunct of the definition. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
noncomputable def stateRelHOL {width : Nat} [NeZero width] {C : Type} {F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) : Prop :=
  source.useStack = true ∧ source.useStore = true ∧
  target.useStack = false ∧ target.useStore = false ∧
  target.useAlloc = false ∧ source.useAlloc = false ∧
  target.be = source.be ∧ target.gcFun = source.gcFun ∧
  target.clock = source.clock ∧ target.ffi = source.ffi ∧
  target.ffiSaveRegs = source.ffiSaveRegs ∧ target.fpRegs = source.fpRegs ∧
  target.codeBuffer = source.codeBuffer ∧ target.shMdomain = source.shMdomain ∧
  source.compile = (fun config program =>
    target.compile config (program.map (progComp jump bounds pointer))) ∧
  target.compileOracle = (fun index =>
    let oracle := source.compileOracle index
    (oracle.1, oracle.2.1.map (progComp jump bounds pointer), oracle.2.2)) ∧
  (∀ index name program, (name, program) ∈ (source.compileOracle index).2.1 →
    StackProps.regBound program pointer ∧ stackNumStubs ≤ name + 1) ∧
  goodDimindex width ∧
  (∀ register, register < pointer →
    target.regs.lookup register = source.regs.lookup register) ∧
  codeRelHOL jump bounds pointer source.code target.code ∧
  sptLookup stackErrLab target.code = some (haltInst (BitVec.ofNat width 2)) ∧
  target.regs.lookup (pointer + 2) = source.store.lookup .currHeap ∧
  (∀ register, register = pointer ∨ register = pointer + 1 ∨ register = pointer + 2 →
    target.ffiSaveRegs register = true) ∧
  isSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) = true ∧
  source.stackSpace ≤ source.stack.length ∧
  (let bitmapBase := theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width
   let allBitmaps := source.bitmaps ++ source.dataBuffer.buffer
   source.dataBuffer.position = bitmapBase + bytesInWord width * BitVec.ofNat width source.bitmaps.length ∧
   match target.regs.lookup (pointer + 1) with
   | some (.word base) =>
     width / 8 * maxStackAlloc ≤ base.toNat ∧
     base.toNat + (bytesInWord width).toNat * source.stack.length < 2 ^ width ∧
     target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) ∧
     SetSep.star
       (SetSep.star
         (SetSep.star
           (SetSep.star (memoryHOL source.memory (fun address => source.mdomain address = true))
             (Misc.wordList bitmapBase (allBitmaps.map WordLocW.word)))
           (Misc.wordListExists (bitmapBase + bytesInWord width * BitVec.ofNat width allBitmaps.length)
             source.dataBuffer.spaceLeft))
         (wordStoreHOL base source.store))
       (Misc.wordList base source.stack)
       (SetSep.fun2Set (target.memory, fun address => target.mdomain address = true))
   | _ => False)

end Flapjack.Compiler.Backend.StackRemove
