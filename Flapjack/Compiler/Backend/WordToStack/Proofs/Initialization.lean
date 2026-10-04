import Flapjack.Compiler.Backend.Semantics.StackSem.State
import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.Misc.Sptree.Mapi

namespace Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Imported native target-state codec roundtrips. This is Flapjack canonical
finite-map representation infrastructure, not an independent HOL theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : StackSemStateBroad width C F) (h : s.FiniteSupport),
      (StackSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Imported native source-state codec roundtrips at the original bitmap/config
product carrier. This is Flapjack representation infrastructure only. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width (Nat × C) F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width (Nat × C) F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Complete original Word-to-Stack source-state initializer. The source compile
configuration is the bitmap-counter/target-config pair; native compilation
threads both the complete bitmap AppList and returned target configuration.
The canonical finite-map qualifier covers only transferred fp/store fields of
the imported owners. Source locals/code/frame sizes remain exact Spt trees.
This definition does not establish init_state_ok or the held state relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def makeInit {width : Nat} [NeZero width] {C F : Type}
    (conf : AsmConfigExact width) (k : Nat) (t : StackSemStateFiniteExact width C F)
    (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    WordSemStateFiniteExact width (Nat × C) F where
  locals := sptInsert 0 (.loc 1 0) .ln
  fpRegs := t.fpRegs
  store := t.store.eraseEq .handler
  stack := []
  memory := t.memory
  mdomain := t.mdomain
  shMdomain := t.shMdomain
  permute := fun _ n => n
  gcFun := t.gcFun
  handler := 0
  clock := t.clock
  code := code
  dataBuffer := t.dataBuffer
  codeBuffer := t.codeBuffer
  compile := fun (bm0,cfg) progs =>
    let (progs,_,bm) := compileWordToStackNative conf false k progs (.nil,bm0)
    (t.compile cfg progs).map fun (bytes,cfg) =>
      (bytes,appListAppend bm.1,(bm.2,cfg))
  compileOracle := coracle
  be := t.be
  ffi := t.ffi
  termdep := 0
  stackLimit := t.stack.length
  stackMax := wordSemStackSize ([] : List (WordSemStackFrame width))
  stackSize := sptMapi (fun _ (argc,prog) =>
    (compileProgNative conf false prog argc k (.nil,0)).2.1) code
  localsSize := some 0

end Flapjack.Compiler.Backend.WordToStack.Native.Initialization
