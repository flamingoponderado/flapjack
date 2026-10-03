import Flapjack.Compiler.Backend.Semantics.StackSem.State
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackRel
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackSize
import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.Compiler.Backend.WordToStack.NativeStubs
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.GcFunOk
import Flapjack.Misc.GoodDimindex
import Flapjack.Pancake.WordConvs

namespace Flapjack.WordToStackProofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native

/-- Canonical exact source-state roundtrip; representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical exact target-state roundtrip; representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original state relation, including every compiler callback/oracle,
code-domain/stub, memory/store/FFI, resource bound, stack abstraction and local
placement conjunct. Exact source config is Nat × C, target config C; the FFI
host is shared. The compiler is the native generic compiler with perf=false.
No successful compiler call or poststate relation is supplied as a premise.
Total HOL HD and EL retain their shared unspecified values; the original
nonempty bitmap guard remains. Named finite-map fields use canonical codecs,
while locals/code/stackSize remain native sptrees. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
noncomputable def stateRel {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f f' : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (lens : List Nat) (extra : Nat) : Prop :=
  s.clock = t.clock ∧ s.gcFun = t.gcFun ∧ s.permute = (fun _ => id) ∧
  t.ffi = s.ffi ∧ t.useStack = true ∧ t.useStore = true ∧ t.useAlloc = true ∧
  t.memory = s.memory ∧ t.mdomain = s.mdomain ∧ 4 < k ∧ t.shMdomain = s.shMdomain ∧
  s.store = t.store.eraseEq .handler ∧ wordGcFunOk t.gcFun ∧ s.termdep = 0 ∧
  t.be = s.be ∧ t.ffi = s.ffi ∧ t.store.lookup .handler ≠ none ∧
  t.fpRegs = s.fpRegs ∧ t.dataBuffer = s.dataBuffer ∧ t.codeBuffer = s.codeBuffer ∧
  s.compile = (fun (bm0, cfg) progs =>
    let (progs, _, bm) := compileWordToStackNative ac false k progs (.nil, bm0)
    (t.compile cfg progs).map (fun (bytes, cfg) => (bytes, appListAppend bm.1, (bm.2, cfg)))) ∧
  t.compileOracle = (fun n =>
    let ((bm0, cfg), progs) := s.compileOracle n
    let (progs, _, bm) := compileWordToStackNative ac false k progs (.nil, bm0)
    (cfg, progs, appListAppend bm.1)) ∧
  (∀ n,
    let ((bm0, _), progs) := s.compileOracle n
    progs.all (fun p => postAllocConventionsHOL k p.2.2) = true ∧
    progs.all (fun p => flatExpConventions p.2.2) = true ∧
    progs.all (fun p => decide (p.1 ≠ raiseStubLocation)) = true ∧
    progs.all (fun p => decide (p.1 ≠ storeConstsStubLocation)) = true ∧
    (n = 0 → bm0 = t.bitmaps.length)) ∧
  sptDomain t.code = (fun n => n = raiseStubLocation ∨ n = storeConstsStubLocation ∨ sptDomain s.code n) ∧
  (∀ n wordProg argumentCount,
    sptLookup n s.code = some (argumentCount, wordProg) →
    postAllocConventionsHOL k wordProg = true ∧ flatExpConventions wordProg = true ∧
    ∃ (bs : AppList (BitVec width)) (i : Nat) (bs2 : AppList (BitVec width))
      (i2 frame : Nat) (stackProg : Compiler.Backend.StackLang.HolProg width),
      compileProgNative ac false wordProg argumentCount k (bs, i) = (stackProg, frame, (bs2, i2)) ∧
      (appListAppend bs).length ≤ i ∧ i - (appListAppend bs).length ≤ t.bitmaps.length ∧
      List.IsPrefix (appListAppend bs2) (t.bitmaps.drop (i - (appListAppend bs).length)) ∧
      sptLookup n t.code = some stackProg ∧ (sptLookup n s.stackSize).getD frame = frame) ∧
  sptLookup raiseStubLocation t.code = some (raiseStubNative false k) ∧
  sptLookup storeConstsStubLocation t.code = some (storeConstsStubNative k) ∧
  goodDimindex width ∧ 8 ≤ width ∧
  t.bitmaps.length + s.dataBuffer.buffer.length + s.dataBuffer.spaceLeft + 1 < 2 ^ width ∧
  1 ≤ t.bitmaps.length ∧ Flapjack.holHd t.bitmaps = (4 : BitVec width) ∧
  t.stackSpace + f ≤ t.stack.length ∧ t.stack.length < 2 ^ width ∧
  (if f' = 0 then f = 0 else f = f' + 1) ∧ sptWf s.locals = true ∧
  stackSizeRel f s.localsSize s.stackLimit s.stackMax s.stack t.stack t.stackSpace extra ∧
  (let stack := t.stack.drop (t.stackSpace + extra)
   let currentFrame := stack.take f
   let restOfStack := stack.drop f
   stackRel k s.handler s.stack (t.store.lookup .handler) restOfStack t.stack.length t.bitmaps lens ∧
   ∀ n v, sptLookup n s.locals = some v →
     n % 2 = 0 ∧
     if n / 2 < k then t.regs.lookup (n / 2) = some v
     else currentFrame[f - 1 - (n / 2 - k)]? = some v ∧ n / 2 < k + f')

end Flapjack.WordToStackProofs
