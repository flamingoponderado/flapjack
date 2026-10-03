import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.AllocStore
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Calls
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Install

/-!
# `stack_allocProof` `comp_correct`

The assembled `comp_correct` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (5297-5894): the
`stack_alloc` program transformation `comp` is simulated by the native StackSem
evaluator, from the source's compiled-state override and with extended
registers. HOL proves it by `recInduct evaluate_ind`; here the induction is on
the same evaluation measure (clock, then program size) that defines the native
evaluator, and the cases are those of `CompCorrect/`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

namespace CompCorrect

/-- Canonical codec for the imported owning StackSem state carrier. -/
theorem holFmapAsFiniteSupportWitness' {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- `comp_correct` for every program and state, by induction on the evaluation
measure, dispatching to HOL's per-constructor cases. -/
theorem goal_all {width : Nat} [NeZero width] {C F : Type} (anything : WordSemGcFun width)
    (cr : CompileFn width C) :
    ∀ (mm : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = mm → Goal anything cr p s := by
  intro mm
  induction mm using EvaluateAddClock.lexNat_wf.induction with
  | _ mm ih =>
  intro p s hm
  subst hm
  have ihp : IH anything cr p s := fun q u hlt => ih _ hlt q u rfl
  cases p with
  | skip => exact goal_skip anything cr s
  | halt v => exact goal_halt anything cr s v
  | tick => exact goal_tick anything cr s
  | ret v => exact goal_ret anything cr s v
  | raise v => exact goal_raise anything cr s v
  | «break» v => exact goal_break anything cr s v
  | «continue» v => exact goal_continue anything cr s v
  | inst i => exact goal_inst anything cr s i
  | get v name => exact goal_get anything cr s v name
  | set name v => exact goal_set anything cr s name v
  | opCurrHeap b v src => exact goal_opCurrHeap anything cr s b v src
  | alloc k => exact goal_alloc anything cr s k
  | storeConsts t1 t2 stub => exact goal_storeConsts anything cr s t1 t2 stub
  | seq c1 c2 => exact goal_seq anything cr s c1 c2 ihp
  | ite cmp r1 ri c1 c2 => exact goal_ite anything cr s cmp r1 ri c1 c2 ihp
  | loop c1 => exact goal_loop anything cr s c1 ihp
  | jumpLower r1 r2 dest => exact goal_jumpLower anything cr s r1 r2 dest ihp
  | rawCall dest => exact goal_rawCall anything cr s dest ihp
  | call ret dest handler =>
      rcases ret with _ | ⟨retH, link, l1, l2⟩
      · exact goal_call_none anything cr s dest handler ihp
      · exact goal_call_some anything cr s retH link l1 l2 dest handler ihp
  | install a b c d e => exact goal_install anything cr s a b c d e
  | shMemOp op v addr => exact goal_shMemOp anything cr s op v addr
  | codeBufferWrite a b => exact goal_codeBufferWrite anything cr s a b
  | dataBufferWrite a b => exact goal_dataBufferWrite anything cr s a b
  | ffi fi p1 p2 p3 p4 p5 => exact goal_ffi anything cr s fi p1 p2 p3 p4 p5
  | locValue v l1 l2 => exact goal_locValue anything cr s v l1 l2
  | stackAlloc k => exact goal_stackAlloc anything cr s k
  | stackFree k => exact goal_stackFree anything cr s k
  | stackLoad a k => exact goal_stackLoad anything cr s a k
  | stackLoadAny a rn => exact goal_stackLoadAny anything cr s a rn
  | stackStore a k => exact goal_stackStore anything cr s a k
  | stackStoreAny a rn => exact goal_stackStoreAny anything cr s a rn
  | stackGetSize a => exact goal_stackGetSize anything cr s a
  | stackSetSize a => exact goal_stackSetSize anything cr s a
  | bitmapLoad a v => exact goal_bitmapLoad anything cr s a v

end CompCorrect

open CompCorrect in
/-- Exact HOL `comp_correct` (`stack_allocProofScript.sml:5297-5894`), with all
twelve source premises and the four-part existential conclusion. HOL's free
`anything` and `compile_rest` are implicit and its `!p s r t m n c regs` are
explicit, in source order. The bound variables of the oracle premise and of the
compiler lambda are renamed `i k q` and `cfg` (HOL reuses `n`, `p` and `c`);
`dimword (:'a)` is `2 ^ width`, `dimindex (:'a) DIV 8` is `width / 8`,
`(I ## MAP prog_comp ## I) o oracle` is
`Prod.map id (Prod.map (List.map progComp) id) ∘ oracle`, `MEM` is list
membership, `SUBMAP` is `HolFiniteMapExact.submap` and `fromAList`/`toAList`/
`lookup` are the `Spt` renderings. The evaluator is the native StackSem
`evaluate`, whose instruction closure inherits the `reals_as_rational_cuts`
limit (`docs/SOUNDNESS.md` item 8). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct {width : Nat} [NeZero width] {C F : Type}
    {anything : WordSemGcFun width}
    {compile_rest : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} :
    ∀ (p : HolProg width) (s : StackSemStateFiniteExact width C F)
      (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F) (m n : Nat)
      (c : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW width)),
      evaluate (p, s) = (r, t) ∧ r ≠ some .error ∧ StackProps.allocArg p ∧
      (∀ k prog, sptLookup k s.code = some prog →
        k ≠ gcStubLocation ∧ StackProps.allocArg prog) ∧
      (∀ (i k : Nat) (q : HolProg width), (k, q) ∈ (s.compileOracle i).2.1 →
        k ≠ gcStubLocation ∧ StackProps.allocArg q) ∧
      s.gcFun = wordGcFun c ∧ s.useAlloc = true ∧
      s.stack.length * (width / 8) < 2 ^ width ∧
      s.regs.submap regs ∧
      s.useStack = true ∧
      s.bitmaps.length + s.dataBuffer.buffer.length + s.dataBuffer.spaceLeft < 2 ^ width - 1 ∧
      s.compile = (fun cfg => compile_rest cfg ∘ List.map progComp) →
      ∃ ck regs1,
        evaluate ((comp n m p).1, { s with
            useStore := true, useStack := true, useAlloc := false
            clock := s.clock + ck, regs := regs, gcFun := anything
            compileOracle := Prod.map id (Prod.map (List.map progComp) id) ∘ s.compileOracle
            compile := compile_rest
            code := sptFromAList (compile c (sptToAList s.code)) }) =
          (r, { t with
            useStore := true, useStack := true, useAlloc := false
            regs := regs1, gcFun := anything
            compileOracle := Prod.map id (Prod.map (List.map progComp) id) ∘ t.compileOracle
            compile := compile_rest
            code := sptFromAList (compile c (sptToAList t.code)) }) ∧
        t.regs.submap regs1 ∧
        t.bitmaps.length + t.dataBuffer.buffer.length + t.dataBuffer.spaceLeft < 2 ^ width - 1 ∧
        ((∀ w, r ≠ some (.halt w)) → t.stack.length * (width / 8) < 2 ^ width) := by
  rintro p s r t m n c regs ⟨h, hr, ha, hcode, horacle, hgc, hA, hst, hsub, hK, hbuf, hC⟩
  exact goal_all anything compile_rest _ p s rfl r t m n c regs h hr ha
    ⟨hcode, horacle, hgc, hA, hst, hsub, hK, hbuf, hC⟩

end Flapjack.Compiler.Backend.StackAlloc
