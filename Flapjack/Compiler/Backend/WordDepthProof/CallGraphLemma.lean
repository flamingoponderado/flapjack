import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Leaves
import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Alloc
import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.If
import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Loop
import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Call

/-!
# `max_depth_call_graph_lemma`

Assembly of `word_depthProofScript.sml:147-788` `max_depth_call_graph_lemma`
from its 26 per-constructor cases by the tagged HOL `evaluate_ind`, as in the
HOL proof (`recInduct evaluate_ind`). HOL `OPTION_MAP2` is `WordDepth.optionMap₂`,
`stack_size` is `wordSemStackSize`, `subspt` is `sptSubspt`, and
`set ns SUBSET domain funs2` is "every element of `ns` has a successful lookup
in `funs2`".
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact

namespace CallGraphLemmaWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CallGraphLemmaWitnesses

open CallGraphLemmaWitnesses

/-- Every program and state satisfies the lemma's conclusion, by `evaluate_ind`
over the 26 cases (Flapjack infrastructure for the tagged statement). -/
theorem depthPost_all {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      depthPost prog s :=
  evaluate_ind (fun p s => depthPost p s)
    ⟨fun s => maxDepthCallGraphLemma_Skip s,
     fun n names s => maxDepthCallGraphLemma_Alloc n names s,
     fun t1 t2 a o ws s => maxDepthCallGraphLemma_StoreConsts t1 t2 a o ws s,
     fun pri moves s => maxDepthCallGraphLemma_Move pri moves s,
     fun i s => maxDepthCallGraphLemma_Inst i s,
     fun v e s => maxDepthCallGraphLemma_Assign v e s,
     fun v name s => maxDepthCallGraphLemma_Get v name s,
     fun v e s => maxDepthCallGraphLemma_Set v e s,
     fun b dst src s => maxDepthCallGraphLemma_OpCurrHeap b dst src s,
     fun e v s => maxDepthCallGraphLemma_Store e v s,
     fun s => maxDepthCallGraphLemma_Tick s,
     fun p s ih => maxDepthCallGraphLemma_MustTerminate p s ih,
     fun c1 c2 s ih => maxDepthCallGraphLemma_Seq c1 c2 s ih,
     fun n ms s => maxDepthCallGraphLemma_Return n ms s,
     fun n s => maxDepthCallGraphLemma_Raise n s,
     fun k s => maxDepthCallGraphLemma_Break k s,
     fun k s => maxDepthCallGraphLemma_Continue k s,
     fun cmp r1 ri c1 c2 s ih => maxDepthCallGraphLemma_If cmp r1 ri c1 c2 s ih,
     fun names c exitNames s ih => maxDepthCallGraphLemma_Loop names c exitNames s ih,
     fun r l1 s => maxDepthCallGraphLemma_LocValue r l1 s,
     fun ptr len dptr dlen names s => maxDepthCallGraphLemma_Install ptr len dptr dlen names s,
     fun r1 r2 s => maxDepthCallGraphLemma_CodeBufferWrite r1 r2 s,
     fun r1 r2 s => maxDepthCallGraphLemma_DataBufferWrite r1 r2 s,
     fun fi p1 l1 p2 l2 names s => maxDepthCallGraphLemma_FFI fi p1 l1 p2 l2 names s,
     fun op v e s => maxDepthCallGraphLemma_ShareInst op v e s,
     fun ret dest args h s ih => maxDepthCallGraphLemma_Call ret dest args h s ih⟩

/-- Full original `max_depth_call_graph_lemma` (`word_depthProofScript.sml:147-788`):
`!prog s res s1 funs n ns funs2. evaluate (prog, s) = (res,s1) /\ subspt funs funs2 /\
subspt funs2 s.code /\ s.locals_size = lookup n s.stack_size /\ res <> SOME Error /\
MEM n ns /\ ALL_DISTINCT ns /\ set ns SUBSET domain funs2 ==>
option_le s1.stack_max (OPTION_MAP2 MAX s.stack_max (OPTION_MAP2 (+) (stack_size s.stack)
  (OPTION_MAP2 MAX (max_depth_graphs s.stack_size ns ns funs funs2)
    (max_depth s.stack_size (call_graph funs n ns (size funs2) prog))))) /\
(max_depth_graphs s.stack_size ns ns funs funs2 <> NONE /\
 max_depth s.stack_size (call_graph funs n ns (size funs2) prog) <> NONE ==>
 s1.stack_size = s.stack_size /\
 ((res = NONE \/ (?k. res = SOME (Break k)) \/ (?k. res = SOME (Continue k))) ==>
  s1.locals_size = s.locals_size))`. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_call_graph_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem maxDepthCallGraphLemma {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
      (funs : Spt (Nat × WordLangProgHOL (BitVec width))) (n : Nat) (ns : List Nat)
      (funs2 : Spt (Nat × WordLangProgHOL (BitVec width))),
      evaluate prog s = (res, s1) ∧ sptSubspt funs funs2 ∧ sptSubspt funs2 s.code ∧
        s.localsSize = sptLookup n s.stackSize ∧ res ≠ some .error ∧ n ∈ ns ∧ ns.Nodup ∧
        (∀ x, x ∈ ns → (sptLookup x funs2).isSome = true) →
      optionLe s1.stackMax
          (optionMap₂ max s.stackMax
            (optionMap₂ (· + ·) (wordSemStackSize s.stack)
              (optionMap₂ max (maxDepthGraphs s.stackSize ns ns funs funs2)
                (maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) prog))))) ∧
        (maxDepthGraphs s.stackSize ns ns funs funs2 ≠ none ∧
            maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) prog) ≠ none →
          s1.stackSize = s.stackSize ∧
            (res = none ∨ (∃ k, res = some (.break k)) ∨ (∃ k, res = some (.continue k)) →
              s1.localsSize = s.localsSize)) := by
  intro prog s res s1 funs n ns funs2 ⟨hev, hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
  have h := depthPost_all prog s funs n ns funs2
    ⟨hsub, hcode, hloc, by rw [hev]; exact herr, hmem, hnd, hdom⟩
  rw [hev] at h
  exact h

end Flapjack.Compiler.Backend.WordDepthProof
