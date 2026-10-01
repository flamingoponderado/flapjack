import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Alloc
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Call
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.FFI
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.If
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Inst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Install
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Loop
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MoveStoreConsts
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MustTerminate
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Seq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.ShareInst

/-!
# `evaluate_apply_colour`

Assembly of `word_allocProofScript.sml:1105-1163` `evaluate_apply_colour` from
its `Resume` cases (`EvaluateApplyColour/*`). HOL proves the theorem by
complete induction on `prog_size`; every case uses the induction hypothesis
only at sub-programs, so the assembly recurses structurally on the program.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateApplyColourWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateApplyColourWitnesses

open EvaluateApplyColourWitnesses

/-- `evaluate_apply_colour` at every program, by structural recursion over the
per-constructor cases (Flapjack infrastructure for the tagged assembly; the
recursive calls are exactly the sub-program induction hypotheses). -/
theorem applyColourGoal_all {width : Nat} [NeZero width] {C F : Type} :
    ∀ prog : WordLangProgHOL (BitVec width), applyColourGoal C F prog
  | .skip => evaluateApplyColour_Skip
  | .move pri moves => evaluateApplyColour_Move pri moves
  | .inst i => evaluateApplyColour_Inst i
  | .assign v e => evaluateApplyColour_Assign v e
  | .get v name => evaluateApplyColour_Get v name
  | .set name e => evaluateApplyColour_Set name e
  | .store e v => evaluateApplyColour_Store e v
  | .mustTerminate body => evaluateApplyColour_MustTerminate body (applyColourGoal_all body)
  | .call none dest args none =>
      evaluateApplyColour_Call none dest args none (fun _ _ _ _ _ h => nomatch h)
        (fun _ _ _ _ h => nomatch h)
  | .call none dest args (some (v, hp, l1, l2)) =>
      evaluateApplyColour_Call none dest args (some (v, hp, l1, l2))
        (fun _ _ _ _ _ h => nomatch h)
        (fun _ _ _ _ h => by cases h; exact applyColourGoal_all hp)
  | .call (some (n, names, rh, l1, l2)) dest args none =>
      evaluateApplyColour_Call (some (n, names, rh, l1, l2)) dest args none
        (fun _ _ _ _ _ h => by cases h; exact applyColourGoal_all rh)
        (fun _ _ _ _ h => nomatch h)
  | .call (some (n, names, rh, l1, l2)) dest args (some (v, hp, l1', l2')) =>
      evaluateApplyColour_Call (some (n, names, rh, l1, l2)) dest args (some (v, hp, l1', l2'))
        (fun _ _ _ _ _ h => by cases h; exact applyColourGoal_all rh)
        (fun _ _ _ _ h => by cases h; exact applyColourGoal_all hp)
  | .seq c1 c2 => evaluateApplyColour_Seq c1 c2 (applyColourGoal_all c1) (applyColourGoal_all c2)
  | .ite cmp r ri c1 c2 =>
      evaluateApplyColour_If cmp r ri c1 c2 (applyColourGoal_all c1) (applyColourGoal_all c2)
  | .loop names body exitNames =>
      evaluateApplyColour_Loop names body exitNames (applyColourGoal_all body)
  | .alloc n names => evaluateApplyColour_Alloc n names
  | .storeConsts a b c d ws => evaluateApplyColour_StoreConsts a b c d ws
  | .raise n => evaluateApplyColour_Raise n
  | .return n ms => evaluateApplyColour_Return n ms
  | .break k => evaluateApplyColour_Break k
  | .continue k => evaluateApplyColour_Continue k
  | .tick => evaluateApplyColour_Tick
  | .opCurrHeap b dst src => evaluateApplyColour_OpCurrHeap b dst src
  | .locValue r l1 => evaluateApplyColour_LocValue r l1
  | .install ptr len dptr dlen (n1, n2) => evaluateApplyColour_Install ptr len dptr dlen n1 n2
  | .codeBufferWrite r1 r2 => evaluateApplyColour_CodeBufferWrite r1 r2
  | .dataBufferWrite r1 r2 => evaluateApplyColour_DataBufferWrite r1 r2
  | .ffi fi p1 l1 p2 l2 (n1, n2) => evaluateApplyColour_FFI fi p1 l1 p2 l2 n1 n2
  | .shareInst op v e => evaluateApplyColour_ShareInst op v e

/-- Exact HOL `evaluate_apply_colour` (`word_allocProofScript.sml:1105-1163`): for
every program, related states, colour and live set satisfying `colouring_ok`,
`word_state_eq_rel` and `strong_locals_rel` on `get_live`, some source
permutation oracle makes the source run either fail or agree with the coloured
run on the result, `word_state_eq_rel` and the live-scoped locals relation. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st cst : WordSemStateFiniteExact width C F)
      (f : Nat → Nat) (live : NumSet) (lt : List (NumSet × NumSet)),
      colouringOk f prog live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive prog live lt)) st.locals cst.locals →
      applyColourPost f prog live lt st cst :=
  fun prog => applyColourGoal_all prog

end Flapjack.WordAlloc
