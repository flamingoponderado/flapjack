import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Labels
import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Backend.StackToLab.Proofs.Prelude
import Flapjack.Compiler.Backend.LabSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

/-! Flatten helper lemmas and result views of `stack_to_labProofScript.sml`
(lines 890-1206), used by `flatten_correct`. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Basis.Pure.MlString

/-- `flatten` never decreases the next free label. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_leq"
  (words_as_type_indexed_bitvec)]
theorem flattenLeq {width : Nat} [NeZero width] :
    ∀ (t : Bool) (x : HolProg width) (y z : Nat) (cs bs : List Nat),
      z ≤ (flattenHOL t x y z cs bs).2.2 := by
  intro t x y z cs bs
  induction t, x, z, cs, bs using flattenHOL.induct y
  case case26 =>
    rw [flattenHOL]
    all_goals assumption
  all_goals
    rw [flattenHOL]
    try simp (config := { zetaDelta := true }) only [*] at *
  all_goals (try split_ifs) <;> (try simp_all) <;> omega

/-- A non-bad function return is present. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "NOT_bad_fun_return_IMP_SOME"
  (words_as_type_indexed_bitvec)]
theorem notBadFunReturnImpSome {width : Nat} [NeZero width] :
    ∀ q : Option (StackSemResult width), ¬StackSemControl.badFunReturn q = true →
      ∃ n, q = some n := by
  intro q h
  cases q with
  | none => simp [StackSemControl.badFunReturn] at h
  | some n => exact ⟨n, rfl⟩

/-- Every program's next label from 2 is at least 2. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "next_lab_non_zero" 1022
  (words_as_type_indexed_bitvec)]
theorem nextLabNonZero {width : Nat} [NeZero width] :
    ∀ p : HolProg width, 2 ≤ StackAlloc.nextLabHOL p 2 := by
  intro p
  rw [StackAlloc.next_lab_EQ_MAX p 0 2]
  omega

/-- The tail flag only affects `Seq`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_T_F"
  (words_as_type_indexed_bitvec)]
theorem flattenTF {width : Nat} [NeZero width] {p_2 : HolProg width} {p_1 m : Nat}
    {cs bs : List Nat} :
    ¬isSeqHOL p_2 = true → flattenHOL true p_2 p_1 m cs bs = flattenHOL false p_2 p_1 m cs bs := by
  intro h
  cases p_2 with
  | seq => simp [isSeqHOL] at h
  | call r d hd =>
    rcases r with _ | ⟨_, _, _, _⟩ <;> rcases hd with _ | ⟨_, _, _⟩ <;> simp only [flattenHOL]
  | _ => simp only [flattenHOL]

/-- An out-of-list `find_lab` result is the default zero. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "NOT_MEM_find_lab_IMP"]
theorem notMemFindLabImp : ∀ (bs : List Nat) (n : Nat), findLabHOL n bs ∉ bs → findLabHOL n bs = 0 := by
  intro bs n h
  unfold findLabHOL at *
  cases hn : bs[n]? with
  | none => simp
  | some v =>
    rw [hn] at h
    exact absurd (List.mem_of_getElem? hn) h

/-- A defined label position stays defined in an extended program. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "is_some_loc_to_pc_prefix"
  (words_as_type_indexed_bitvec)]
theorem isSomeLocToPcPrefix {width : Nat} [NeZero width] {n k : Nat}
    {c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))} :
    (locToPc n k c1).isSome ∧ c1 <+: c2 → (locToPc n k c2).isSome := by
  rintro ⟨some_, pre⟩
  obtain ⟨pc, hpc⟩ := Option.isSome_iff_exists.mp some_
  rw [locToPcIsPrefix n k c1 pc c2 ⟨hpc, pre⟩]
  rfl

/-- Pointwise form of `is_some_loc_to_pc_prefix`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "every_is_some_loc_to_pc_prefix"
  (words_as_type_indexed_bitvec)]
theorem everyIsSomeLocToPcPrefix {width : Nat} [NeZero width] {n : Nat} {cs : List Nat}
    {c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))} :
    (∀ k ∈ cs, (locToPc n k c1).isSome) ∧ c1 <+: c2 → ∀ k ∈ cs, (locToPc n k c2).isSome := by
  rintro ⟨all, pre⟩ k mem
  exact isSomeLocToPcPrefix ⟨all k mem, pre⟩

/-- Programs that `flatten` marks as not returning always produce a StackSem
result. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "no_ret_correct"
  (words_as_type_indexed_bitvec)]
theorem noRetCorrect {width : Nat} [NeZero width] {C F : Type} :
    ∀ (t : Bool) (p : HolProg width) (y z : Nat) (cs bs : List Nat),
      (flattenHOL t p y z cs bs).2.1 = true →
      ∀ s : StackSemStateFiniteExact width C F, (StackSemEvaluate.evaluate (p, s)).1.isSome := by
  intro t p y z cs bs
  induction t, p, z, cs, bs using flattenHOL.induct y
  all_goals intro hnr s
  case case26 =>
    rw [flattenHOL] at hnr
    all_goals first | assumption | simp at hnr
  all_goals rw [flattenHOL] at hnr
  all_goals try simp (config := { zetaDelta := true }) only [*] at *
  all_goals try (simp at hnr; done)
  all_goals try simp at hnr
  case case3 => rw [StackSemEvaluate.evaluate_halt]; split <;> rfl
  case case12 => rw [StackSemEvaluate.evaluate_raise]; split <;> rfl
  case case13 => rw [StackSemEvaluate.evaluate_ret]; split <;> rfl
  case case14 => rw [StackSemEvaluate.evaluate_break]; rfl
  case case15 => rw [StackSemEvaluate.evaluate_continue]; rfl
  case case4 =>
    rename_i ihFirst ihSecond
    rw [StackSemEvaluate.evaluate_seq]
    split
    · rename_i s1 heq
      have first := congrArg Prod.fst heq
      simp only [StackSemControl.fixClock] at first
      rcases hnr with h1 | h2
      · have := ihFirst h1 s; rw [first] at this; simp at this
      · exact ihSecond h2 _
    · rename_i res s1 hres heq
      have first := congrArg Prod.fst heq
      simp only [StackSemControl.fixClock] at first
      cases res with
      | none => exact absurd rfl hres
      | some r => rfl
  case case8 =>
    rename_i ihThen ihElse
    rw [StackSemEvaluate.evaluate_ite]
    repeat' split
    all_goals first | rfl | exact ihThen trivial _ | exact ihElse hnr _
  case case16 =>
    rw [StackSemEvaluate.evaluate_rawCall]
    repeat' split
    all_goals first | rfl |
      (rename_i hb; obtain ⟨n, hn⟩ := notBadFunReturnImpSome _ hb; simp [hn])
  case case17 =>
    simp only [StackSemEvaluate.evaluate_call]
    repeat' split
    all_goals first | rfl |
      (rename_i hb; obtain ⟨n, hn⟩ := notBadFunReturnImpSome _ hb; simp [hn])
  case case6 => split_ifs at hnr
  case case18 =>
    rename_i ihRet
    simp only [StackSemEvaluate.evaluate_call]
    repeat' split
    all_goals first | rfl | exact ihRet hnr _ | (simp_all; done) |
      exact Option.isSome_iff_ne_none.mpr ‹¬_ = none›
  case case19 =>
    rename_i ihRet ihHandler
    simp only [StackSemEvaluate.evaluate_call]
    repeat' split
    all_goals first | rfl | exact ihRet hnr.1 _ | exact ihHandler hnr.2 _ | (simp_all; done) |
      exact Option.isSome_iff_ne_none.mpr ‹¬_ = none›

/-- A fetched compiled jump to an installed destination takes one LabSem
step to the destination position. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "compile_jump_correct"
  (words_as_type_indexed_bitvec)]
theorem compileJumpCorrect {width : Nat} [NeZero width] {C F : Type}
    {s : Flapjack.Compiler.Backend.LabSem.State width C F} {pc pc' : Nat}
    {code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))}
    {dest : Nat ⊕ Nat} {regs : Nat → WordLocW width} :
    asmFetchAux pc code = some (compileJumpHOL dest) ∧
      locToPc (Prelude.destToLoc' regs dest) 0 code = some pc' ∧
      (∀ r, dest = .inr r → ∃ p, s.regs r = .loc p 0) ∧
      s.pc = pc ∧ s.code = code ∧ s.regs = regs ∧ s.clock ≠ 0 →
    evaluate s = evaluate (updPc pc' (decClock s)) := by
  rintro ⟨fetch, loc, regsLoc, rfl, rfl, rfl, clk⟩
  rw [evaluate]
  cases dest with
  | inl n =>
    simp only [Prelude.destToLoc'] at loc
    simp [clk, asmFetch, fetch, compileJumpHOL, getPcValue, loc]
  | inr r =>
    obtain ⟨p, hp⟩ := regsLoc r rfl
    simp only [Prelude.destToLoc', hp] at loc
    simp [clk, asmFetch, fetch, compileJumpHOL, hp, loc]

/-- HOL `result_view`: the target-observable shape of a StackSem result. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "result_view"]
inductive ResultView where
  | vloc (n1 n2 : Nat)
  | vcont (n1 n2 : Nat)
  | vtimeout
  | verr
  deriving DecidableEq, Repr

/-- Complete original view of a StackSem result at section `l` with the
continue and break label stacks. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "result_view_def"
  (words_as_type_indexed_bitvec)]
def resultView {width : Nat} [NeZero width] :
    StackSemResult width → Nat → List Nat → List Nat → ResultView
  | .result (.loc n1 n2), _, _, _ => .vloc n1 n2
  | .exception (.loc n1 n2), _, _, _ => .vloc n1 n2
  | .timeOut, _, _, _ => .vtimeout
  | .continue n, l, cs, _ => .vcont l (findLabHOL n cs)
  | .break n, l, _, bs => .vloc l (findLabHOL n bs)
  | _, _, _, _ => .verr

/-- Complete original view of a halting word as a machine result. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "halt_word_view_def"
  (words_as_type_indexed_bitvec)]
def haltWordView {width : Nat} [NeZero width] : WordLocW width → MachineResult
  | .word w => if w = 0 then .halt .success else .halt .resourceLimitHit
  | .loc _ _ => .error

/-- Complete original view of a halting StackSem result. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "halt_view_def"
  (words_as_type_indexed_bitvec)]
def haltView {width : Nat} [NeZero width] : Option (StackSemResult width) → Option MachineResult
  | some (.halt w) => some (haltWordView w)
  | some (.finalFFI outcome) => some (.halt (.ffiOutcome outcome))
  | _ => none

end Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
