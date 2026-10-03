import Flapjack.Compiler.Backend.WordAlloc.ClashTreeProg
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LiveExpressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ReadsLiveExpressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSets
import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Pancake.WordConvs.ProgramMonotonicity
import Flapjack.Misc.Sptree.ToAList

namespace Flapjack.WordAlloc
open Flapjack Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm
attribute [local instance] Classical.propDecidable

/-- Original unconditional expression occurrence in its literal read list. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_var_exp_get_reads_exp" (words_as_type_indexed_bitvec)]
theorem everyVarExp_getReadsExp {width : Nat} [NeZero width]
    (exp : WordLangExpHOL (BitVec width)) :
    everyVarExpHOL (fun x => decide (x ∈ getReadsExpHOL exp)) exp = true := by
  apply everyVarExpMono _ exp _ ⟨?_, everyVarExp_getLiveExp exp⟩
  intro x hx
  simp only [decide_eq_true_eq] at hx ⊢
  exact Eq.mpr (congrArg (fun predicate => predicate x) (getReadsExpGetLiveExp exp)) hx

/-- Flapjack infrastructure for the original instruction case: the literal
delta's reads/writes cover every source occurrence, including FP width guards. -/
private theorem instruction_inClashTree {width : Nat} [NeZero width]
    (i : WordLangInst (BitVec width)) :
    everyVarInstHOL (fun x => decide (inClashTree
      (getDeltaInst (HolInst.ofWordLangInst i)) x)) i = true := by
  cases i with
  | skip | const _ _ =>
      simp [everyVarInstHOL, getDeltaInst, HolInst.ofWordLangInst, inClashTree]
  | arith a =>
      cases a with
      | binop op r1 r2 ri | shift op r1 r2 ri =>
          cases ri <;> simp [everyVarInstHOL, everyVarImmHOL, getDeltaInst,
            HolInst.ofWordLangInst, HolArith.ofWordLangArith,
            HolRegImm.ofWordRegImm, inClashTree]
      | div _ _ _ | addCarry _ _ _ _ | addOverflow _ _ _ _
      | subOverflow _ _ _ _ | longMul _ _ _ _ | longDiv _ _ _ _ _ =>
          simp [everyVarInstHOL, getDeltaInst, HolInst.ofWordLangInst,
            HolArith.ofWordLangArith, inClashTree]
  | mem op r addr =>
      cases op <;> cases addr <;> simp [everyVarInstHOL, getDeltaInst,
        HolInst.ofWordLangInst, HolAddr.ofWordLangAddr, inClashTree]
  | fp op =>
      cases op <;> simp [everyVarInstHOL, getDeltaInst,
        HolInst.ofWordLangInst, inClashTree]
      all_goals by_cases dim : width = 64 <;> simp_all [inClashTree]

/-- Flapjack lifting from canonical cut-set domain coverage to source key
occurrences, using unconditional Spt enumeration/domain correspondence. -/
private theorem namesCovered (names : WordLangCutsetsHOL) (P : Nat → Bool)
    (covered : ∀ x, sptDomain names.1 x ∨ sptDomain names.2 x → P x = true) :
    everyNameHOL P names = true := by
  simp only [everyNameHOL, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro x member
    exact covered x (Or.inl ((sptMemMapFstToAList names.1 x).mp member))
  · intro x member
    exact covered x (Or.inr ((sptMemMapFstToAList names.2 x).mp member))

/-- Flapjack projection from an actual enumeration entry to its source domain. -/
private theorem pairDomain (tree : Spt Unit) (key : Nat) (value : Unit)
    (member : (key, value) ∈ sptToAList tree) : sptDomain tree key := by
  have lookup := (sptMemToAList tree key value).mp member
  simp [sptDomain, lookup]

local macro "finishClashCoverage" : tactic => `(tactic| (
    all_goals try simp [getClashTree, everyVarHOL, inClashTree,
      Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map,
      List.mem_cons, List.not_mem_nil, sptDomain_sptUnion, domainNumsetListInsert]
    all_goals try simp only [everyVarImmHOL, Bool.or_eq_true, decide_eq_true_eq,
      true_or, or_true, true_and, sptDomainInsert, sptDomain_sptUnion]
    all_goals repeat' constructor
    all_goals first
      | exact instruction_inClashTree _
      | exact everyVarExp_getReadsExp _
      | assumption
      | (refine everyVarExpMono _ _ _ ⟨?_, everyVarExp_getReadsExp _⟩
         intro x hx
         simp only [Bool.or_eq_true, decide_eq_true_eq] at hx ⊢
         aesop
         done)
      | (refine everyVarMono _ _ _ ⟨?_, by assumption⟩
         intro x hx
         simp only [Bool.or_eq_true, decide_eq_true_eq] at hx ⊢
         aesop
         done)
      | (refine namesCovered _ _ ?_
         intro x hx
         simp only [Bool.or_eq_true, decide_eq_true_eq] at hx ⊢
         aesop
         done)
      | aesop (add safe forward [pairDomain])

))

/-- Original complete program occurrence coverage by its clash tree, for
arbitrary loop-target contexts. No support, validity or tree invariant premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_var_in_get_clash_tree" (words_as_type_indexed_bitvec)]
theorem everyVar_inGetClashTree {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) (lt : List (Spt Unit × Spt Unit)) :
    everyVarHOL (fun x => decide (inClashTree (getClashTree prog lt) x)) prog = true := by
  induction prog, lt using getClashTree.induct
  case case29 target args lt values cutsets body lab loc ih =>
    rcases cutsets with ⟨left, right⟩
    finishClashCoverage
  case case30 target args lt values cutsets retBody lab loc value body hLab hLoc ihRet ihHandler =>
    rcases cutsets with ⟨left, right⟩
    finishClashCoverage
  case case23 op name addr lt store =>
    simp only [getClashTree, if_pos store, everyVarHOL, inClashTree,
      Bool.and_eq_true, decide_eq_true_eq]
    simp only [List.not_mem_nil, false_or, List.mem_cons, true_or]
    refine ⟨True.intro, everyVarExpMono _ addr _ ⟨?_, everyVarExp_getReadsExp addr⟩⟩
    intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact Or.inr hx
  case case24 op name addr lt store =>
    simp only [getClashTree, if_neg store, everyVarHOL, inClashTree,
      Bool.and_eq_true, decide_eq_true_eq]
    simp only [List.mem_cons, true_or]
    refine ⟨True.intro, everyVarExpMono _ addr _ ⟨?_, everyVarExp_getReadsExp addr⟩⟩
    intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact Or.inr hx
  finishClashCoverage

end Flapjack.WordAlloc
