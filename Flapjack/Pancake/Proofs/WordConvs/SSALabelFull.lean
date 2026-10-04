import Flapjack.Pancake.Proofs.WordConvs.SSALabelHelpers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.FullSSA

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack factoring of the generalized native induction motive. -/
private def programLabels {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ ssa next tables, extractLabels (ssaCcTrans program ssa next tables).1 =
    extractLabels program

/-- Flapjack projection factoring of the literal reconciliation producer. -/
private theorem fixLabels {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    let out := fixInconsistencies (width := width) prio l r next
    extractLabels out.1 = [] ∧ extractLabels out.2.1 = [] := by
  unfold fixInconsistencies
  generalize hm : mergeMoves ((sptToAList (sptUnion l r)).map Prod.fst) l r next = merged
  rcases merged with ⟨lmov, rmov, count, left, right⟩
  generalize hf : fakeMoves (width := width) prio ((sptToAList (sptUnion l r)).map Prod.fst)
    left right count = result
  rcases result with ⟨a, b, final, leftOut, rightOut⟩
  have facts := fakeMoves_noLabels prio _ left right count a b final leftOut rightOut hf
  simpa [hm, hf, extractLabels] using facts

private theorem fixLabelsLeft {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    extractLabels (fixInconsistencies (width := width) prio l r next).1 = [] :=
  (fixLabels prio l r next).1

private theorem fixLabelsRight {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    extractLabels (fixInconsistencies (width := width) prio l r next).2.1 = [] :=
  (fixLabels prio l r next).2

/-- Flapjack internal instruction projection used by the original fullSSA
label proof; HOL has no separately named theorem for this local step. -/
private theorem instNoLabels {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (ssa : Spt Nat) (next : Nat) :
    extractLabels (ssaCcTransInst instruction ssa next).1 = [] := by
  fun_cases ssaCcTransInst instruction ssa next <;> simp [extractLabels]

/-- Flapjack factoring of the native structural induction inside HOL fullSSA
label preservation; no separately named HOL declaration. -/
private theorem ssaLabels {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) :
    extractLabels program = extractLabels (ssaCcTrans program ssa next tables).1 := by
  have all : ∀ p : WordLangProgHOL (BitVec width), programLabels p := by
    intro p
    apply WordLangProgHOL.rec
      (motive_1 := programLabels)
      (motive_2 := fun ret => match ret with | none => True | some r => programLabels r.2.2.1)
      (motive_3 := fun exc => match exc with | none => True | some r => programLabels r.2.1)
      (motive_4 := fun r => programLabels r.2.2.1)
      (motive_5 := fun r => programLabels r.2.1)
      (motive_6 := fun r => programLabels r.2.1)
      (motive_7 := fun r => programLabels r.1) (t := p)
    all_goals dsimp only [programLabels]
    all_goals intros
    all_goals try simp_all [ssaCcTrans, extractLabels, nextVarRename, listNextVarRenameMove,
      instNoLabels, fixLabelsLeft, fixLabelsRight]
    case «break» =>
      split <;> simp_all [extractLabels]
      split <;> simp_all [extractLabels, ssaReconcile_noLabels]
    case «continue» =>
      split <;> simp_all [extractLabels]
      split <;> simp_all [extractLabels, ssaReconcile_noLabels]
    case shareInst =>
      split <;> rfl
    case loop =>
      rename_i names body exits bodyIH tree counter context
      generalize setupEq : loopSetup (width := width) names exits tree counter = setupOut at *
      rcases setupOut with ⟨setupProg, setupTree, setupNext⟩
      have setupLabels := loopSetup_noLabels (width := width) names exits tree counter
        setupProg setupTree setupNext setupEq
      have bodyLabels := bodyIH (sptInter setupTree names) setupNext
        ((setupTree, names, exits) :: context)
      generalize bodyEq : ssaCcTrans body (sptInter setupTree names) setupNext
        ((setupTree, names, exits) :: context) = bodyOut at *
      rcases bodyOut with ⟨bodyProg, bodyTree, bodyNext⟩
      have backLabels := ssaReconcile_noLabels (width := width) bodyTree setupTree names
      generalize backEq : ssaReconcile (width := width) bodyTree setupTree names = back at *
      cases back <;> simp_all [extractLabels]
    case call =>
      rename_i returns target arguments handler retIH excIH tree counter context
      cases returns with
      | none => simp [ssaCcTrans, extractLabels]
      | some ret =>
        rcases ret with ⟨retNames, cutsets, retBody, l1, l2⟩
        cases handler with
        | none => simp_all [ssaCcTrans, extractLabels, listNextVarRenameMove]
        | some exc =>
          rcases exc with ⟨excName, excBody, e1, e2⟩
          simp_all [ssaCcTrans, extractLabels, listNextVarRenameMove, nextVarRename,
            fixLabelsLeft, fixLabelsRight]
  exact (all program ssa next tables).symm

/-- Original unconditional fullSSA label equality for arbitrary source programs
and counts, including all nested return and exception handlers. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fullSsaCcTrans_labPres {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (count : Nat) :
    extractLabels program = extractLabels (fullSsaCcTrans count program) := by
  generalize produced : setupSSA (outputWidth := width) count (limitVar program) program = result
  rcases result with ⟨move, ssa, next⟩
  have moveLabels : extractLabels move = [] := by
    unfold setupSSA at produced
    generalize listNextVarRename (evenList count) .ln (limitVar program) = renamed at produced
    rcases renamed with ⟨names, tree, counter⟩
    cases produced
    rfl
  have bodyLabels := ssaLabels program ssa next []
  generalize bodyEq : ssaCcTrans program ssa next [] = bodyResult
  rcases bodyResult with ⟨body, finalMap, finalNext⟩
  rw [bodyEq] at bodyLabels
  simpa only [fullSsaCcTrans, produced, bodyEq, extractLabels, moveLabels, List.nil_append]
    using bodyLabels

end Flapjack.WordAlloc
