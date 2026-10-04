import Flapjack.Pancake.Proofs.WordConvs.SSAFlatInst

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack factoring of the generalized native induction motive. -/
private def programFlat {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ ssa next tables, flatExpConventions program = true →
    flatExpConventions (ssaCcTrans program ssa next tables).1 = true

/-- Flapjack projection factoring of the literal reconciliation producer. -/
private theorem fixFlat {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    let out := fixInconsistencies (width := width) prio l r next
    flatExpConventions out.1 = true ∧ flatExpConventions out.2.1 = true := by
  unfold fixInconsistencies
  generalize hm : mergeMoves ((sptToAList (sptUnion l r)).map Prod.fst) l r next = merged
  rcases merged with ⟨lmov, rmov, count, left, right⟩
  generalize hf : fakeMoves (width := width) prio ((sptToAList (sptUnion l r)).map Prod.fst)
    left right count = result
  rcases result with ⟨a, b, final, leftOut, rightOut⟩
  have facts := fakeMoves_flatExpConventions prio _ left right count a b final leftOut rightOut hf
  simpa [hm, hf, flatExpConventions] using facts

private theorem fixFlatLeft {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    flatExpConventions (fixInconsistencies (width := width) prio l r next).1 = true :=
  (fixFlat prio l r next).1

private theorem fixFlatRight {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    flatExpConventions (fixInconsistencies (width := width) prio l r next).2.1 = true :=
  (fixFlat prio l r next).2

/-- Original complete SSA flat-expression preservation statement. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTrans_flatExpConventions {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source : flatExpConventions program = true) :
    flatExpConventions (ssaCcTrans program ssa next tables).1 = true := by
  have all : ∀ p : WordLangProgHOL (BitVec width), programFlat p := by
    intro p
    apply WordLangProgHOL.rec
      (motive_1 := programFlat)
      (motive_2 := fun ret => match ret with | none => True | some r => programFlat r.2.2.1)
      (motive_3 := fun exc => match exc with | none => True | some r => programFlat r.2.1)
      (motive_4 := fun r => programFlat r.2.2.1)
      (motive_5 := fun r => programFlat r.2.1)
      (motive_6 := fun r => programFlat r.2.1)
      (motive_7 := fun r => programFlat r.1) (t := p)
    all_goals dsimp only [programFlat]
    all_goals intros
    all_goals try simp_all [ssaCcTrans, flatExpConventions, nextVarRename, listNextVarRenameMove]
    case inst =>
      rename_i instruction tree counter context
      simpa only [ssaCcTrans] using ssaCcTrans_flatExpInst instruction tree counter context rfl
    case set =>
      rename_i store value tree counter context premise
      cases value <;> simp_all [flatExpConventions, ssaCcTransExp]
    case ite =>
      exact fixFlat _ _ _ _
    case «break» =>
      split <;> simp_all [flatExpConventions]
      split <;> simp_all [flatExpConventions, ssaReconcile_flatExpConventions]
    case «continue» =>
      split <;> simp_all [flatExpConventions]
      split <;> simp_all [flatExpConventions, ssaReconcile_flatExpConventions]
    case loop =>
      rename_i names body exits tree counter context bodyIH premise
      generalize setupEq : loopSetup (width := width) names exits tree counter = setupOut at *
      rcases setupOut with ⟨setupProg, setupTree, setupNext⟩
      have setupFlat := loopSetup_flatExpConventions (width := width) names exits tree counter
        setupProg setupTree setupNext setupEq
      have bodyFlat := bodyIH (sptInter setupTree names) setupNext
        ((setupTree, names, exits) :: context)
      generalize bodyEq : ssaCcTrans body (sptInter setupTree names) setupNext
        ((setupTree, names, exits) :: context) = bodyOut at *
      rcases bodyOut with ⟨bodyProg, bodyTree, bodyNext⟩
      have backFlat := ssaReconcile_flatExpConventions (width := width) bodyTree setupTree names
      generalize backEq : ssaReconcile (width := width) bodyTree setupTree names = back at *
      cases back <;> simp_all [flatExpConventions]
    case shareInst =>
      rename_i operator name address tree counter context premise
      split
      all_goals
        unfold flatExpConventions at premise
        split at premise <;> simp_all [flatExpConventions, ssaCcTransExp]
    case call =>
      rename_i returns target arguments handler retIH excIH tree counter context premise
      cases returns with
      | none =>
        cases handler with
        | none => simp [ssaCcTrans, flatExpConventions]
        | some exc =>
          rcases exc with ⟨name, body, l1, l2⟩
          simpa [ssaCcTrans, flatExpConventions] using premise
      | some ret =>
        rcases ret with ⟨retNames, cutsets, retBody, l1, l2⟩
        cases handler with
        | none =>
          simp_all [ssaCcTrans, flatExpConventions, listNextVarRenameMove]
        | some exc =>
          rcases exc with ⟨excName, excBody, e1, e2⟩
          simp_all [ssaCcTrans, flatExpConventions, listNextVarRenameMove, nextVarRename,
            fixFlatLeft, fixFlatRight]
  exact all program ssa next tables source

end Flapjack.WordAlloc
