import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryReads
import Flapjack.Compiler.Backend.StackRemove.Proofs.RelationLaws
import Flapjack.Compiler.Backend.Semantics.StackSem.Expressions

/-! Full six-constructor StackRemove expression simulation. The operand-list
induction covers every Op argument; no successful target expression is supplied
as a premise, and the native domain-checked load is used unchanged. -/
namespace Flapjack.Compiler.Backend.StackRemove.ExpressionSimulation
open Flapjack

/-- Flapjack-specific canonical state codec witness; no standalone HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original expression theorem, with only source success, full
register bound and the actual full native state relation as hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelWordExp {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (expression : WordLangExpHOL (BitVec width)) (value : BitVec width)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundExp expression pointer ∧ StackSemExpressions.wordExp source expression = some value) :
    StackSemExpressions.wordExp target expression = some value := by
  rcases hypothesis with ⟨relation, bound, sourceRun⟩
  have simulate : ∀ e w, StackProps.regBoundExp e pointer →
      StackSemExpressions.wordExp source e = some w → StackSemExpressions.wordExp target e = some w := by
    intro e
    induction e using WordLangExpHOL.rec
      (motive_2 := fun args => ∀ e ∈ args, ∀ w, StackProps.regBoundExp e pointer →
        StackSemExpressions.wordExp source e = some w → StackSemExpressions.wordExp target e = some w) with
    | const word =>
      intro w _bound run
      simpa only [StackSemExpressions.wordExp] using run
    | var register =>
      intro w registerBound run
      simp only [StackProps.regBoundExp] at registerBound
      have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
        ⟨relation, registerBound⟩
      change source.regs.lookup register = target.regs.lookup register at lookupEq
      simpa only [StackSemExpressions.wordExp, ← lookupEq] using run
    | lookup name =>
      intro _w impossible _run
      simp only [StackProps.regBoundExp] at impossible
    | load address ih =>
      intro w addressBound run
      simp only [StackProps.regBoundExp] at addressBound
      cases addressRun : StackSemExpressions.wordExp source address with
      | none => simp [StackSemExpressions.wordExp, addressRun] at run
      | some word =>
        have targetAddress := ih word addressBound addressRun
        cases sourceRead : StackSemStateOps.memLoad word source with
        | none => simp [StackSemExpressions.wordExp, addressRun, sourceRead] at run
        | some payload =>
          cases payload with
          | loc block offset => simp [StackSemExpressions.wordExp, addressRun, sourceRead] at run
          | word payload =>
            have targetRead := MemoryReads.stateRelMemLoadImp jump bounds pointer source target word
              (.word payload) ⟨relation, sourceRead⟩
            simpa only [StackSemExpressions.wordExp, targetAddress, targetRead] using
              (show some payload = some w from
                by simpa only [StackSemExpressions.wordExp, addressRun, sourceRead] using run)
    | op operator args ihArgs =>
      intro w argsBound run
      simp only [StackProps.regBoundExp] at argsBound
      simp only [StackSemExpressions.wordExp] at run ⊢
      cases allSource : (args.attach.map (fun e => StackSemExpressions.wordExp source e.val)).all Option.isSome with
      | false =>
        rw [allSource] at run
        cases run
      | true =>
        have listsEqual : args.attach.map (fun e => StackSemExpressions.wordExp target e.val) =
            args.attach.map (fun e => StackSemExpressions.wordExp source e.val) := by
          apply List.map_congr_left
          intro arg _member
          have sourceSome : (StackSemExpressions.wordExp source arg.val).isSome = true :=
            (List.all_eq_true.mp allSource) _
              (List.mem_map.mpr ⟨arg, List.mem_attach args arg, rfl⟩)
          rcases Option.isSome_iff_exists.mp sourceSome with ⟨word, argRun⟩
          exact (ihArgs arg.val arg.property word (argsBound arg.val arg.property) argRun).trans argRun.symm
        rw [listsEqual]
        exact run
    | shift operator left right ihLeft ihRight =>
      intro w bothBounds run
      simp only [StackProps.regBoundExp] at bothBounds
      cases leftRun : StackSemExpressions.wordExp source left with
      | none => simp [StackSemExpressions.wordExp, leftRun] at run
      | some leftWord =>
        have targetLeft := ihLeft leftWord bothBounds.1 leftRun
        cases rightRun : StackSemExpressions.wordExp source right with
        | none => simp [StackSemExpressions.wordExp, leftRun, rightRun] at run
        | some rightWord =>
          have targetRight := ihRight rightWord bothBounds.2 rightRun
          simpa only [StackSemExpressions.wordExp, targetLeft, targetRight] using
            (show wordShiftHOL operator leftWord rightWord.toNat = some w from
              by simpa only [StackSemExpressions.wordExp, leftRun, rightRun] using run)
    | nil e member _w _expressionBound _expressionRun => cases member
    | cons head tail ihHead ihTail e member w expressionBound expressionRun =>
      rcases List.mem_cons.mp member with same | member
      · subst e
        exact ihHead w expressionBound expressionRun
      · exact ihTail e member w expressionBound expressionRun
  exact simulate expression value bound sourceRun

end Flapjack.Compiler.Backend.StackRemove.ExpressionSimulation
