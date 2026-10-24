import Flapjack.Pancake.WordLang.MaxVarExp
import Flapjack.Compiler.Backend.Semantics.StackSem.Expressions
import Flapjack.Compiler.Backend.StackProps.StateConstants

/-! Full original memory/expression/assignment clock-commutation statements.
The misleading source name mem_load_with_const is retained in its HOL tag:
its actual equation concerns mem_store. These are primitive-expression proofs,
independent of the full evaluator and of native instruction acceptance. -/
namespace Flapjack.StackPropsExpressionClock
open StackSemExpressions StackSemStateOps

/-- Same-module codec for the actual imported state owner; infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Full original mem_load_with_const: this is memory-store commutation,
including failure when the address is outside the original domain. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "mem_load_with_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memStoreWithClock {width : Nat} [NeZero width] {C F : Type}
    (x : BitVec width) (y : WordLocW width)
    (z : StackSemStateFiniteExact width C F) (k : Nat) :
    memStore x y { z with clock := k } =
      (memStore x y z).map (fun s => { s with clock := k }) := by
  unfold memStore
  split <;> simp_all

/-- Full original recursive expression clock invariance. Every Op argument
is covered by the nested expression/list recursor, without any premise about
successful evaluation or the argument list. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "word_exp_with_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpWithClock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F)
    (y : WordLangExpHOL (BitVec width)) (k : Nat) :
    wordExp { s with clock := k } y = wordExp s y := by
  set_option tactic.fun_induction.unfolding false in
    fun_induction maxVarExpHOL y with
    | case3 operator arguments ih =>
        simp only [wordExp]
        have hmap := List.map_congr_left (l := arguments.attach)
          (fun e _ => ih e.val e.property)
        rw [hmap]
    | case5 expression _ _ _ _ => cases expression <;> grind only [wordExp, memLoad]
    | _ => simp_all only [wordExp, memLoad]

/-- Full original OPTION_MAP equation for assignment, preserving both success
and failure and updating only the original destination register. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "assign_with_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignWithClock {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : WordLangExpHOL (BitVec width))
    (s : StackSemStateFiniteExact width C F) (k : Nat) :
    assign x y { s with clock := k } =
      (assign x y s).map (fun s => { s with clock := k }) := by
  simp only [assign, wordExpWithClock]
  cases wordExp s y <;> simp [setVar]

end Flapjack.StackPropsExpressionClock
