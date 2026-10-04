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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordExpWithClock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F)
    (y : WordLangExpHOL (BitVec width)) (k : Nat) :
    wordExp { s with clock := k } y = wordExp s y := by
  refine WordLangExpHOL.rec
    (motive_1 := fun e : WordLangExpHOL (BitVec width) =>
      wordExp { s with clock := k } e = wordExp s e)
    (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) =>
      ∀ e ∈ es, wordExp { s with clock := k } e = wordExp s e)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y
  · intro value; simp only [wordExp]
  · intro register; simp only [wordExp]
  · intro name; simp only [wordExp]
  · intro address ih
    simp only [wordExp, ih, memLoad]
  · intro operator arguments ih
    simp only [wordExp]
    have hmap : arguments.attach.map (fun e => wordExp { s with clock := k } e.val) =
        arguments.attach.map (fun e => wordExp s e.val) := by
      apply List.map_congr_left
      intro e _
      exact ih e.val e.property
    rw [hmap]
  · intro operator left right ihLeft ihRight
    simp only [wordExp, ihLeft, ihRight]
  · intro e h; cases h
  · intro head tail ihHead ihTail e he
    rcases List.mem_cons.mp he with rfl | ht
    · exact ihHead
    · exact ihTail e ht

/-- Full original OPTION_MAP equation for assignment, preserving both success
and failure and updating only the original destination register. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem assignWithClock {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : WordLangExpHOL (BitVec width))
    (s : StackSemStateFiniteExact width C F) (k : Nat) :
    assign x y { s with clock := k } =
      (assign x y s).map (fun s => { s with clock := k }) := by
  simp only [assign, wordExpWithClock]
  cases wordExp s y <;> simp [setVar]

end Flapjack.StackPropsExpressionClock
