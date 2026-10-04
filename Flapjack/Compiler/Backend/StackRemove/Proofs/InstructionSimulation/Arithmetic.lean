import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation.Atoms

namespace Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.Arithmetic
open Flapjack Compiler.Encoders.Asm

/-- Flapjack factoring of bounded input-list equality. The individual bounds
are derived from the original instruction bound in each constructor case;
there is no separately named HOL theorem claimed for this helper. -/
theorem stateRelGetVars {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (registers : List Nat) (relation : stateRelHOL jump bounds pointer source target)
    (bounded : ∀ register ∈ registers, register < pointer) :
    StackSemStateOps.getVars registers source = StackSemStateOps.getVars registers target := by
  induction registers with
  | nil => rfl
  | cons head tail ih =>
    have headEq := RelationLaws.stateRelGetVar jump bounds pointer head source target
      ⟨relation, bounded head (List.mem_cons_self)⟩
    have tailEq := ih (fun register member => bounded register (List.mem_cons_of_mem head member))
    simp only [StackSemStateOps.getVars, headEq, tailEq]

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine complete original arithmetic constructor case; input failures,
operation guards and ordered destination updates follow native execution. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelInstDiv {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer r1 r2 r3 : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst ((.arith (.div r1 r2 r3)) : HolInst width) pointer ∧
      StackSemInst.instHOL (.arith (.div r1 r2 r3)) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.arith (.div r1 r2 r3)) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  simp only [StackProps.regBoundInst] at bound
  have inputEq := stateRelGetVars jump bounds pointer source target [r3, r2] relation (by
    intro register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h0 | h1
    all_goals subst register; omega)
  simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    Option.join_some] at run ⊢
  rw [← inputEq]
  clear inputEq
  repeat' (split at run)
  all_goals try contradiction
  all_goals simp_all
  all_goals try subst postSource
  all_goals repeat' (first | exact relation |
    (apply StateUpdates.stateRelSetVar; constructor) | omega)

/-- Genuine complete original arithmetic constructor case; input failures,
operation guards and ordered destination updates follow native execution. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelInstAddCarry {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer r1 r2 r3 r4 : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst ((.arith (.addCarry r1 r2 r3 r4)) : HolInst width) pointer ∧
      StackSemInst.instHOL (.arith (.addCarry r1 r2 r3 r4)) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.arith (.addCarry r1 r2 r3 r4)) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  simp only [StackProps.regBoundInst] at bound
  have inputEq := stateRelGetVars jump bounds pointer source target [r2, r3, r4] relation (by
    intro register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h0 | h1 | h2
    all_goals subst register; omega)
  simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    Option.join_some] at run ⊢
  rw [← inputEq]
  clear inputEq
  repeat' (split at run)
  all_goals try contradiction
  all_goals simp_all
  all_goals try subst postSource
  all_goals simp_all only [← Nat.not_le]
  all_goals repeat' (first | exact relation |
    (apply StateUpdates.stateRelSetVar; constructor) | omega)

/-- Genuine complete original arithmetic constructor case; input failures,
operation guards and ordered destination updates follow native execution. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelInstAddOverflow {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer r1 r2 r3 r4 : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst ((.arith (.addOverflow r1 r2 r3 r4)) : HolInst width) pointer ∧
      StackSemInst.instHOL (.arith (.addOverflow r1 r2 r3 r4)) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.arith (.addOverflow r1 r2 r3 r4)) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  simp only [StackProps.regBoundInst] at bound
  have inputEq := stateRelGetVars jump bounds pointer source target [r2, r3] relation (by
    intro register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h0 | h1
    all_goals subst register; omega)
  simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    Option.join_some] at run ⊢
  rw [← inputEq]
  clear inputEq
  repeat' (split at run)
  all_goals try contradiction
  all_goals simp_all
  all_goals try subst postSource
  all_goals repeat' (first | exact relation |
    (apply StateUpdates.stateRelSetVar; constructor) | omega)

/-- Genuine complete original arithmetic constructor case; input failures,
operation guards and ordered destination updates follow native execution. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelInstSubOverflow {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer r1 r2 r3 r4 : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst ((.arith (.subOverflow r1 r2 r3 r4)) : HolInst width) pointer ∧
      StackSemInst.instHOL (.arith (.subOverflow r1 r2 r3 r4)) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.arith (.subOverflow r1 r2 r3 r4)) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  simp only [StackProps.regBoundInst] at bound
  have inputEq := stateRelGetVars jump bounds pointer source target [r2, r3] relation (by
    intro register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h0 | h1
    all_goals subst register; omega)
  simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    Option.join_some] at run ⊢
  rw [← inputEq]
  clear inputEq
  repeat' (split at run)
  all_goals try contradiction
  all_goals simp_all
  all_goals try subst postSource
  all_goals repeat' (first | exact relation |
    (apply StateUpdates.stateRelSetVar; constructor) | omega)

/-- Genuine complete original arithmetic constructor case; input failures,
operation guards and ordered destination updates follow native execution. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelInstLongMul {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer r1 r2 r3 r4 : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst ((.arith (.longMul r1 r2 r3 r4)) : HolInst width) pointer ∧
      StackSemInst.instHOL (.arith (.longMul r1 r2 r3 r4)) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.arith (.longMul r1 r2 r3 r4)) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  simp only [StackProps.regBoundInst] at bound
  have inputEq := stateRelGetVars jump bounds pointer source target [r3, r4] relation (by
    intro register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h0 | h1
    all_goals subst register; omega)
  simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    Option.join_some] at run ⊢
  rw [← inputEq]
  clear inputEq
  repeat' (split at run)
  all_goals try contradiction
  all_goals simp_all
  all_goals try subst postSource
  all_goals repeat' (first | exact relation |
    (apply StateUpdates.stateRelSetVar; constructor) | omega)

/-- Genuine complete original arithmetic constructor case; input failures,
operation guards and ordered destination updates follow native execution. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelInstLongDiv {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer r1 r2 r3 r4 r5 : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst ((.arith (.longDiv r1 r2 r3 r4 r5)) : HolInst width) pointer ∧
      StackSemInst.instHOL (.arith (.longDiv r1 r2 r3 r4 r5)) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.arith (.longDiv r1 r2 r3 r4 r5)) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  simp only [StackProps.regBoundInst] at bound
  have inputEq := stateRelGetVars jump bounds pointer source target [r3, r4, r5] relation (by
    intro register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h0 | h1 | h2
    all_goals subst register; omega)
  simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    Option.join_some] at run ⊢
  rw [← inputEq]
  clear inputEq
  repeat' (split at run)
  all_goals try contradiction
  all_goals simp_all
  all_goals try subst postSource
  all_goals repeat' (first | exact relation |
    (apply StateUpdates.stateRelSetVar; constructor) | omega)

end Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.Arithmetic
