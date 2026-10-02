import Flapjack.Compiler.Backend.StackLang.MacroLeaves
import Flapjack.Compiler.Backend.StackLang.ProductionCodec

/-!
Complete recursive assembly of the emission-reviewed production macro leaves.
Flapjack-specific infrastructure: production macros have no HOL constructors.
Only the three macro constructors are replaced; literal shared constructors,
word payloads, names, labels, counts and offsets retain their exact positions.
A Nat macro constant outside the width is rejected, including in any nested
body. This does not establish whole-program labFlatten equivalence: its
peepholes and section conventions remain separate production-route obligations.
-/
namespace Flapjack.Compiler.Backend.StackLang.ProductionMacros
open Flapjack

def projectMacros {width : Nat} : StackProg (BitVec width) → Option (StackProg (BitVec width))
  | .skip => some (.skip)
  | .const destination value =>
      if value < 2 ^ width then some (.inst (.const destination (BitVec.ofNat width value)))
      else none
  | .arith operator destination left right =>
      some (.inst (.arith (.binOp operator destination left (.reg right))))
  | .shift operator destination left right =>
      some (.inst (.arith (.shift operator destination left (.reg right))))
  | .inst instruction => some (.inst instruction)
  | .shMem operator source address => some (.shMem operator source address)
  | .shMemOffset operator source address offset => some (.shMemOffset operator source address offset)
  | .get destination store => some (.get destination store)
  | .set store source => some (.set store source)
  | .opCurrHeap operator destination source =>
      some (.opCurrHeap operator destination source)
  | .call none target none => some (.call none target none)
  | .call none target (some (program, exceptionLabel, handlerLabel)) => do
      let body ← projectMacros program
      pure (.call none target (some (body, exceptionLabel, handlerLabel)))
  | .call (some (program, link, returnLabel, entryLabel)) target none => do
      let body ← projectMacros program
      pure (.call (some (body, link, returnLabel, entryLabel)) target none)
  | .call (some (program, link, returnLabel, entryLabel)) target
      (some (handlerProgram, exceptionLabel, handlerLabel)) => do
      let body ← projectMacros program
      let handler ← projectMacros handlerProgram
      pure (.call (some (body, link, returnLabel, entryLabel)) target
        (some (handler, exceptionLabel, handlerLabel)))
  | .seq first second => do
      let first ← projectMacros first
      let second ← projectMacros second
      pure (.seq first second)
  | .ite operator condition right thenBranch elseBranch => do
      let first ← projectMacros thenBranch
      let second ← projectMacros elseBranch
      pure (.ite operator condition right first second)
  | .loop body => (projectMacros body).map .loop
  | .jumpLower register target label => some (.jumpLower register target label)
  | .alloc words => some (.alloc words)
  | .storeConsts source bitmap stub => some (.storeConsts source bitmap stub)
  | .codeBufferWrite address value => some (.codeBufferWrite address value)
  | .dataBufferWrite address value => some (.dataBufferWrite address value)
  | .raise exception => some (.raise exception)
  | .return value => some (.return value)
  | .break label => some (.break label)
  | .continue label => some (.continue label)
  | .ffi function configuration configurationLength array arrayLength returnAddress =>
      some (.ffi function configuration configurationLength array arrayLength
        returnAddress)
  | .tick => some (.tick)
  | .locValue destination label entry => some (.locValue destination label entry)
  | .install codeBuffer codeLength dataBuffer dataLength returnAddress =>
      some (.install codeBuffer codeLength dataBuffer dataLength
        returnAddress)
  | .rawCall target => some (.rawCall target)
  | .stackAlloc words => some (.stackAlloc words)
  | .stackFree words => some (.stackFree words)
  | .stackStore register offset => some (.stackStore register offset)
  | .stackStoreAny register offsetRegister => some (.stackStoreAny register offsetRegister)
  | .stackLoad register offset => some (.stackLoad register offset)
  | .stackLoadAny register offsetRegister => some (.stackLoadAny register offsetRegister)
  | .stackGetSize register => some (.stackGetSize register)
  | .stackSetSize register => some (.stackSetSize register)
  | .bitmapLoad destination address => some (.bitmapLoad destination address)
  | .halt register => some (.halt register)
termination_by program => stackMapDepth program
decreasing_by
  all_goals simp [stackMapDepth] <;> omega

/-- Checks only the three production macro constructors; not validity of the
native codec or of the eventual Stack-to-Lab input language. -/
def noMacros (program : StackProg α) : Bool :=
  match program with
  | .const _ _ | .arith _ _ _ _ | .shift _ _ _ _ => false
  | .seq p q | .ite _ _ _ p q => noMacros p && noMacros q
  | .loop p => noMacros p
  | .call ret _ handler =>
    (match ret with | none => true | some (p, _, _, _) => noMacros p) &&
    (match handler with | none => true | some (q, _, _) => noMacros q)
  | _ => true
termination_by sizeOf program
decreasing_by all_goals decreasing_trivial

/-- All successful outputs are macro-free, including both nested call bodies. -/
theorem projectMacros_noMacros {width : Nat}
    (program result : StackProg (BitVec width))
    (accepted : projectMacros program = some result) : noMacros result = true := by
  cases program with
  | const destination value =>
    simp only [projectMacros] at accepted
    split at accepted
    · cases accepted
      simp only [noMacros]
    · contradiction
  | seq p q =>
    simp [projectMacros, Option.bind_eq_some_iff] at accepted
    rcases accepted with ⟨p', hp, q', hq, rfl⟩
    simp only [noMacros, projectMacros_noMacros p p' hp, projectMacros_noMacros q q' hq,
      Bool.and_self]
  | ite op r right p q =>
    simp [projectMacros, Option.bind_eq_some_iff] at accepted
    rcases accepted with ⟨p', hp, q', hq, rfl⟩
    simp only [noMacros, projectMacros_noMacros p p' hp, projectMacros_noMacros q q' hq,
      Bool.and_self]
  | loop p =>
    simp only [projectMacros, Option.map_eq_some_iff] at accepted
    rcases accepted with ⟨p', hp, rfl⟩
    simp only [noMacros, projectMacros_noMacros p p' hp]
  | call ret target handler =>
    rcases hr : ret with _ | ⟨p, link, l1, l2⟩ <;>
      rcases hh : handler with _ | ⟨q, l3, l4⟩
    · simp only [projectMacros, hr, hh, Option.some.injEq] at accepted
      subst result
      simp only [noMacros, Bool.and_self]
    · simp [projectMacros, hr, hh, Option.bind_eq_some_iff] at accepted
      rcases accepted with ⟨q', hq, rfl⟩
      simp only [noMacros, projectMacros_noMacros q q' hq, Bool.and_self]
    · simp [projectMacros, hr, hh, Option.bind_eq_some_iff] at accepted
      rcases accepted with ⟨p', hp, rfl⟩
      simp only [noMacros, projectMacros_noMacros p p' hp, Bool.and_self]
    · simp [projectMacros, hr, hh, Option.bind_eq_some_iff] at accepted
      rcases accepted with ⟨p', hp, q', hq, rfl⟩
      simp only [noMacros, projectMacros_noMacros p p' hp, projectMacros_noMacros q q' hq,
        Bool.and_self]
  | _ =>
    simp only [projectMacros, Option.some.injEq] at accepted
    subst result
    simp only [noMacros]
termination_by sizeOf program
decreasing_by all_goals simp_all only [Option.some.injEq]; subst_vars; decreasing_trivial

/-- Every macro-free input is retained literally, with no successful-pass assumption. -/
theorem projectMacros_of_noMacros {width : Nat}
    (program : StackProg (BitVec width)) (free : noMacros program = true) :
    projectMacros program = some program := by
  cases program with
  | const _ _ | arith _ _ _ _ | shift _ _ _ _ => simp [noMacros] at free
  | seq p q =>
    simp only [noMacros, Bool.and_eq_true] at free
    simp only [projectMacros, projectMacros_of_noMacros p free.1,
      projectMacros_of_noMacros q free.2, bind, Option.bind_some, pure]
  | ite op r right p q =>
    simp only [noMacros, Bool.and_eq_true] at free
    simp only [projectMacros, projectMacros_of_noMacros p free.1,
      projectMacros_of_noMacros q free.2, bind, Option.bind_some, pure]
  | loop p =>
    simp only [noMacros] at free
    simp only [projectMacros, projectMacros_of_noMacros p free, Option.map_some]
  | call ret target handler =>
    rcases hr : ret with _ | ⟨p, link, l1, l2⟩ <;>
      rcases hh : handler with _ | ⟨q, l3, l4⟩
    · simp only [projectMacros]
    · simp only [noMacros, hr, hh, Bool.true_and] at free
      simp only [projectMacros, projectMacros_of_noMacros q free, bind, Option.bind_some, pure]
    · simp only [noMacros, hr, hh, Bool.and_true] at free
      simp only [projectMacros, projectMacros_of_noMacros p free, bind, Option.bind_some, pure]
    · simp only [noMacros, hr, hh, Bool.and_eq_true] at free
      simp only [projectMacros, projectMacros_of_noMacros p free.1,
        projectMacros_of_noMacros q free.2, bind, Option.bind_some, pure]
  | _ => simp only [projectMacros]
termination_by sizeOf program
decreasing_by all_goals simp_all only [Option.some.injEq]; subst_vars; decreasing_trivial

/-- Complete idempotence with failure retained, not only an accepted-image equation. -/
theorem projectMacros_idempotent {width : Nat} (program : StackProg (BitVec width)) :
    (projectMacros program).bind projectMacros = projectMacros program := by
  cases hp : projectMacros program with
  | none => rfl
  | some result =>
    simp only [Option.bind_some]
    exact projectMacros_of_noMacros result (projectMacros_noMacros program result hp)

-- The exact existing emission-reviewed leaves are reused, not re-proved or retagged.
theorem const_leaf {width : Nat} (destination value : Nat) :
    projectMacros (width := width) (.const destination value) =
      MacroLeaves.project width (.const destination value) := by
  simp only [projectMacros, MacroLeaves.project]

theorem arith_leaf {width : Nat} (op : BinOp) (d l r : Nat) :
    projectMacros (width := width) (.arith op d l r) =
      MacroLeaves.project width (.arith op d l r) := by
  simp only [projectMacros, MacroLeaves.project]

theorem shift_leaf {width : Nat} (op : Shift) (d l r : Nat) :
    projectMacros (width := width) (.shift op d l r) =
      MacroLeaves.project width (.shift op d l r) := by
  simp only [projectMacros, MacroLeaves.project]

end Flapjack.Compiler.Backend.StackLang.ProductionMacros
