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
  fun_induction projectMacros program generalizing result with
  | _ =>
      simp_all only [bind, pure, Option.bind_eq_some_iff,
        Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
        grind only [noMacros]


/-- Every macro-free input is retained literally, with no successful-pass assumption. -/
theorem projectMacros_of_noMacros {width : Nat}
    (program : StackProg (BitVec width)) (free : noMacros program = true) :
    projectMacros program = some program := by
  fun_induction projectMacros program with
  | _ => simp_all [noMacros]


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
