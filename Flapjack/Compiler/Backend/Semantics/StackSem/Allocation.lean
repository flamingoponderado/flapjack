import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec

namespace Flapjack.StackSemAllocation

/-- Canonical state carrier roundtrip re-export; Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Exact stackSem garbage-collection transition. Preserve the unused prefix,
encode only the active stack, pass the original four GC arguments, decode
against the old active stack and update exactly stack/store/regs/memory.
This proof-side port is a prerequisite of the faithful evaluator; production
routing/refinement is still required on the parent evaluator bead. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "gc_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def gc {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : Option (StackSemStateFiniteExact width C F) :=
  if s.stack.length < s.stackSpace then none else
  let unused := s.stack.take s.stackSpace
  let stack := s.stack.drop s.stackSpace
  match StackSem.encStack s.bitmaps stack with
  | none => none
  | some roots =>
      match s.gcFun (roots,s.memory,s.mdomain,s.store) with
      | none => none
      | some (roots',memory,store) =>
          match StackSem.decStack s.bitmaps roots' stack with
          | none => none
          | some stack' =>
              some { s with stack := unused ++ stack', store := store, regs := HolFiniteMapExact.empty, memory := memory }

/-- Exact unsigned modular-space test; missing entries and location-valued
operands return NONE. HOL independently quantifies the request and store word
dimensions; allocation instantiates both at its state width. The store
argument is the canonical finite map. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "has_space_def"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
def hasSpace {requestWidth : Nat} {storeWidth : Nat} [NeZero requestWidth] [NeZero storeWidth]
    (wl : WordLocW requestWidth) (store : HolFiniteMapExact WordStoreHOL (WordLocW storeWidth)) : Option Bool :=
  match wl,store.lookup .nextFree,store.lookup .triggerGC with
  | .word w,some (.word n),some (.word l) => some (decide (w.toNat ≤ (l-n).toNat))
  | _,_,_ => none

/-- Exact allocation result: GC failure returns the original input state;
post-GC lookup/space errors retain that GC state; insufficient space emits
Halt (Word 1) after empty_env. No extra success assumption is introduced. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "alloc_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def alloc {width : Nat} [NeZero width] {C F : Type}
    (w : BitVec width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match gc (StackSemStateOps.setStore .allocSize (.word w) s) with
  | none => (some .error,s)
  | some collected =>
      match collected.store.lookup .allocSize with
      | none => (some .error,collected)
      | some amount =>
          match hasSpace amount collected.store with
          | none => (some .error,collected)
          | some true => (none,collected)
          | some false => (some (.halt (.word 1)),StackSemStateOps.emptyEnv collected)

end Flapjack.StackSemAllocation
