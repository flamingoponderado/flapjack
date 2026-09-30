import Flapjack.Compiler.Backend.Semantics.StackSem.State

/-! HOL StackSem state primitives. All operations use the accepted owning state
carrier; finite-support maps have canonical lookup/update semantics. No local
state duplicate, evaluator, or executed compiler refinement is introduced. -/

namespace Flapjack.StackSemStateOps

/-- Same-module re-export of the canonical state roundtrip; infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- HOL domain-checked memory update. Equality implements addr =+ value;
    the update preserves the domain and every other state field. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "mem_store_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def memStore {width : Nat} [NeZero width] {C F : Type}
    (addr : BitVec width) (value : WordLocW width) (s : StackSemStateFiniteExact width C F) : Option (StackSemStateFiniteExact width C F) :=
  if s.mdomain addr then some { s with memory := fun key => if key = addr then value else s.memory key } else none

/-- HOL state operation, preserving all fields except the source update. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "mem_load_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def memLoad {width : Nat} [NeZero width] {C F : Type}
    (addr : BitVec width) (s : StackSemStateFiniteExact width C F) : Option (WordLocW width) :=
  if s.mdomain addr then some (s.memory addr) else none

/-- HOL state operation, preserving all fields except the source update. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "dec_clock_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def decClock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with clock := s.clock - 1 }

/-- HOL state operation, preserving all fields except the source update. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_var_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def getVar {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (s : StackSemStateFiniteExact width C F) : Option (WordLocW width) :=
  s.regs.lookup v

/-- HOL state operation, preserving all fields except the source update. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_fp_var_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def getFpVar {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (s : StackSemStateFiniteExact width C F) : Option (BitVec 64) :=
  s.fpRegs.lookup v

/-- HOL state operation, preserving all fields except the source update. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "set_var_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def setVar {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (x : WordLocW width) (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with regs := s.regs.updateEq (v, x) }

/-- HOL state operation, preserving all fields except the source update. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "set_fp_var_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def setFpVar {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (x : BitVec 64) (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with fpRegs := s.fpRegs.updateEq (v, x) }

/-- HOL state operation, preserving all fields except the source update. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "set_store_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def setStore {width : Nat} [NeZero width] {C F : Type}
    (v : WordStoreHOL) (x : WordLocW width) (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with store := s.store.updateEq (v, x) }

/-- HOL state operation, preserving all fields except the source update. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "empty_env_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def emptyEnv {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with regs := HolFiniteMapExact.empty, stack := [] }

/-- HOL register-list lookup: retain order and fail at the first missing key. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_vars_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def getVars {width : Nat} [NeZero width] {C F : Type}
    (vars : List Nat) (s : StackSemStateFiniteExact width C F) : Option (List (WordLocW width)) :=
  match vars with
  | [] => some []
  | v :: vs =>
      match getVar v s with
      | none => none
      | some x =>
          match getVars vs s with
          | none => none
          | some xs => some (x :: xs)

end Flapjack.StackSemStateOps
