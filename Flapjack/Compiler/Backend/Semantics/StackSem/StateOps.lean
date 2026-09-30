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

/-- HOL register/immediate lookup. Register lookup preserves Word and Loc
payloads; an immediate always becomes a Word without inspecting the state. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_var_imm_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def getVarImm {width : Nat} [NeZero width] {C F : Type}
    (value : WordRegImm (BitVec width))
    (s : StackSemStateFiniteExact width C F) : Option (WordLocW width) :=
  match value with
  | .reg name => getVar name s
  | .imm word => some (.word word)

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

/-! HOL `bytes_in_word` (`hol/src/n-bit/byteScript.sml:193`, external HOL
library outside the CakeML sources) has no `@[hol]` tag: the cakeml-only
reference checker cannot cite it. It is the word-sized byte count. -/
def bytesInWord (width : Nat) [NeZero width] : BitVec width :=
  BitVec.ofNat width (width / 8)

/-- HOL StackSem `copy_words_for_pattern_def` (`stackSemScript.sml:684-700`):
    copy the set bits of `pattern` into memory as `Word` payloads, advancing
    the destination by `bytes_in_word` per copied bit, until the pattern is
    exhausted (`1w`) or a guard fails (`0w`, out of domain, past the bitmap). -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "copy_words_for_pattern_def"
  (words_as_type_indexed_bitvec)]
def copyWordsForPatternExact {width : Nat} [NeZero width]
    (pattern : BitVec width) (i : Nat) (a off : BitVec width)
    (bs : List (BitVec width)) (dm : BitVec width → Bool)
    (m : BitVec width → WordLocW width) :
    Option (Nat × BitVec width × (BitVec width → WordLocW width)) :=
  if pattern = 0 then none
  else if pattern = 1 then some (i, a, m)
  else if dm a = true ∧ i < bs.length then
    let b := pattern.getLsbD 0
    let w := bs[i]!
    let m' := fun key => if key = a then WordLocW.word (if b then w + off else w) else m key
    copyWordsForPatternExact (pattern >>> 1) (i + 1) (a + bytesInWord width) off bs dm m'
  else none
termination_by bs.length - i
decreasing_by
  simp_wf
  omega

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
/-- HOL `copy_words_for_pattern_LESS_EQ` (stackSemScript.sml, immediately after
`copy_words_for_pattern_def`): the copy cursor never decreases.  Untagged
Flapjack infrastructure: the HOL original is a proof-side bound for the same
external-library helper and has no separate cakeml declaration to cite. -/
theorem copyWordsForPatternExact_least {width : Nat} [NeZero width] (off : BitVec width)
    (bs : List (BitVec width)) (dm : BitVec width → Bool) :
    ∀ (pattern : BitVec width) (i : Nat) (a : BitVec width) (m : BitVec width → WordLocW width)
      {j : Nat} {a' : BitVec width} {m' : BitVec width → WordLocW width},
      copyWordsForPatternExact pattern i a off bs dm m = some (j, a', m') → i ≤ j := by
  apply copyWordsForPatternExact.induct off bs dm
  case case1 =>
    intro i a m j a' m' h
    rw [copyWordsForPatternExact.eq_def] at h
    simp only [if_pos rfl] at h
    cases h
  case case2 =>
    intro i a m _ j a' m' h
    rw [copyWordsForPatternExact.eq_def] at h
    by_cases h10 : (1 : BitVec width) = 0
    · rw [if_pos h10] at h; cases h
    · rw [if_neg h10, if_pos rfl] at h
      injection h with hpair
      injection hpair with hji _
      omega
  case case3 =>
    intro pattern i a m h0 h1 hcond b w mNew ihR j a' m' h
    rw [copyWordsForPatternExact.eq_def] at h
    rw [if_neg h0, if_neg h1, if_pos hcond] at h
    exact Nat.le_trans (Nat.le_succ i) (ihR h)
  case case4 =>
    intro pattern i a m h0 h1 hnc j a' m' h
    rw [copyWordsForPatternExact.eq_def] at h
    rw [if_neg h0, if_neg h1, if_neg hnc] at h
    cases h

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "copy_words_def"
  (words_as_type_indexed_bitvec)]
def copyWordsExact {width : Nat} [NeZero width] (i : Nat) (a off : BitVec width)
    (bs : List (BitVec width)) (dm : BitVec width → Bool) (m : BitVec width → WordLocW width) :
    Option (BitVec width × (BitVec width → WordLocW width)) :=
  if _h : bs.length ≤ i then none
  else
    let pattern := bs[i]!
    match _hcp : copyWordsForPatternExact pattern (i + 1) a off bs dm m with
    | none => none
    | some (i1, a1, m1) =>
        if pattern.msb then copyWordsExact i1 a1 off bs dm m1 else some (a1, m1)
termination_by bs.length - i
decreasing_by
  simp_wf
  have hle : i + 1 ≤ i1 := copyWordsForPatternExact_least off bs dm pattern (i + 1) a m _hcp
  omega

end Flapjack.StackSemStateOps
