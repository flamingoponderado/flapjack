module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.Relations
public import Flapjack.Compiler.Backend.WordBignum.Proofs.MiniStateOps
public import Flapjack.Misc.WordList
public import Flapjack.Misc.Sptree
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

@[expose] public section

/-! The bignum generator's memory and state relations against `wordSem`, ported
from `cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. -/
namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack
open Flapjack.Misc
open Flapjack.Misc.Multiword
open Flapjack.SetSep

namespace MiniStateSupport

/-- Same-module canonical finite-support witness for the `regs` field named by
the relations in this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) :=
  Flapjack.Compiler.Backend.WordBignum.holFmapAsFiniteSupportWitness

/-- Same-module canonical roundtrip witness for the mini-language state
carrier, required by the multi-carrier relation qualifier on `stateRel`. -/
theorem holFmapAsFiniteSupportRelationWitness_MiniState {width : Nat} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) :=
  Flapjack.Compiler.Backend.WordBignum.holFmapAsFiniteSupportWitness

end MiniStateSupport

namespace WordSemSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store` fields
named by the tagged `divCodeAssum` in this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Same-module canonical roundtrip witness for the `wordSem` state carrier,
required by the multi-carrier relation qualifier on `stateRel`. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact {width : Nat}
    [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemSupport

/-- The compiled-code relation: every installed mini-program has a compiled
word program in `code`, and the accumulator only grows. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "code_rel_def"
  (words_as_type_indexed_bitvec)]
def codeRel {α : Type} {width : Nat} [NeZero width]
    (cs : α × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ (prog : Mini (BitVec width)) (n : Nat) (p2 : WordLangProgHOL (BitVec width)),
    holAlookup cs.2 prog = some (n, p2) →
      ∃ (cs1 : Nat × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
        (l2 i2 : Nat)
        (cs2 : Nat × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width))),
        compile n 2 1 cs1 prog = (p2, l2, i2, cs2) ∧
          sptLookup n code = some (1, .seq p2 (.return 0 [0])) ∧
          codeSubset cs2 cs

/-- The division-code assumption: for any well-formed division call the compiled
`DivCode` body returns the quotient and remainder.  HOL writes this as a
Boolean proposition whose body universally quantifies the state and argument
variables (`div_code_assum code <=> !(t1:state) n l ... . ...`); the Lean
definition keeps that shape, with the universals inside the `Prop` body.
The post-state is bound by a `let` because Lean's parser does not accept a
multi-field record update as a deeply nested argument. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "div_code_assum_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def divCodeAssum {width : Nat} [NeZero width] {C F : Type}
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ (t1 : WordSemStateFiniteExact width C F) (n l i0 i1 i2 i3 i4 : Nat)
      (w3 w4 w5 : BitVec width) (retVal : WordLocW width),
    0 < i0 ∧ 0 < i1 ∧ 0 < i2 ∧ 0 < i3 ∧ 0 < i4 ∧
      [i0, i1, i2, i3, i4].Nodup ∧
      t1.code = code ∧ t1.termdep ≠ 0 ∧ WordSemStateFiniteExact.getVar 0 t1 = some retVal ∧
      singleDivPre w3 w4 w5 →
      ∃ max : Option Nat,
        let t3 : WordSemStateFiniteExact width C F :=
          { t1 with permute := (fun n => t1.permute (n + 1)), locals := .ln, stackMax := max }
        WordSemStateFiniteExact.evaluate (divCode n l i0 i1 i2 i3 i4)
            ({ t1 with locals := (sptInsert i2 (.word w3)
                (sptInsert i3 (.word w4) (sptInsert i4 (.word w5) t1.locals))) }) =
          (none,
            let (w1, w2) := singleDiv w3 w4 w5
            WordSemStateFiniteExact.setVar 0 retVal
              (WordSemStateFiniteExact.setVar i1 (.word w2)
                (WordSemStateFiniteExact.setVar i0 (.word w1)
                  (WordSemStateFiniteExact.setStore (.temp (BitVec.ofNat 5 28)) (.word w2)
                    t3))))

/-- The three array contents are represented by heap lists at the temporary
registers, sharing the out-array list. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "array_rel_def"
  (words_as_type_indexed_bitvec)]
def arrayRel {payload : Nat} {address : Nat} [NeZero payload] [NeZero address]
    (arr : Address → List (BitVec payload))
    (v1 v2 v3 : Option (WordLocW address))
    (m : BitVec address → WordLocW payload) (dm : BitVec address → Bool)
    (frame : ((BitVec address × WordLocW payload) → Prop) → Prop) : Prop :=
  ∃ (a1 a2 a3 : BitVec address)
      (rest1 rest2 : ((BitVec address × WordLocW payload) → Prop) → Prop),
    v1 = some (.word a1) ∧ v2 = some (.word a2) ∧ v3 = some (.word a3) ∧
      star (star (wordList a1 ((arr .in1).map .word)) (wordList a3 ((arr .out).map .word)))
          rest1 (fun2Set (m, fun a => dm a = true)) ∧
        star (star (wordList a2 ((arr .in2).map .word))
            (wordList a3 ((arr .out).map .word)))
          rest2 (fun2Set (m, fun a => dm a = true)) ∧
          star (wordList a3 ((arr .out).map .word)) frame
            (fun2Set (m, fun a => dm a = true))

/-- The source's state relation between a mini-language state and a `wordSem`
state: matching clocks, the array representation, the register file in the
temporary registers, the code and division assumptions, and the untouched
`wordSem` fields of the original state.  HOL's `div_code_assum (:'ffi) (:'c)
t.code` conjunct is kept directly, as `divCodeAssum t.code`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [MiniState.regs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
def stateRel {width : Nat} [NeZero width] {β : Type} {C F : Type}
    (s : MiniState width) (t : WordSemStateFiniteExact width C F)
    (cs : β × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
    (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) : Prop :=
  s.clock = t.clock ∧
    arrayRel s.arrays (t.store.lookup tempIn1) (t.store.lookup tempIn2)
      (t.store.lookup tempOut) t.memory t.mdomain frame ∧
    (∀ (a : Nat) (v : BitVec width), s.regs.lookup a = some v →
      a < 25 ∧ t.store.lookup (.temp (BitVec.ofNat 5 a)) = some (.word v)) ∧
    codeRel cs t.code ∧
    divCodeAssum (C := C) (F := F) t.code ∧
    t.termdep ≠ 0 ∧
    t0.gcFun = t.gcFun ∧ t0.handler = t.handler ∧ t0.termdep = t.termdep ∧
    t0.code = t.code ∧ t0.be = t.be ∧ t0.ffi = t.ffi ∧
    t0.compile = t.compile ∧ t0.compileOracle = t.compileOracle ∧
    t0.codeBuffer = t.codeBuffer ∧ t0.dataBuffer = t.dataBuffer ∧
    t0.stackLimit = t.stackLimit ∧ t0.stackSize = t.stackSize ∧
    t.store.lookup tempOut = t0.store.lookup tempOut ∧
    (∀ n, (∀ r, n ≠ .temp r) → t.store.lookup n = t0.store.lookup n)

/-- Flapjack-only inhabitant for the `wordSem` location carrier, so the reviewed
`holFapply` rendering of HOL `FAPPLY` can be used without putting the instance
into any tagged signature. -/
instance wordLocWNonempty {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Flapjack-only helper for the `state_rel_delete_vars` port: a lookup that
survives domain subtraction at another key was already defined. -/
theorem HolFiniteMapExact.eraseEq_lookup_some {α β : Type} [DecidableEq α]
    (map : HolFiniteMapExact α β) (key other : α) {value : β}
    (h : (map.eraseEq key).lookup other = some value) : map.lookup other = some value := by
  by_cases hk : other = key
  · subst hk
    simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL] at h
  · simpa [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hk] using h

/-- HOL `state_rel_delete_vars` (first declaration,
`word_bignumProofScript.sml:282`): a state that agrees on arrays and clock and
whose registers are a HOL `SUBMAP` of the first state's registers satisfies the
same state relation. HOL's `SUBMAP` is written out as its definition, the
pointwise lookup implication. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "state_rel_delete_vars" 282
  (fmap_as_finite_support_relation := [MiniState.regs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRel_delete_vars_regs {width : Nat} [NeZero width] {β : Type} {C F : Type}
    (s1 s2 : MiniState width)
    (t1 : WordSemStateFiniteExact width C F)
    (cs : β × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
    (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) :
    (s1.arrays = s2.arrays ∧ s1.clock = s2.clock ∧
        ∀ (n : Nat) (v : BitVec width), s2.regs.lookup n = some v → s1.regs.lookup n = some v) →
      stateRel s1 t1 cs t0 frame → stateRel s2 t1 cs t0 frame := by
  intro hsub hrel
  obtain ⟨harrays, hclock, hregs⟩ := hsub
  obtain ⟨hc, ha, hr, hcode, hdiv, htd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14⟩ := hrel
  refine ⟨?_, ?_, ?_, hcode, hdiv, htd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14⟩
  · rw [← hclock]
    exact hc
  · rw [← harrays]
    exact ha
  · intro a v hv
    exact hr a v (hregs a v hv)

/-- HOL `state_rel_delete_vars` (second declaration,
`word_bignumProofScript.sml:293`): deleting a register list preserves the state
relation, since `reg_write v NONE` only erases a register. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "state_rel_delete_vars" 293
  (fmap_as_finite_support_relation := [MiniState.regs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRel_delete_vars {width : Nat} [NeZero width] {β : Type} {C F : Type}
    (vs : List Nat) (s1 : MiniState width)
    (t1 : WordSemStateFiniteExact width C F)
    (cs : β × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
    (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) :
    stateRel s1 t1 cs t0 frame → stateRel (deleteVars vs s1) t1 cs t0 frame := by
  induction vs with
  | nil =>
    intro hrel
    exact hrel
  | cons head tail ih =>
    intro hrel
    have hprev := ih hrel
    have hw : (regWrite head none (deleteVars tail s1)).regs =
        (deleteVars tail s1).regs.eraseEq head := (regWrite_simp head 0 none _).1
    refine stateRel_delete_vars_regs (deleteVars tail s1)
      (regWrite head none (deleteVars tail s1)) t1 cs t0 frame ⟨?_, ?_, ?_⟩ hprev
    · rw [(regWrite_simp head 0 none (deleteVars tail s1)).2.2.1]
    · rw [(regWrite_simp head 0 none (deleteVars tail s1)).2.2.2]
    · intro n v hv
      rw [hw] at hv
      exact HolFiniteMapExact.eraseEq_lookup_some _ head n hv

/-- HOL `state_rel_IN_FDOM` (`word_bignumProofScript.sml:420`): a live mini-state
register is a live temporary register in the `wordSem` store, holding the same
value. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "state_rel_IN_FDOM"
  (fmap_as_finite_support_relation := [MiniState.regs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRel_IN_FDOM {width : Nat} [NeZero width] {β : Type} {C F : Type}
    (s1 : MiniState width)
    (t1 : WordSemStateFiniteExact width C F)
    (cs2 : β × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
    (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (r : Nat) :
    stateRel s1 t1 cs2 t0 frame ∧ r ∈ s1.regs.dom →
      (.temp (BitVec.ofNat 5 r)) ∈ t1.store.dom ∧
        holFapply t1.store (.temp (BitVec.ofNat 5 r)) = .word (holFapply s1.regs r) := by
  intro h
  obtain ⟨hrel, hdom⟩ := h
  obtain ⟨_, _, hr, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hrel
  cases hl : s1.regs.lookup r with
  | none => exact absurd hl hdom
  | some v =>
    have hstore := (hr r v hl).2
    refine ⟨?_, ?_⟩
    · simp only [HolFiniteMapExact.dom, Set.mem_ofPred_eq, hstore]
      simp
    · rw [holFapply_of_lookup hstore, holFapply_of_lookup hl]

end Flapjack.Compiler.Backend.WordBignum
