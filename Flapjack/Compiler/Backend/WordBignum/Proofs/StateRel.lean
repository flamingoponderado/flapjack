module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.Relations
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

set_option linter.unusedVariables false in
/-- The division-code assumption: for any well-formed division call the compiled
`DivCode` body returns the quotient and remainder. HOL binds the state and
argument quantifiers inside the definition body (`div_code_assum code <=>
!(t1:state) n l ... . ...`); Lean states the same quantifiers as a Pi type so
that the finite-map carrier `WordSemStateFiniteExact` is named in the
signature, as the `fmap_as_finite_support` qualifier requires, and `stateRel`
spells HOL's conjunct as its eta-expansion `∀ t1 ..., divCodeAssum code t1 ...`.
The post-state is bound by a `let` because Lean's parser does not accept a
multi-field record update as a deeply nested argument. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "div_code_assum_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def divCodeAssum {width : Nat} [NeZero width] {C F : Type}
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) :
    ∀ (t1 : WordSemStateFiniteExact width C F) (n l i0 i1 i2 i3 i4 : Nat)
      (w3 w4 w5 : BitVec width) (retVal : WordLocW width), Prop :=
  fun t1 n l i0 i1 i2 i3 i4 w3 w4 w5 retVal =>
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
`wordSem` fields of the original state. HOL's `div_code_assum (:'ffi) (:'c)
t.code` conjunct is written as its eta-expansion `∀ t1 ..., divCodeAssum t.code
t1 ...` because the Lean definition is Pi-typed (see `divCodeAssum`); the two
forms are definitionally the same proposition. -/
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
    (∀ (t1 : WordSemStateFiniteExact width C F) (n l i0 i1 i2 i3 i4 : Nat)
        (w3 w4 w5 : BitVec width) (retVal : WordLocW width),
      divCodeAssum t.code t1 n l i0 i1 i2 i3 i4 w3 w4 w5 retVal) ∧
    t.termdep ≠ 0 ∧
    t0.gcFun = t.gcFun ∧ t0.handler = t.handler ∧ t0.termdep = t.termdep ∧
    t0.code = t.code ∧ t0.be = t.be ∧ t0.ffi = t.ffi ∧
    t0.compile = t.compile ∧ t0.compileOracle = t.compileOracle ∧
    t0.codeBuffer = t.codeBuffer ∧ t0.dataBuffer = t.dataBuffer ∧
    t0.stackLimit = t.stackLimit ∧ t0.stackSize = t.stackSize ∧
    t.store.lookup tempOut = t0.store.lookup tempOut ∧
    (∀ n, (∀ r, n ≠ .temp r) → t.store.lookup n = t0.store.lookup n)

end Flapjack.Compiler.Backend.WordBignum
