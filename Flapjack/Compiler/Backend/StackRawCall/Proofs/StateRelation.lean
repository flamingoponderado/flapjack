module

public import Flapjack.Compiler.Backend.StackRawCall
public import Flapjack.Compiler.Backend.StackRawCall.Proofs.StateOk
public import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompLn
public import Flapjack.Compiler.Backend.Semantics.StackSem.State

@[expose] public section

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Canonical roundtrip for the imported full state carrier. This is
Flapjack representation infrastructure, with no separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Literal rawcall state relation: the full state is preserved except code,
whose domain is unchanged. Each source code entry has its own existential
frame-info witness, independent of the outer frame-info argument. The source's
commented compile/oracle clauses are inactive and impose no obligations.
The whole-state equality includes regs/fpRegs/store at the imported canonical
finite-map carrier; code itself is the native Spt, not a finite map. All 22
state fields, configuration and FFI parameters are retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
def stateRel {width : Nat} [NeZero width] {C F : Type} (info : Spt Nat)
    (source target : StackSemStateFiniteExact width C F) : Prop :=
  ∃ code : Spt (HolProg width),
    sptDomain code = sptDomain source.code ∧
    target = { source with code := code } ∧
    stateOk info source.code ∧
    ∀ n body, sptLookup n source.code = some body →
      ∃ entryInfo : Spt Nat, stateOk entryInfo source.code ∧
        sptLookup n code = some (compTop entryInfo body)

/-- The relation unfolded field by field, as HOL's `state_rel_thm` obtains
from `state_rel_def` by `SIMP_RULE` with the state component equality: the
code domains agree, every other field (21 of them) is equal, and the
frame-info and per-entry compilation conditions hold. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "state_rel_thm"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRel_thm {width : Nat} [NeZero width] {C F : Type} :
    ∀ (i : Spt Nat) (s t : StackSemStateFiniteExact width C F),
      stateRel i s t ↔
        sptDomain t.code = sptDomain s.code ∧ t.regs = s.regs ∧ t.fpRegs = s.fpRegs ∧
        t.store = s.store ∧ t.stack = s.stack ∧ t.stackSpace = s.stackSpace ∧
        t.memory = s.memory ∧ t.mdomain = s.mdomain ∧ t.shMdomain = s.shMdomain ∧
        t.bitmaps = s.bitmaps ∧ t.compile = s.compile ∧ t.compileOracle = s.compileOracle ∧
        t.codeBuffer = s.codeBuffer ∧ t.dataBuffer = s.dataBuffer ∧ t.gcFun = s.gcFun ∧
        t.useStack = s.useStack ∧ t.useStore = s.useStore ∧ t.useAlloc = s.useAlloc ∧
        t.clock = s.clock ∧ t.ffi = s.ffi ∧ t.ffiSaveRegs = s.ffiSaveRegs ∧ t.be = s.be ∧
        stateOk i s.code ∧
        ∀ (n : Nat) (b : HolProg width), sptLookup n s.code = some b →
          ∃ i : Spt Nat, stateOk i s.code ∧ sptLookup n t.code = some (compTop i b) := by
  intro i s t
  constructor
  · rintro ⟨code, domain, rfl, ok, entries⟩
    exact ⟨domain, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, ok, entries⟩
  · rintro ⟨domain, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, ok, entries⟩
    refine ⟨t.code, domain, ?_, ok, entries⟩
    cases s
    cases t
    simp_all

/-- Updating the stack space to its own value leaves the state unchanged. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "with_stack_space"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem withStackSpace {width : Nat} [NeZero width] {C F : Type}
    (t1 : StackSemStateFiniteExact width C F) : { t1 with stackSpace := t1.stackSpace } = t1 := rfl

/-- Same-module canonical roundtrip re-export for the field qualifier; Flapjack
representation infrastructure with no HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Flapjack verification infrastructure: the independent empty entry-info
witness makes the literal relation reflexive whenever its outer frame-info
obligation holds. This does not assume a target relation or evaluation. -/
theorem stateRel_self {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source : StackSemStateFiniteExact width C F)
    (frames : stateOk info source.code) : stateRel info source source := by
  refine ⟨source.code, rfl, rfl, frames, ?_⟩
  intro n body entry
  refine ⟨.ln, stateOk_empty source.code, ?_⟩
  simpa only [(compLn info body).1] using entry

/-- Flapjack verification infrastructure: the whole-state equality in the
relation preserves the compile oracle, rather than transporting it through
the pass. The source's commented oracle clause is intentionally inactive. -/
theorem stateRel_compileOracle {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) :
    target.compileOracle = source.compileOracle := by
  obtain ⟨code, _, equality, _⟩ := relation
  subst target
  rfl

end Flapjack.Compiler.Backend.StackRawCall
