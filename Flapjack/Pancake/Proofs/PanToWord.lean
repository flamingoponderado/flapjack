import Flapjack.HolRef
import Flapjack.Pancake.PanLang.Prog
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.PanToWord
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.DeclContextExact
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Misc.Option
import Flapjack.Misc.Sptree
import Flapjack.HolArb

/-!
The source-level lemmas from CakeML's `pan_to_wordProofScript.sml`.
This is the counterpart module for theorem ports from that HOL proof script.
-/

namespace Flapjack

/-- Exact port of HOL `pan_exps_of_nested_seq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:1018`).  Enumerating
    the expressions of a nested sequence is the concatenation of the
    per-statement expression lists.  This is a concrete proof consumer of the
    exact PanProps `expsOfHOL` port. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_exps_of_nested_seq"]
theorem panExpsOfNestedSeqHOL {width : Nat} [NeZero width]
    (statements : List (Flapjack.Pancake.PanLang.ProgHOL width)) :
    expsOfHOL (Flapjack.Pancake.PanLang.nestedSeqHOL statements) =
      (statements.map expsOfHOL).flatten := by
  induction statements with
  | nil => rfl
  | cons statement statements ih =>
      simp only [Flapjack.Pancake.PanLang.nestedSeqHOL, expsOfHOL, List.map_cons,
        List.flatten_cons, ih]

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

/-! ## Local definitions of `pan_to_wordProofScript.sml` -/

namespace PanToWordProofWitnesses

/-- Canonical roundtrip of the Crep state carrier, re-exported for the
`fmap_as_finite_support_relation` qualifier of `crep_state_def`. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

/-- Canonical roundtrip of the Loop state carrier, re-exported for the
`fmap_as_finite_support_relation` qualifier of `loop_state_def`. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical roundtrip of the Pan state carrier, re-exported for the
`fmap_as_finite_support` qualifier of `globals_allocatable_def`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

end PanToWordProofWitnesses

/-- Exact HOL `crep_state_def` (`pan_to_wordProofScript.sml:14-27`): the Crep
state built from a Pan state, a Pan program and a memory. `alist_to_fmap` is
the canonical update of the empty map with the reversed association list (the
accepted pan_to_crep convention), and `pan_to_crep$compile_prog` is the
reviewed `compileProgDeclsHOLW`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "crep_state_def"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
def crepStateHOL {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (pan_code : List (DeclHOL width))
    (mem : BitVec width → HolWordLab width) : CrepSemHOLState width σ where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty.updateList (compileProgDeclsHOLW pan_code).reverse
  memory := mem
  memaddrs := s.memaddrs
  shMemaddrs := s.shMemaddrs
  clock := s.clock
  be := s.be
  ffi := s.ffi
  topAddr := s.topAddr
  baseAddr := s.baseAddr

/-- Exact HOL `wloc_wlab_def` (`pan_to_wordProofScript.sml:29-31`):
`wloc_wlab (Word w) = Word w`. HOL gives no clause for `Loc`, so that case is
the shared unspecified value `holArb`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "wloc_wlab_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wlocWlabHOL {width : Nat} [NeZero width] :
    WordLocW width → HolWordLab width
  | .word w => .word w
  | .loc _ _ => @holArb (HolWordLab width) ⟨.word 0⟩

/-- Exact HOL `no_labels_def` (`pan_to_wordProofScript.sml:39-41`):
`no_labels mem dom = (∀a. a ∈ dom ⇒ ∃w. mem a = Word w)`. As in the elaborated
HOL constant (`pan_to_word_definitions_probe`), the address type `α` is
arbitrary and independent of the word width; the set `dom` is a predicate, as
in the tagged `addresses`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "no_labels_def"
  (words_as_type_indexed_bitvec)]
def noLabelsHOL {α : Type} {width : Nat} [NeZero width] (mem : α → WordLocW width)
    (dom : α → Prop) : Prop :=
  ∀ a, dom a → ∃ w, mem a = .word w

/-- Exact HOL `loop_state_def` (`pan_to_wordProofScript.sml:43-56`). `LN` is
`Spt.ln`, `fromAList` the Sptree rendering `sptFromAList`, and
`crep_to_loop$compile_prog` the reviewed `compileProgHOLExact`. The Loop
carrier renders its `'a word set` domains as Boolean predicates; the Crep
domains are Lean propositions, so membership is decided classically, which
denotes the same set. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "loop_state_def"
  (fmap_as_finite_support_relation := [LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
noncomputable def loopStateHOL {width : Nat} {σ : Type} [NeZero width]
    (s : CrepSemHOLState width σ) (c : AsmArchitecture)
    (crep_code : List (MlString × List Nat × CrepProgHOL width)) (ck : Nat)
    (mem : BitVec width → WordLocW width) : LoopSemStateFiniteExact width σ :=
  open Classical in
  { locals := .ln
    globals := HolFiniteMapExact.empty
    memory := mem
    mdomain := fun a => decide (s.memaddrs a)
    shMdomain := fun a => decide (s.shMemaddrs a)
    code := sptFromAList (compileProgHOLExact c crep_code)
    clock := ck
    be := s.be
    ffi := s.ffi
    topAddr := s.topAddr
    baseAddr := s.baseAddr }

/-- Exact HOL `distinct_params_def` (`pan_to_wordProofScript.sml:58-61`):
`distinct_params prog <=> EVERY (λ(name,params,body). ALL_DISTINCT params) prog`.
HOL's polymorphic triple type is kept as three type parameters. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "distinct_params_def"]
def distinctParamsHOL {α β γ : Type} (prog : List (α × List β × γ)) : Prop :=
  ∀ entry ∈ prog, entry.2.1.Nodup

/-- Exact HOL `globals_allocatable_def` (`pan_to_wordProofScript.sml:228-239`).
`THE` is the reviewed `holThe`, `DISJOINT` of the two address sets is the
absence of a common member, `bytes_in_word` is `bytesInWord width`
(`n2w (dimindex(:α) DIV 8)`), `w2n` is `BitVec.toNat`, and `dimword(:α)` is
`2 ^ width`. As in the elaborated HOL constant
(`pan_to_word_definitions_probe`), the program's word dimension `width'` is
independent of the state's `width`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "globals_allocatable_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
noncomputable def globalsAllocatableHOL {width width' : Nat} {σ : Type} [NeZero width]
    [NeZero width'] (s : PanSemStateFiniteExact width σ) (pan_code : List (DeclHOL width')) :
    Prop :=
  let dec_shs := decShapesHOL pan_code
  let struct_ctxt := decsStcnamesHOLExact (width := width') [] pan_code
  let sz := (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum
  struct_ctxt ≠ none ∧
  (∀ a, ¬ (s.memaddrs a ∧ Compiler.Backend.StackRemove.addresses s.topAddr sz a)) ∧
  ¬ s.memaddrs (s.topAddr + Compiler.Backend.StackRemove.bytesInWord width * BitVec.ofNat width sz) ∧
  sz * (Compiler.Backend.StackRemove.bytesInWord width).toNat < 2 ^ width

end Flapjack
