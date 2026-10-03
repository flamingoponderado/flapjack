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
import Flapjack.Pancake.Proofs.PanSimp
import Flapjack.Pancake.LoopToWord.Proofs.ProgramNames
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.Semantics.PanProps.HasMain
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsDecls
import Flapjack.Pancake.PanGlobals.CompileExpExact
import Flapjack.Pancake.PanStructs.CompileDeclsExact
import Flapjack.Pancake.Proofs.PanStructs.CompileShapeN
import Flapjack.Pancake.Proofs.PanStructs.DecsStcnamesNames
import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural

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

namespace PanToWordProofWitnesses

/-- Canonical roundtrip of the pan_globals context carrier, re-exported for the
`fmap_as_finite_support_relation := [PanGlobalsContextExact.globals]`
qualifier of the `compile_decs` lemmas. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

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


/-! ## Structural lemmas of `pan_to_wordProofScript.sml` -/

/-- Exact HOL `wloc_wlab_wlab_wloc` (`pan_to_wordProofScript.sml:33-37`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "wloc_wlab_wlab_wloc"
  (words_as_type_indexed_bitvec)]
theorem wlocWlabWlabWlocHOL {width : Nat} [NeZero width] (w : HolWordLab width) :
    wlocWlabHOL (wlabWlocExact w) = w := by
  cases w
  rfl

/-- Exact HOL `loop_state_simps` (`pan_to_wordProofScript.sml:77-93`). The
Loop carrier's Boolean domains are compared with the Crep domains through
membership, as in the accepted crep_to_loop `state_rel_imp_semantics`, and
`isEmpty` is `sptIsEmpty`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "loop_state_simps"
  (fmap_as_finite_support_relation := [LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem loopStateSimpsHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s : CrepSemHOLState width σ) (c : AsmArchitecture)
      (crep_code : List (MlString × List Nat × CrepProgHOL width)) (ck : Nat)
      (mem : BitVec width → WordLocW width),
      (loopStateHOL s c crep_code ck mem).memory = mem ∧
      (fun a => (loopStateHOL s c crep_code ck mem).mdomain a = true) = s.memaddrs ∧
      (fun a => (loopStateHOL s c crep_code ck mem).shMdomain a = true) = s.shMemaddrs ∧
      (loopStateHOL s c crep_code ck mem).clock = ck ∧
      ((loopStateHOL s c crep_code ck mem).be = true ↔ s.be = true) ∧
      (loopStateHOL s c crep_code ck mem).ffi = s.ffi ∧
      (loopStateHOL s c crep_code ck mem).baseAddr = s.baseAddr ∧
      (loopStateHOL s c crep_code ck mem).topAddr = s.topAddr ∧
      (loopStateHOL s c crep_code ck mem).globals = HolFiniteMapExact.empty ∧
      sptIsEmpty (loopStateHOL s c crep_code ck mem).locals = true ∧
      (loopStateHOL s c crep_code ck mem).code = sptFromAList (compileProgHOLExact c crep_code) := by
  intro s c crep_code ck mem
  refine ⟨rfl, ?_, ?_, rfl, Iff.rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · funext a
    simp [loopStateHOL]

/-- Exact HOL `first_compile_prog_all_distinct`
(`pan_to_wordProofScript.sml:95-103`); `c` is free in the HOL theorem and is
universally quantified first. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "first_compile_prog_all_distinct"
  (words_as_type_indexed_bitvec)]
theorem panToWordFirstCompileProgAllDistinctHOL {width : Nat} [NeZero width]
    (c : AsmArchitecture) :
    ∀ (prog : List (DeclHOL width)), ((functionsHOL prog).map Prod.fst).Nodup →
      ((panToWordCompileProgHOL c prog).map Prod.fst).Nodup := by
  intro prog _
  exact loopToWordFirstCompileAllDistinct _ (firstCompileProgAllDistinctExact c _)

/-- Exact HOL `dec_shapes_compile_prog` (`pan_to_wordProofScript.sml:241-246`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "dec_shapes_compile_prog"]
theorem decShapesCompileProgHOL {width : Nat} [NeZero width] :
    ∀ (pan_code : List (DeclHOL width)),
      decShapesHOL (panSimpDeclsHOL pan_code) = decShapesHOL pan_code := by
  intro pan_code
  induction pan_code with
  | nil => simp [panSimpDeclsHOL, decShapesHOL]
  | cons d ds ih => cases d <;> simp_all [panSimpDeclsHOL, decShapesHOL]

/-- Exact HOL `function_names_compile_prog` (`pan_to_wordProofScript.sml:248-253`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "function_names_compile_prog"]
theorem functionNamesCompileProgHOL {width : Nat} [NeZero width] :
    ∀ (pan_code : List (DeclHOL width)),
      (functionsHOL (panSimpDeclsHOL pan_code)).map Prod.fst =
        (functionsHOL pan_code).map Prod.fst := by
  intro pan_code
  rw [functionsHOL_panSimpDeclsHOL_eq, List.map_map]
  rfl

/-- Exact HOL `no_names_compile_prog` (`pan_to_wordProofScript.sml:318-328`);
`EVERY` is membership quantification over the Boolean classifiers. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "no_names_compile_prog"]
theorem noNamesCompileProgHOL {width : Nat} [NeZero width] (pan_code : List (DeclHOL width)) :
    (∀ d ∈ pan_code, isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) →
    ∀ d ∈ panSimpDeclsHOL pan_code,
      isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true := by
  induction pan_code with
  | nil => intro _ d hd; simp [panSimpDeclsHOL] at hd
  | cons d ds ih =>
    intro h e he
    cases d with
    | function f =>
      simp only [panSimpDeclsHOL, List.mem_cons] at he
      rcases he with rfl | he
      · simp [isFunctionHOL]
      · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) e he
    | decl sh v ex =>
      simp only [panSimpDeclsHOL, List.mem_cons] at he
      rcases he with rfl | he
      · exact h _ (List.mem_cons_self ..)
      · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) e he
    | exnDecl n sh =>
      simp only [panSimpDeclsHOL, List.mem_cons] at he
      rcases he with rfl | he
      · exact h _ (List.mem_cons_self ..)
      · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) e he
    | name n fs =>
      simp only [panSimpDeclsHOL, List.mem_cons] at he
      rcases he with rfl | he
      · exact h _ (List.mem_cons_self ..)
      · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) e he

/-- Exact HOL `semantics_decls_has_main'` (`pan_to_wordProofScript.sml:330-341`);
`ALOOKUP` is `List.lookup`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "semantics_decls_has_main'"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem semanticsDeclsHasMainPanToWordHOL {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (start : MlS) (code : List (DeclHOL width)) :
    s.code = HolFiniteMapExact.empty ∧ ((functionsHOL code).map Prod.fst).Nodup ∧
      PanSemStateFiniteExact.semanticsDecls s start code ≠ .fail →
    ∃ body rshape, List.lookup start (functionsHOL code) = some ([], body, rshape) := by
  rintro ⟨hcode, hnd, hsem⟩
  obtain ⟨body, rshape, h⟩ := PanPropsHasMain.semanticsDeclsHasMainPrime s start code hsem
  rw [hcode, PanGlobalsCompileTopSemanticsDecls.emptyUpdateListLookup _ _ hnd] at h
  exact ⟨body, rshape, h⟩


/-- Exact HOL `map_map2_fst_lemma` (`pan_to_wordProofScript.sml:118-126`);
`MAP2 (λx y. (x,y))` is `List.zip`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "map_map2_fst_lemma"]
theorem mapMap2FstLemmaHOL {α β : Type} :
    ∀ (xs : List α) (ys : List β),
      (List.zipWith (fun x y => (x, y)) xs ys).map Prod.fst =
        xs.take (min xs.length ys.length) := by
  intro xs
  induction xs with
  | nil => intro ys; simp
  | cons x xs ih =>
    intro ys
    cases ys with
    | nil => simp
    | cons y ys => simp [ih, Nat.succ_min_succ]

/-- Exact HOL `exp_ids_nested_seq` (`pan_to_wordProofScript.sml:128-133`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exp_ids_nested_seq"]
theorem expIdsNestedSeqHOL {width : Nat} [NeZero width] :
    ∀ (ps : List (ProgHOL width)), expIdsHOL (nestedSeqHOL ps) = (ps.map expIdsHOL).flatten := by
  intro ps
  induction ps with
  | nil => simp [nestedSeqHOL, expIdsHOL]
  | cons p ps ih => simp [nestedSeqHOL, expIdsHOL, ih]

/-- Exact HOL `exp_ids_compile_globals` (`pan_to_wordProofScript.sml:135-142`),
by the source's `compile_ind` recursion realised as strong induction on the
program size. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exp_ids_compile_globals"
  (fmap_as_finite_support_relation := [PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem expIdsCompileGlobalsHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (p : ProgHOL width),
      expIdsHOL (compileProgExactHOL ctxt p) = expIdsHOL p := by
  intro ctxt p
  induction p using compileProgExactHOL.induct ctxt
  case case30 =>
    rename_i p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    cases p <;> simp_all [compileProgExactHOL, expIdsHOL]
  all_goals
    rw [compileProgExactHOL]
    try simp_all [expIdsHOL]
    try split <;> simp_all [expIdsHOL]

/-- Exact HOL `exp_ids_fperm` (`pan_to_wordProofScript.sml:144-151`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exp_ids_fperm"
  (words_as_type_indexed_bitvec)]
theorem expIdsFpermHOL {width : Nat} [NeZero width] :
    ∀ (f g : MlS) (p : ProgHOL width), expIdsHOL (fpermHOL f g p) = expIdsHOL p := by
  intro f g p
  induction p using fpermHOL.induct
  case case7 =>
    rename_i p _ _ _ _ _ _
    cases p <;> simp_all [fpermHOL, expIdsHOL]
  case case5 info _ _ ih =>
    rcases info with _ | ⟨k, _ | ⟨e, b, h⟩⟩ <;> simp_all [fpermHOL, expIdsHOL]
  all_goals
    rw [fpermHOL]
    try simp_all [expIdsHOL]
    try split <;> simp_all [expIdsHOL]

/-- Exact HOL `compile_decs_exp_ids` (`pan_to_wordProofScript.sml:153-161`);
`exp_ids ∘ FST ∘ SND ∘ SND` on a function entry `(name, params, body, rshape)`
is `expIdsHOL` of the body. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "compile_decs_exp_ids"
  (fmap_as_finite_support_relation := [PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileDecsExpIdsHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (pan_code : List (DeclHOL width)),
      (functionsHOL (compileDecsExactHOL ctxt pan_code).2.1).map (fun e => expIdsHOL e.2.2.1) =
        (functionsHOL pan_code).map (fun e => expIdsHOL e.2.2.1) := by
  intro ctxt pan_code
  induction pan_code generalizing ctxt with
  | nil => simp [compileDecsExactHOL, functionsHOL]
  | cons d ds ih =>
    cases d <;> simp_all [compileDecsExactHOL, functionsHOL, expIdsCompileGlobalsHOL]

/-- Exact HOL `fperm_exp_ids` (`pan_to_wordProofScript.sml:163-172`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "fperm_exp_ids"
  (words_as_type_indexed_bitvec)]
theorem fpermExpIdsHOL {width : Nat} [NeZero width] :
    ∀ (f g : MlS) (pan_code : List (DeclHOL width)),
      (functionsHOL (fpermDecsHOL f g pan_code)).map (fun e => expIdsHOL e.2.2.1) =
        (functionsHOL pan_code).map (fun e => expIdsHOL e.2.2.1) := by
  intro f g pan_code
  induction pan_code with
  | nil => simp [fpermDecsHOL, functionsHOL]
  | cons d ds ih =>
    cases d <;> simp_all [fpermDecsHOL, functionsHOL, expIdsFpermHOL]

/-- Exact HOL `compile_decs_no_exp_ids_main` (`pan_to_wordProofScript.sml:174-180`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "compile_decs_no_exp_ids_main"
  (fmap_as_finite_support_relation := [PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileDecsNoExpIdsMainHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (prog : List (DeclHOL width)),
      ∀ x ∈ (compileDecsExactHOL ctxt prog).1, expIdsHOL x = [] := by
  intro ctxt prog
  induction prog generalizing ctxt with
  | nil => simp [compileDecsExactHOL]
  | cons d ds ih =>
    cases d <;> simp [compileDecsExactHOL, expIdsHOL] <;> exact ih _

/-- Exact HOL `functions_resort_decls` (`pan_to_wordProofScript.sml:182-187`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "functions_resort_decls"]
theorem functionsResortDeclsHOL {width : Nat} [NeZero width] (xs : List (DeclHOL width)) :
    functionsHOL (resortDeclsHOL xs) = functionsHOL xs := by
  have hname : ∀ ys : List (DeclHOL width), functionsHOL (ys.filter isNameHOL) = [] := by
    intro ys
    induction ys with
    | nil => rfl
    | cons d ds ih => cases d <;> simp_all [functionsHOL, isNameHOL, List.filter]
  have hexn : ∀ ys : List (DeclHOL width), functionsHOL (ys.filter isExnDeclHOL) = [] := by
    intro ys
    induction ys with
    | nil => rfl
    | cons d ds ih => cases d <;> simp_all [functionsHOL, isExnDeclHOL, List.filter]
  simp only [resortDeclsHOL, functionsHOL_append, hname, hexn, functionsHOL_filter_isDecl,
    functionsHOL_filter_isFunction, List.nil_append]


/-- Exact HOL `exp_ids_structs_compile` (`pan_to_wordProofScript.sml:263-271`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exp_ids_structs_compile"
  (words_as_type_indexed_bitvec)]
theorem expIdsStructsCompileHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : Pancake.PanStructs.CompileShapeExact.ContextExact) (prog : ProgHOL width),
      expIdsHOL (Pancake.PanStructs.CompileShapeExact.compileProgExact ctxt prog) =
        expIdsHOL prog := by
  intro ctxt prog
  induction ctxt, prog using Pancake.PanStructs.CompileShapeExact.compileProgExact.induct
  case case18 =>
    rename_i p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    cases p <;> simp_all [Pancake.PanStructs.CompileShapeExact.compileProgExact, expIdsHOL]
  case case11 _ _ _ _ handler ih =>
    rcases handler with _ | ⟨e, b, h⟩ <;>
      simp_all [Pancake.PanStructs.CompileShapeExact.compileProgExact, expIdsHOL]
  all_goals
    rw [Pancake.PanStructs.CompileShapeExact.compileProgExact]
    try simp_all [expIdsHOL]

/-- Exact HOL `function_names_structs_compile_decs`
(`pan_to_wordProofScript.sml:255-261`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "function_names_structs_compile_decs"
  (words_as_type_indexed_bitvec)]
theorem functionNamesStructsCompileDecsHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : Pancake.PanStructs.CompileShapeExact.ContextExact) (pan_code : List (DeclHOL width)),
      (functionsHOL (Pancake.PanStructs.CompileShapeExact.compileDeclsExact ctxt pan_code).1).map
          Prod.fst = (functionsHOL pan_code).map Prod.fst := by
  intro ctxt pan_code
  induction pan_code generalizing ctxt with
  | nil => simp [Pancake.PanStructs.CompileShapeExact.compileDeclsExact, functionsHOL]
  | cons d ds ih =>
    cases d <;> simp_all [Pancake.PanStructs.CompileShapeExact.compileDeclsExact, functionsHOL]

/-- Exact HOL `function_names_structs_compile_top`
(`pan_to_wordProofScript.sml:312-316`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "function_names_structs_compile_top"
  (words_as_type_indexed_bitvec)]
theorem functionNamesStructsCompileTopHOL {width : Nat} [NeZero width] :
    ∀ (pan_code : List (DeclHOL width)),
      (functionsHOL (Pancake.PanStructs.CompileShapeExact.compileTopExact pan_code)).map Prod.fst =
        (functionsHOL pan_code).map Prod.fst := by
  intro pan_code
  exact functionNamesStructsCompileDecsHOL _ pan_code

/-- Exact HOL `functions_FILTER_nil` (`pan_to_wordProofScript.sml:412-417`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "functions_FILTER_nil"]
theorem functionsFilterNilHOL {width : Nat} [NeZero width] (xs : List (DeclHOL width)) :
    functionsHOL (xs.filter isExnDeclHOL) = [] := by
  induction xs with
  | nil => rfl
  | cons d ds ih => cases d <;> simp_all [functionsHOL, isExnDeclHOL, List.filter]

/-- Exact HOL `semantics_decls_decl_structs` (`pan_to_wordProofScript.sml:506-512`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "semantics_decls_decl_structs"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem semanticsDeclsDeclStructsHOL {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (start : MlS) (pan_code : List (DeclHOL width)) :
    PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ .fail →
    ∃ s_ctxt, decsStcnamesHOLExact [] pan_code = some s_ctxt := by
  intro h
  unfold PanSemStateFiniteExact.semanticsDecls at h
  cases hd : decsStcnamesHOLExact [] pan_code with
  | none => simp [hd] at h
  | some c => exact ⟨c, rfl⟩

/-- Exact HOL `functions_compile_decs_exns` (`pan_to_wordProofScript.sml:519-527`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "functions_compile_decs_exns"
  (fmap_as_finite_support_relation := [PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem functionsCompileDecsExnsHOL {width : Nat} [NeZero width]
    (ctxt : PanGlobalsContextExact width) (prog : List (DeclHOL width)) :
    functionsHOL (compileDecsExactHOL ctxt prog).2.2.1 = [] := by
  rcases h : compileDecsExactHOL ctxt prog with ⟨a, b, c, d⟩
  rw [PanGlobalsCompileDecsStructural.compile_decs_exns_are_exnsHOL ctxt prog a b c d h]
  exact functionsFilterNilHOL prog


/-- The exception-code association list depends only on the exception names:
`size_of_eids` is their number. Flapjack infrastructure for the `get_eids`
domain lemmas below; no HOL original. -/
theorem getEidsEntriesHOL_congr {width : Nat} [NeZero width] (a b : List (DeclHOL width))
    (h : (exceptionsHOL a).map Prod.fst = (exceptionsHOL b).map Prod.fst) :
    getEidsEntriesHOL a = getEidsEntriesHOL b := by
  have hl : sizeOfEidsHOL a = sizeOfEidsHOL b := by
    rw [← exceptionsHOL_length_eq_sizeOfEidsHOL, ← exceptionsHOL_length_eq_sizeOfEidsHOL,
      ← List.length_map (f := Prod.fst), h, List.length_map]
  simp only [getEidsEntriesHOL, h, hl]

/-- pan_simp leaves the exception declarations unchanged. Flapjack
infrastructure; no HOL original. -/
theorem exceptionsHOL_panSimpDeclsHOL {width : Nat} [NeZero width] (prog : List (DeclHOL width)) :
    exceptionsHOL (panSimpDeclsHOL prog) = exceptionsHOL prog := by
  induction prog with
  | nil => simp [panSimpDeclsHOL, exceptionsHOL]
  | cons d ds ih => cases d <;> simp_all [panSimpDeclsHOL, exceptionsHOL]

/-- pan_structs keeps the exception names in order (only their shapes are
compiled). Flapjack infrastructure; no HOL original. -/
theorem exceptionNames_compileDeclsExact {width : Nat} [NeZero width] :
    ∀ (ctxt : Pancake.PanStructs.CompileShapeExact.ContextExact) (prog : List (DeclHOL width)),
      (exceptionsHOL (Pancake.PanStructs.CompileShapeExact.compileDeclsExact ctxt prog).1).map
          Prod.fst = (exceptionsHOL prog).map Prod.fst := by
  intro ctxt prog
  induction prog generalizing ctxt with
  | nil => simp [Pancake.PanStructs.CompileShapeExact.compileDeclsExact, exceptionsHOL]
  | cons d ds ih =>
    cases d <;> simp_all [Pancake.PanStructs.CompileShapeExact.compileDeclsExact, exceptionsHOL]

/-- Exact HOL `get_eids_pan_simp_compile_eq` (`pan_to_wordProofScript.sml:105-116`);
`FDOM` equality is pointwise definedness of the canonical lookups. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "get_eids_pan_simp_compile_eq"
  (fmap_as_finite_support_result_observations := [Flapjack.getEidsFromDeclsHOL])]
theorem getEidsPanSimpCompileEqHOL {width : Nat} [NeZero width] :
    ∀ (prog : List (DeclHOL width)) (key : MlS),
      ((getEidsFromDeclsHOL prog).lookup key).isSome =
        ((getEidsFromDeclsHOL (panSimpDeclsHOL prog)).lookup key).isSome := by
  intro prog key
  have h := getEidsEntriesHOL_congr prog (panSimpDeclsHOL prog)
    (by rw [exceptionsHOL_panSimpDeclsHOL])
  simp only [getEidsFromDeclsHOL, h]

/-- Exact HOL `FDOM_get_eids_pan_globals_compile_eq`
(`pan_to_wordProofScript.sml:189-226`); `ALOOKUP` is `List.lookup`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FDOM_get_eids_pan_globals_compile_eq"
  (fmap_as_finite_support_result_observations := [Flapjack.getEidsFromDeclsHOL])]
theorem fdomGetEidsPanGlobalsCompileEqHOL {width : Nat} [NeZero width] :
    ∀ (pan_code : List (DeclHOL width)) (main : MlS) (args : List (MlS × ShapeHOL))
      (body : ProgHOL width) (rshape : ShapeHOL),
      List.lookup main (functionsHOL pan_code) = some (args, body, rshape) →
      ∀ key, ((getEidsFromDeclsHOL (compileTopExactHOL pan_code main)).lookup key).isSome =
        ((getEidsFromDeclsHOL pan_code).lookup key).isSome := by
  intro pan_code main args body rshape hl key
  have h := getEidsEntriesHOL_congr (compileTopExactHOL pan_code main) pan_code
    (by rw [PanGlobalsCompileDecsStructural.exceptions_compile_topHOL pan_code main _ hl])
  simp only [getEidsFromDeclsHOL, h]

/-- Exact HOL `FDOM_get_eids_structs_compile_decs_eq` (first declaration,
`pan_to_wordProofScript.sml:273-283`, local in HOL). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FDOM_get_eids_structs_compile_decs_eq" 273
  (fmap_as_finite_support_result_observations := [Flapjack.getEidsFromDeclsHOL])]
theorem fdomGetEidsStructsCompileDecsEqHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : Pancake.PanStructs.CompileShapeExact.ContextExact) (prog : List (DeclHOL width))
      (key : MlS),
      ((getEidsFromDeclsHOL prog).lookup key).isSome =
        ((getEidsFromDeclsHOL
          (Pancake.PanStructs.CompileShapeExact.compileDeclsExact ctxt prog).1).lookup key).isSome := by
  intro ctxt prog key
  have h := getEidsEntriesHOL_congr prog _ (exceptionNames_compileDeclsExact ctxt prog).symm
  simp only [getEidsFromDeclsHOL, h]

/-- Exact HOL `FDOM_get_eids_structs_compile_eq`
(`pan_to_wordProofScript.sml:285-291`, local in HOL). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FDOM_get_eids_structs_compile_eq"
  (fmap_as_finite_support_result_observations := [Flapjack.getEidsFromDeclsHOL])]
theorem fdomGetEidsStructsCompileEqHOL {width : Nat} [NeZero width]
    (prog : List (DeclHOL width)) (key : MlS) :
    ((getEidsFromDeclsHOL (Pancake.PanStructs.CompileShapeExact.compileTopExact prog)).lookup
        key).isSome = ((getEidsFromDeclsHOL prog).lookup key).isSome :=
  (fdomGetEidsStructsCompileDecsEqHOL _ prog key).symm

/-- Exact HOL `FDOM_get_eids_structs_compile_decs_eq` (second declaration of
the name, `pan_to_wordProofScript.sml:293-303`, local in HOL), which states
`size_of_eids` preservation. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FDOM_get_eids_structs_compile_decs_eq" 293
  (words_as_type_indexed_bitvec)]
theorem sizeOfEidsStructsCompileDecsEqHOL {width : Nat} [NeZero width] :
    ∀ (ctxt : Pancake.PanStructs.CompileShapeExact.ContextExact) (prog : List (DeclHOL width)),
      sizeOfEidsHOL prog =
        sizeOfEidsHOL (Pancake.PanStructs.CompileShapeExact.compileDeclsExact ctxt prog).1 := by
  intro ctxt prog
  rw [← exceptionsHOL_length_eq_sizeOfEidsHOL, ← exceptionsHOL_length_eq_sizeOfEidsHOL,
    ← List.length_map (f := Prod.fst), ← exceptionNames_compileDeclsExact ctxt prog,
    List.length_map]

/-- Exact HOL `size_of_eids_structs_compile_eq`
(`pan_to_wordProofScript.sml:305-310`, local in HOL). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "size_of_eids_structs_compile_eq"
  (words_as_type_indexed_bitvec)]
theorem sizeOfEidsStructsCompileEqHOL {width : Nat} [NeZero width] (prog : List (DeclHOL width)) :
    sizeOfEidsHOL (Pancake.PanStructs.CompileShapeExact.compileTopExact prog) =
      sizeOfEidsHOL prog :=
  (sizeOfEidsStructsCompileDecsEqHOL _ prog).symm

/-- Exact HOL `size_of_eids_compile_top` (`pan_to_wordProofScript.sml:364-410`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "size_of_eids_compile_top"
  (words_as_type_indexed_bitvec)]
theorem sizeOfEidsCompileTopHOL {width : Nat} [NeZero width]
    (pan_code : List (DeclHOL width)) (main : MlS) (args : List (MlS × ShapeHOL))
    (body : ProgHOL width) (rshape : ShapeHOL) :
    List.lookup main (functionsHOL pan_code) = some (args, body, rshape) →
    sizeOfEidsHOL (compileTopExactHOL pan_code main) = sizeOfEidsHOL pan_code := by
  intro hl
  rw [← exceptionsHOL_length_eq_sizeOfEidsHOL, ← exceptionsHOL_length_eq_sizeOfEidsHOL,
    PanGlobalsCompileDecsStructural.exceptions_compile_topHOL pan_code main _ hl]


/-- Exact HOL `lookup_first_name_compile_prog_main`
(`pan_to_wordProofScript.sml:63-75`). `make_funcs` is the reviewed
crep_to_loop `crepToLoopMakeFuncsExactHOL`, `first_name` is `firstLoopName`,
`fromAList`/`lookup` are the Sptree renderings, and the free `c` and
`crep_code` are bound explicitly. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "lookup_first_name_compile_prog_main"
  (fmap_as_finite_support_result_observations := [crepToLoopMakeFuncsExactHOL])]
theorem lookupFirstNameCompileProgMainHOL {width : Nat} [NeZero width] (c : AsmArchitecture)
    (crep_code : List (MlString × List Nat × CrepProgHOL width)) :
    (crepToLoopMakeFuncsExactHOL crep_code).lookup (ofString "main") = some (firstLoopName, 0) →
    ∃ prog, sptLookup firstLoopName (sptFromAList (compileProgHOLExact c crep_code)) =
      some ([], prog) := by
  intro h
  obtain ⟨heq, hlen⟩ := initialProgMakeFuncsElExact crep_code (ofString "main") 0
    (by simpa using h)
  cases crep_code with
  | nil => simp at hlen
  | cons e rest =>
    have he : (ofString "main", ([] : List Nat), e.2.2) = e := heq
    obtain ⟨name, params, body⟩ := e
    have hp : params = [] := by
      have := congrArg (fun x => x.2.1) he
      simpa using this.symm
    subst hp
    simp only [compileProgHOLExact, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.zipWith_cons_cons, sptFromAList]
    exact ⟨_, sptLookup_sptInsert_same _ _ _⟩


/-- `make_funcs` maps the name of the first program entry to the first label
and that entry's arity (first binding wins). Flapjack infrastructure; no HOL
original. -/
theorem crepToLoopMakeFuncsExactHOL_head {α β γ : Type} (k : α) (params : List β) (b : γ)
    (rest : List (α × List β × γ)) :
    (crepToLoopMakeFuncsExactHOL ((k, params, b) :: rest)).lookup k =
      some (firstLoopName, params.length) := by
  classical
  rw [holFmapAsFiniteSupportResultWitness_crepToLoopMakeFuncsExactHOL]
  simp only [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons, List.map_cons,
    List.reverse_cons, FUPDATE_LIST_HOL, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp [FUPDATE_HOL]

/-- Exact HOL `FLOOKUP_make_funcs_main` (`pan_to_wordProofScript.sml:419-443`):
`make_funcs` (crep_to_loop) of `pan_to_crep$compile_prog (compile_top pan_code
main)` maps `main` to `(first_name, 0)`. `ALOOKUP` is `List.lookup`; the free
variables are bound explicitly. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FLOOKUP_make_funcs_main"
  (fmap_as_finite_support_result_observations := [crepToLoopMakeFuncsExactHOL])]
theorem flookupMakeFuncsMainHOL {width : Nat} [NeZero width] (pan_code : List (DeclHOL width))
    (main : MlS) (body : ProgHOL width) (rshape : ShapeHOL) :
    List.lookup main (functionsHOL pan_code) = some ([], body, rshape) →
    (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW (compileTopExactHOL pan_code main))).lookup
      main = some (firstLoopName, 0) := by
  intro hl
  have hfun : ∃ b' rest, functionsHOL (compileTopExactHOL pan_code main) =
      (main, [], b', rshape) :: rest := by
    unfold compileTopExactHOL
    rw [compileTopFunctionLookup_eq_lookup, hl]
    simp only
    rw [PanGlobalsCompileDecsStructural.compile_decs_exns_are_exnsHOL _ _ _ _ _ _ rfl,
      functionsHOL_append, functionsFilterNilHOL]
    exact ⟨_, _, rfl⟩
  obtain ⟨b', rest, hf⟩ := hfun
  simp only [compileProgDeclsHOLW, compileToCrepExactHOLW, hf, List.map_cons,
    CrepInlineCanonical.compileInlTopHOLExact, CrepInlineCanonical.compileInlProgHOLExactWithSupport]
  rw [crepToLoopMakeFuncsExactHOL_head]
  simp [crepVarsHOL, sizeOfShapeHOL]

/-- Exact HOL `compile_shape_no_name` (`pan_to_wordProofScript.sml:445-458`),
over pan_structsProof's `compile_shape_n` (`compileShapeNHOL`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "compile_shape_no_name"]
theorem compileShapeNoNamePanToWordHOL {α : Type} :
    ∀ (ctxt : List (MlS × List (α × ShapeHOL))) (n : Nat) (sh : ShapeHOL),
      isWfShapeExactHOL [] (Pancake.PanStructs.CompileShapeExact.compileShapeNHOL ctxt n sh) =
        true :=
  Pancake.PanStructs.CompileShapeExact.compileShapeNNoName


/-- `size_decs_stcnames_compile_decs_structs`, generic in the memory-domain
decider of `evaluate_decls`. Flapjack infrastructure for the tagged theorem
below; no separate HOL original. -/
theorem sizeDecsStcnamesCompileDecsStructsCore {width : Nat} {σ : Type} [NeZero width] :
    ∀ (pan_code : List (DeclHOL width)) (s : PanSemStateFiniteExact width σ)
      (h : DecidablePred s.memaddrs) (ctxt : Pancake.PanStructs.CompileShapeExact.ContextExact)
      (s' : PanSemStateFiniteExact width σ) (code' : List (DeclHOL width))
      (ctxt' : Pancake.PanStructs.CompileShapeExact.ContextExact),
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ s h pan_code = some s' →
      Pancake.PanStructs.CompileShapeExact.compileDeclsExact ctxt pan_code = (code', ctxt') →
      Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact s.structs →
      (∀ nm v, s.globals.lookup nm = some v → isWfShapeValueHOLExact s.structs v = true) →
      ctxt.structs = s.structs.map (fun entry => (entry.1, entry.2.fields)) →
      (decShapesHOL code').map sizeOfShapeHOL =
        (decShapesHOL pan_code).map (sizeOfShapeWithContextHOL s.structs)
  | [], s, h, ctxt, s', code', ctxt', _, hcomp, _, _, _ => by
      simp only [Pancake.PanStructs.CompileShapeExact.compileDeclsExact, Prod.mk.injEq] at hcomp
      obtain ⟨rfl, -⟩ := hcomp
      rfl
  | .name nm fields :: ds, s, h, ctxt, s', code', ctxt', hev, hcomp, hok, hglob, hctxt => by
      simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hev
      simp only [Pancake.PanStructs.CompileShapeExact.compileDeclsExact] at hcomp
      simp only [decShapesHOL]
      exact sizeDecsStcnamesCompileDecsStructsCore ds s h ctxt s' code' ctxt' hev hcomp hok hglob hctxt
  | .function f :: ds, s, h, ctxt, s', code', ctxt', hev, hcomp, hok, hglob, hctxt => by
      simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hev
      split at hev
      · rcases hc : Pancake.PanStructs.CompileShapeExact.compileDeclsExact ctxt ds with ⟨c2, x2⟩
        simp only [Pancake.PanStructs.CompileShapeExact.compileDeclsExact, hc, Prod.mk.injEq] at hcomp
        obtain ⟨rfl, -⟩ := hcomp
        simp only [decShapesHOL]
        exact sizeDecsStcnamesCompileDecsStructsCore ds { s with code := s.code.update (f.name, (f.params, f.body, f.returnShape)) } h ctxt s' c2 x2 hev hc hok hglob hctxt
      · exact absurd hev (by simp)
  | .exnDecl en sh :: ds, s, h, ctxt, s', code', ctxt', hev, hcomp, hok, hglob, hctxt => by
      simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hev
      split at hev
      · rcases hc : Pancake.PanStructs.CompileShapeExact.compileDeclsExact ctxt ds with ⟨c2, x2⟩
        simp only [Pancake.PanStructs.CompileShapeExact.compileDeclsExact, hc, Prod.mk.injEq] at hcomp
        obtain ⟨rfl, -⟩ := hcomp
        simp only [decShapesHOL]
        exact sizeDecsStcnamesCompileDecsStructsCore ds { s with eshapes := s.eshapes.update (en, sh) } h ctxt s' c2 x2 hev hc hok hglob hctxt
      · exact absurd hev (by simp)
  | .decl sh v e :: ds, s, h, ctxt, s', code', ctxt', hev, hcomp, hok, hglob, hctxt => by
      simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hev
      cases he : @PanSemStateFiniteExact.evalHOLFinite width σ _ (PanSemStateFiniteExact.emptyLocalsHOLFinite s) h e with
      | none => rw [he] at hev; exact absurd hev (by simp)
      | some value =>
        rw [he] at hev
        simp only at hev
        split at hev
        · rename_i hs
          have hvwf : isWfShapeValueHOLExact s.structs value = true :=
            @evalHOLExact_isWfShapeValueHOLExact _ _ _ (PanSemStateFiniteExact.emptyLocalsHOLFinite s).toExact h
              (fun _ _ hl => by simp [PanSemStateFiniteExact.emptyLocalsHOLFinite] at hl) hglob e value he
          have hsh : sh = shapeOfHOLExact value := (shapeEqHOL_eq_true _ _).mp hs
          have hshwf : isWfShapeExactHOL s.structs sh = true := by
            rw [hsh]; exact isWfShapeValueHOLExact_shapeOfHOLExact _ value hvwf
          rcases hc : Pancake.PanStructs.CompileShapeExact.compileDeclsExact
              { ctxt with globals := (v, sh) :: ctxt.globals } ds with ⟨c2, x2⟩
          simp only [Pancake.PanStructs.CompileShapeExact.compileDeclsExact, hc,
            Prod.mk.injEq] at hcomp
          obtain ⟨rfl, -⟩ := hcomp
          simp only [decShapesHOL, List.map_cons]
          congr 1
          · exact Pancake.PanStructs.CompileShapeExact.sizeOfShapeCompilePassEq s sh ctxt.structs
              ⟨hok, hshwf, hctxt⟩
          · refine sizeDecsStcnamesCompileDecsStructsCore ds (PanSemStateFiniteExact.setGlobalHOLFinite v value s) h _ s'
              c2 x2 hev hc hok ?_ hctxt
            intro nm w hw
            simp only [PanSemStateFiniteExact.setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at hw
            split at hw
            · cases hw; exact hvwf
            · exact hglob nm w hw
        · exact absurd hev (by simp)

/-- Exact HOL `size_decs_stcnames_compile_decs_structs`
(`pan_to_wordProofScript.sml:460-486`). `FEVERY` over `s.globals` is the
pointwise statement on the canonical lookups; `evaluate_decls`' memory-domain
decider is chosen classically, as in the tagged `semantics_decls`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "size_decs_stcnames_compile_decs_structs"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem sizeDecsStcnamesCompileDecsStructsHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s : PanSemStateFiniteExact width σ) (pan_code : List (DeclHOL width))
      (ctxt : Pancake.PanStructs.CompileShapeExact.ContextExact)
      (s' : PanSemStateFiniteExact width σ) (code' : List (DeclHOL width))
      (ctxt' : Pancake.PanStructs.CompileShapeExact.ContextExact),
      (open Classical in PanSemStateFiniteExact.evaluateDeclsHOLFinite s pan_code) = some s' ∧
        Pancake.PanStructs.CompileShapeExact.compileDeclsExact ctxt pan_code = (code', ctxt') ∧
        Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact s.structs ∧
        (∀ nm v, s.globals.lookup nm = some v → isWfShapeValueHOLExact s.structs v = true) ∧
        ctxt.structs = s.structs.map (fun entry => (entry.1, entry.2.fields)) →
      (decShapesHOL code').map sizeOfShapeHOL =
        (decShapesHOL pan_code).map (sizeOfShapeWithContextHOL s.structs) := by
  rintro s pan_code ctxt s' code' ctxt' ⟨hev, hcomp, hok, hglob, hctxt⟩
  exact sizeDecsStcnamesCompileDecsStructsCore pan_code s _ ctxt s' code' ctxt' hev hcomp hok
    hglob hctxt

/-- Exact HOL `semantics_size_decs_stcnames_compile_structs`
(`pan_to_wordProofScript.sml:488-504`). `THE` is the reviewed `holThe`; the
free `s`, `nm` and `pan_code` are bound explicitly. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "semantics_size_decs_stcnames_compile_structs"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem semanticsSizeDecsStcnamesCompileStructsHOL {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (nm : MlS) (pan_code : List (DeclHOL width)) :
    PanSemStateFiniteExact.semanticsDecls s nm pan_code ≠ .fail ∧
      s.globals = HolFiniteMapExact.empty →
    (decShapesHOL (Pancake.PanStructs.CompileShapeExact.compileTopExact pan_code)).map
        sizeOfShapeHOL =
      (decShapesHOL pan_code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact (width := width) [] pan_code))) := by
  classical
  rintro ⟨hsem, hglob⟩
  unfold PanSemStateFiniteExact.semanticsDecls at hsem
  cases hst : decsStcnamesHOLExact (width := width) [] pan_code with
  | none => simp [hst] at hsem
  | some st =>
    simp only [hst] at hsem
    cases hev : PanSemStateFiniteExact.evaluateDeclsHOLFinite { s with structs := st } pan_code with
    | none => simp [hev] at hsem
    | some s' =>
      have hok0 : Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact
          ([] : StructContextExact) := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
      have hok := Pancake.PanStructs.CompileShapeExact.decsStcnamesInfosOk [] pan_code st ()
        ⟨hst, hok0⟩
      have hnames := Pancake.PanStructs.CompileShapeExact.decsStcnamesToGetNames [] pan_code st
        { structs := [], locals := [], globals := [] } ⟨hst, rfl⟩
      simp only [holThe]
      unfold Pancake.PanStructs.CompileShapeExact.compileTopExact
      dsimp only
      rw [hnames]
      rcases hc : Pancake.PanStructs.CompileShapeExact.compileDeclsExact
          { structs := st.map (fun entry => (entry.1, entry.2.fields)), locals := [],
            globals := [] } pan_code with ⟨c2, x2⟩
      exact sizeDecsStcnamesCompileDecsStructsCore pan_code { s with structs := st } _ _ s' c2 x2
        hev hc hok (fun n v hv => by simp [hglob] at hv) rfl

end Flapjack
