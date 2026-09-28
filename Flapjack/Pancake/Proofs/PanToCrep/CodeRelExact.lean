import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
Exact-carrier code relation for the HOL Pancake-to-Crep correctness boundary.
This lives below the counterpart proof module because it complements
`codeRelW` without changing that production-carrier relation.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-! Exact source review of HOL `code_rel_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:32-43`). HOL's three
    explicit arguments are `ctxt`, `s_code`, and `t_code`; inside the relation
    it universally quantifies `f`, `vshs`, `prog`, and `rsh` in that order.
    This definition preserves that binder structure and each clause:

    * a successful source `FLOOKUP` requires `localised_prog prog`;
    * `ctxt.funcs` must map `f` to the same `(vshs, rsh)`;
    * `vs` and `shs` are `MAP FST`/`MAP SND` of `vshs`, and `ns` is
      `GENLIST I (size_of_shape (Comb shs))`;
    * `nctxt` is exactly `ctxt_fc ctxt.funcs ctxt.eids vs shs ns`;
    * target lookup must return `(ns, compile nctxt prog)`.

    The carrier comparison is constructor-for-constructor: HOL `mlstring` is
    `MlS`, HOL `shape`/`prog`/`crepLang$prog` are `ShapeHOL`/`ProgHOL`/
    `CrepProgHOL`, and HOL's word type is the positive-width `BitVec width`.
    HOL finite-map parameters `s_code` and `t_code` use the canonical
    `HolFiniteMapExact` carrier, recorded as bare entries in
    `fmap_as_finite_support_relation`; the context's `funcs` and `eids` fields
    use the same representation and are named with their owner. No binder is
    bundled, no raw function map admits infinite support, and no key or
    executable behavior is changed. The canonical context roundtrip witness
    below validates that carrier field translation.

    This is an exact port of the HOL definition, not a theorem establishing
    `pc_compile_correct` and not evidence that the production String-backed
    compiler path uses this exact carrier. That executable-path replacement
    remains tracked on the parent correctness bead.

    The combined `(fmap_as_finite_support_relation := [...])` +
    `(words_as_type_indexed_bitvec)` qualifiers are attached: the relation
    traverses the finite-map fields named above, and HOL's type-indexed
    `'a word` (context exception codes, `ProgHOL width`) is rendered by the
    positive-width `BitVec width` carrier of the named structures, so the
    combined reviewed status
    `reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec`
    records the whole representation translation (bead flapjack-ikjm.4).
-/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_def"
  (fmap_as_finite_support_relation := [sourceCode, targetCode,
    PanToCrepContextExact.funcs, PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
def codeRelExactHOLW {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceCode : HolFiniteMapExact MlS
      (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (targetCode : HolFiniteMapExact MlS (List Nat × CrepProgHOL width)) : Prop :=
  ∀ function variableShapes program returnShape,
    sourceCode.lookup function = some (variableShapes, program, returnShape) →
      localisedProgHOL program = true ∧
      context.funcs.lookup function = some (variableShapes, returnShape) ∧
      let variables := variableShapes.map Prod.fst
      let shapes := variableShapes.map Prod.snd
      let names := List.range (sizeOfShapeHOL (.comb shapes))
      let nextContext := ctxtFcExactHOL context.funcs context.eids variables shapes names
      targetCode.lookup function = some
        (names, compileProgExactHOLW nextContext program)

/-- Flapjack finite-map bridge (no HOL declaration): `alistToFmap` is the
    right-fold form of HOL `alist_to_fmap`, so lookup observes the first source
    occurrence just like `List.lookup`. -/
private theorem flookup_alistToFmap_eq_lookup {α β : Type}
    [BEq α] [LawfulBEq α] (entries : List (α × β)) (key : α) :
    Flapjack.FLOOKUP (Flapjack.alistToFmap entries) key = List.lookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨entryKey, entryValue⟩ := entry
      by_cases h : entryKey = key
      · subst entryKey
        simp [Flapjack.alistToFmap, List.lookup, Flapjack.FLOOKUP_update]
      · have h₁ : (entryKey == key) = false := beq_eq_false_iff_ne.mpr h
        have h₂ : (key == entryKey) = false :=
          beq_eq_false_iff_ne.mpr (fun he => h he.symm)
        change Flapjack.FLOOKUP
          (Flapjack.FUPDATE (Flapjack.alistToFmap entries)
            (entryKey, entryValue)) key = _
        rw [Flapjack.FLOOKUP_update]
        simp only [h₁, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, h₂]
        simpa [Flapjack.alistToFmap] using ih

/-- Exact body-compiler bridge for the per-entry context built by HOL
    `ctxt_fc`. The exact `make_vmap` and `crep_vars` definitions construct the
    same map, and `MAX_LIST (GENLIST I n) = n - 1`. Flapjack bridge theorem; it
    has no separate HOL declaration. -/
private theorem compFuncExactHOLW_ctxtFcExactHOL {width : Nat} [NeZero width]
    (fs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (eids : HolFiniteMapExact MlS (BitVec width))
    (params : List (MlS × ShapeHOL)) (program : ProgHOL width) :
    compFuncExactHOLW fs eids params program =
      compileProgExactHOLW
        (ctxtFcExactHOL fs eids (params.map Prod.fst) (params.map Prod.snd)
          (crepVarsHOL params)) program := by
  have hcontext :
      mkCtxtExactHOL (panToCrepMakeVmapHOLExact params) fs
          (sizeOfShapeHOL (.comb (params.map Prod.snd)) - 1) eids =
        ctxtFcExactHOL fs eids (params.map Prod.fst) (params.map Prod.snd)
          (crepVarsHOL params) := by
    simp [mkCtxtExactHOL, ctxtFcExactHOL, panToCrepMakeVmapHOLExact,
      crepVarsHOL, maxList_range, List.zip]
  change compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact params) fs
        (sizeOfShapeHOL (.comb (params.map Prod.snd)) - 1) eids) program = _
  rw [hcontext]

/-- Exact-carrier HOL `mk_ctxt_code_imp_code_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4604-4616`).  The
    declaration list is projected by exact `functionsHOL`; source and target
    code tables are the HOL `alist_to_fmap` construction represented by
    `HolFiniteMapExact.updateList` over the reversed function/compiled lists.
    The exact initial compiler context uses the tagged `make_funcs`,
    `get_eids_from_decls`, `compile_to_crep`, and `compile` definitions.  The
    two HOL premises remain all-distinct function names and localization of
    every function body. The context's traversed `funcs`/`eids` fields use the
    canonical `HolFiniteMapExact` carrier with the same-module context
    roundtrip witness; the constructed source/target code maps preserve HOL
    `alist_to_fmap` first-occurrence lookup by reversing before `updateList`.
    `MlS`, `ShapeHOL`, `ProgHOL`, and `CrepProgHOL` match HOL's `mlstring`,
    `shape`, `panLang$prog`, and `crepLang$prog`; positive-width `BitVec`
    records HOL's type-indexed word. These are the exact map/word
    representation qualifications below, with no extra premises or carrier
    narrowing. The direct `code_rel_generated_initial` EVAL expansion and its
    original HOL theorem discharge `code_rel_generated_initial_proved` are in
    `scripts/hol-probes/code_rel_probe.out`; the corresponding exact-carrier
    regression is in `Flapjack.Test.PanToCrepCodeRelParity`. This theorem uses
    the tagged exact `compileToCrepExactHOLW`/`compileProgExactHOLW` definitions
    and the same per-entry `compile` body as HOL `compile_def`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml"
  "mk_ctxt_code_imp_code_rel" 4604
  (fmap_as_finite_support_relation :=
    [PanToCrepContextExact.funcs, PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem mkCtxtCodeImpCodeRelExactHOLW {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width))
    (_hdistinct : (functionsHOL declarations).map Prod.fst |>.Nodup)
    (hlocalised : ∀ entry ∈ functionsHOL declarations,
      localisedProgHOL entry.2.2.1 = true) :
    codeRelExactHOLW
      (mkCtxtExactHOL HolFiniteMapExact.empty
        (makeFuncsExactHOL (functionsHOL declarations)) 0
        (getEidsFromDeclsHOL declarations))
      (HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse)
      (HolFiniteMapExact.empty.updateList
        (compileToCrepExactHOLW declarations).reverse) := by
  intro function variableShapes program returnShape hsource
  change Flapjack.FLOOKUP
      (Flapjack.FUPDATE_LIST Flapjack.FEMPTY
        (functionsHOL declarations).reverse) function =
    some (variableShapes, program, returnShape) at hsource
  rw [Flapjack.FLOOKUP_FUPDATE_LIST_reverse_eq_lookup] at hsource
  have hmem : (function, (variableShapes, (program, returnShape))) ∈
      functionsHOL declarations := by
    obtain ⟨before, after, hsplit, _hfirst⟩ :=
      List.lookup_eq_some_iff.mp hsource
    rw [hsplit]
    simp
  have hbody : localisedProgHOL program = true := hlocalised _ hmem
  refine ⟨hbody, ?_, ?_⟩
  · change Flapjack.FLOOKUP
      (Flapjack.alistToFmap (makeFuncsEntriesHOL (functionsHOL declarations)))
      function = some (variableShapes, returnShape)
    change Flapjack.FLOOKUP
      (Flapjack.alistToFmap
        ((functionsHOL declarations).map fun entry =>
          (entry.1, (entry.2.1, entry.2.2.2)))) function = _
    rw [flookup_alistToFmap_eq_lookup,
      lookup_map_preserveFst
        (project := fun value : List (MlS × ShapeHOL) ×
          (Flapjack.Pancake.PanLang.ProgHOL width × ShapeHOL) =>
            (value.1, value.2.2))]
    rw [hsource]
    rfl
  · simp only [HolFiniteMapExact.lookup_updateList]
    change Flapjack.FLOOKUP
      (Flapjack.FUPDATE_LIST Flapjack.FEMPTY
        (compileToCrepExactHOLW declarations).reverse) function = _
    rw [Flapjack.FLOOKUP_FUPDATE_LIST_reverse_eq_lookup]
    simp only [compileToCrepExactHOLW]
    rw [lookup_map_preserveFst
      (functions := functionsHOL declarations)
      (project := fun entry : List (MlS × ShapeHOL) ×
        (ProgHOL width × ShapeHOL) =>
          (crepVarsHOL entry.1,
            compFuncExactHOLW (makeFuncsExactHOL (functionsHOL declarations))
              (getEidsFromDeclsHOL declarations) entry.1 entry.2.1))]
    rw [hsource]
    simp only [Option.map_some]
    rw [compFuncExactHOLW_ctxtFcExactHOL]
    rfl

/-- Exact port of HOL `code_rel_imp`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:81-91`):
    `code_rel ctxt s_code t_code ==>` then for all `f`, `vshs`, `prog`, `rsh`,
    `FLOOKUP s_code f = SOME (vshs, prog, rsh)` implies `localised_prog prog`
    and `FLOOKUP ctxt.funcs f = SOME (vshs, rsh)` and, with
    `vs = MAP FST vshs`, `shs = MAP SND vshs`,
    `ns = GENLIST I (size_of_shape (Comb shs))`,
    `nctxt = ctxt_fc ctxt.funcs ctxt.eids vs shs ns`,
    `FLOOKUP t_code f = SOME (ns, compile nctxt prog)`.

    The Lean statement keeps HOL's outer `code_rel` hypothesis and the
    per-entry conclusion over the exact `codeRelExactHOLW` relation, clause for
    clause: source lookup yields `localisedProgHOL`, `context.funcs` returns the
    same `(vshs, rsh)`, and the target lookup returns the compiled program under
    `ctxtFcExactHOL`. The carriers are `MlS` = `mlstring`, `ShapeHOL` = `shape`,
    `ProgHOL width` = `'a panLang$prog`, `CrepProgHOL width` = `'a crepLang$prog`,
    and the positive-width `BitVec width` = HOL `'a word`. The proof is the
    definitional unfolding of `codeRelExactHOLW` (HOL's
    `fs [code_rel_def] >> metis_tac[]`). The relation qualifier records the two
    standalone `HolFiniteMapExact` parameters `sourceCode`/`targetCode` and the
    traversed `PanToCrepContextExact.funcs`/`eids` owner fields, matching the
    imported `code_rel_def` tag; the same-module checked witness
    `holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact` validates the
    context carrier. This tags only the exact proof-side relation, not the
    production `codeRel`/`codeRelW`, which remain on the parent bead.

    The combined `(fmap_as_finite_support_relation := [...])` +
    `(words_as_type_indexed_bitvec)` qualifiers are attached, matching the
    imported `code_rel_def` tag (bead flapjack-ikjm.4). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_imp"
  (fmap_as_finite_support_relation := [sourceCode, targetCode,
    PanToCrepContextExact.funcs, PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem codeRelExactHOLW_imp {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceCode : HolFiniteMapExact MlS
      (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (targetCode : HolFiniteMapExact MlS (List Nat × CrepProgHOL width)) :
    codeRelExactHOLW context sourceCode targetCode →
    ∀ function variableShapes program returnShape,
      sourceCode.lookup function = some (variableShapes, program, returnShape) →
        localisedProgHOL program = true ∧
        context.funcs.lookup function = some (variableShapes, returnShape) ∧
        let variables := variableShapes.map Prod.fst
        let shapes := variableShapes.map Prod.snd
        let names := List.range (sizeOfShapeHOL (.comb shapes))
        let nextContext := ctxtFcExactHOL context.funcs context.eids variables shapes names
        targetCode.lookup function = some
          (names, compileProgExactHOLW nextContext program) := by
  intro hcodeRel
  simpa only [codeRelExactHOLW] using hcodeRel

/-- Same-module finite-map relation witness for the imported exact context
    fields named by `codeRelExactHOLW`'s qualifier. Flapjack representation
    infrastructure only; the parameter maps are validated directly at their
    `HolFiniteMapExact` binders, so they need no owner witness. -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context := by
  exact PanToCrepContextExact.holFmapAsFiniteSupportWitness context

/-- Same-module finite-map relation witness for the `PanSemStateFiniteExact`
    carrier, whose `code` field is traversed by the tagged
    `codeRelExactHOLW_emptyLocals` port. It forwards the canonical
    `toExact`/`ofExact` roundtrip of the finite-support carrier with its broad
    `PanSemStateExact` counterpart. Flapjack representation infrastructure only;
    it is not a port of a HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module finite-map relation witness for the `CrepSemHOLState` carrier,
    whose `code` field is traversed by the tagged
    `codeRelExactHOLW_emptyLocals` port. It forwards the canonical
    `toBroad`/`ofBroad` roundtrip of the finite-support carrier with its broad
    `CrepSemBroadState` counterpart. Flapjack representation infrastructure only;
    it is not a port of a HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

/-- Exact port of HOL `code_rel_empty_locals`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:96-100`):
    `code_rel ctxt s.code t.code ==>
       code_rel ctxt (empty_locals s).code (empty_locals t).code`.

    HOL clears only the source and target `locals` fields, so the `code` fields
    consumed by `code_rel` are unchanged. The Lean statement keeps HOL's context
    and both state binders over the exact `PanToCrepContextExact`,
    `PanSemStateFiniteExact`, and `CrepSemHOLState` carriers, and applies the
    tagged exact `emptyLocalsHOLFinite` / `CrepSemHOLState.emptyLocals` state
    updates. The relation is the exact `codeRelExactHOLW` port. The only
    representation translation is the canonical finite-support form of the two
    traversed `code` fields, recorded by the multi-carrier qualifier; the
    context's own finite-map fields are already recorded on the tagged
    `codeRelExactHOLW` relation. `empty_locals` is definitionally the identity
    on `code`, so the proof is HOL's
    `rw [code_rel_def, empty_locals_def, panSemTheory.empty_locals_def] >>
    metis_tac[]`. This tags only the exact proof-side theorem, not the
    production `codeRel`/`codeRelW` carriers.

    The combined `(fmap_as_finite_support_relation := [...])` +
    `(words_as_type_indexed_bitvec)` qualifiers are attached; see the schema
    note on `codeRelExactHOLW` above (bead flapjack-ikjm.4). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_empty_locals"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.code, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem codeRelExactHOLW_emptyLocals {width : Nat} [NeZero width] {σ : Type}
    (context : PanToCrepContextExact width)
    (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ) :
    codeRelExactHOLW context source.code target.code →
      codeRelExactHOLW context (source.emptyLocalsHOLFinite).code
        (CrepSemHOLState.emptyLocals target).code := by
  intro hrel
  simpa only [PanSemStateFiniteExact.emptyLocalsHOLFinite,
    CrepSemHOLState.emptyLocals] using hrel

end Flapjack
