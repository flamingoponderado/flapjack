import Flapjack.Pancake.CrepInline.Pass

/-!
# `inline_prog` recursive core over the canonical `HolFiniteMapExact`

FLAPJACK-SPECIFIC (not a tagged HOL port, so no `@[hol]` annotation): this
module carries the recursive core of HOL `inline_prog`
(`cakeml/pancake/crep_inlineScript.sml:203-257`) over the reviewed canonical
finite-support carrier while the carrier review is still pending (bead
`flapjack-e7w.2.1.13`, child of `flapjack-e7w.2.1`; blocks
`flapjack-e7w.2.2` exact `compile_inl_prog`/`compile_inl_top` wrappers and
`flapjack-4ac.2.20.2` `compile_prog_def`).

This is the port of HOL `inline_prog`
(`cakeml/pancake/crep_inlineScript.sml:203-257`) over the reviewed canonical
finite-support carrier
`Flapjack.HolFiniteMapExact` (`Flapjack/Pancake/Semantics/CrepSem/HOLState.lean:34`)
rather than the untagged unique-key list model `CrepInlineFmapHOL`
(`Flapjack/Pancake/CrepInline/Pass.lean:495`).

The core `inlineProgHOLCoreExact` reproduces the clause structure of
`inlineProgHOLCore` (`Pass.lean:827`) and of the HOL source equation by
equation, swapping only the carrier: `FLOOKUP` becomes `fs.lookup` and
domain subtraction `inlineable_fs \\ e` becomes `fs.erase name`.

**Termination.** `HolFiniteMapExact` stores its finite support as an
*existential* `∃ keys, ∀ key, lookup key ≠ none → key ∈ keys` (HOLState.lean:36)
and therefore exposes no canonical cardinality (its witness list may contain
duplicates and unused keys).  Following the source statement of the task we
prove `erase` strictly decreases an explicit finite-support cardinality: the
core carries the support list `supportKeys`, valid by `support_spec`, and
recurses with `supportKeys.filter (fun k => k != name)` after `fs.erase name`.
`HolFiniteMapExact.erase_support` shows that filtered list still covers the
eraser's domain, and `erase_support_length_lt` shows its length strictly
decreases when the erased key is present.  The measure
`(supportKeys.length, sizeOf program)` is thus the concrete analogue of HOL's
`(CARD (FDOM fs), prog_size program)`; `supportKeys.length` is the `CARD (FDOM
fs)` certificate.  `inlineProgHOLExact` discharges the certificate from the
carrier's own `finiteSupport` via `Classical.choose`.

Nothing in this file carries an `@[hol]` attribute: the carrier review is not
yet complete, and the recursive helper cross-system correspondence to HOL is
still open.  This is deliberately untagged infrastructure for the exact
carrier port (`flapjack-e7w.2.1.13`).
-/

namespace Flapjack

namespace CrepInlineCanonical

variable {α : Type} {β : Type} {width : Nat} [NeZero width]

open Flapjack.Basis.Pure.MlString

/-! ## Finite-support cardinality certificate -/

/-- HDL `erase_support` support lemma: filtering the erased key out of a support
    list for `fs` yields a support list for `fs.erase name`.  The eraser's
    lookup is `FDOMSUB fs.lookup name`, so every defined key is a key of `fs`
    (hence was in `keys`) and is different from `name`. -/
theorem HolFiniteMapExact.erase_support [BEq α] [LawfulBEq α]
    (fs : HolFiniteMapExact α β) (keys : List α)
    (hkeys : ∀ k, fs.lookup k ≠ none → k ∈ keys) (name : α) :
    ∀ k, (fs.erase name).lookup k ≠ none →
      k ∈ keys.filter (fun k => k != name) := by
  intro k hk
  have hkfs : fs.lookup k ≠ none := by
    intro hnone
    apply hk
    simp only [HolFiniteMapExact.lookup_erase]
    unfold FDOMSUB
    by_cases h : name == k
    · simp [h]
    · simp [h, hnone]
  have hne : k ≠ name := by
    intro heq
    subst heq
    apply hk
    simp [FDOMSUB]
  exact List.mem_filter.mpr
    ⟨hkeys k hkfs, by rw [bne_iff_ne]; exact hne⟩

/-- Erasing a present key strictly decreases the length of the explicit
    finite-support certificate.  This is the finite-support analogue of HOL's
    `CARD (FDOM fs)` decrease in the `inline_prog` termination proof. -/
theorem erase_support_length_lt [BEq α] [LawfulBEq α]
    (fs : HolFiniteMapExact α β) (keys : List α)
    (hkeys : ∀ k, fs.lookup k ≠ none → k ∈ keys) (name : α)
    (hname : fs.lookup name ≠ none) :
    (keys.filter (fun k => k != name)).length < keys.length :=
  List.length_filter_lt_length_iff_exists.mpr
    ⟨name, hkeys name hname, by simp⟩

/-! ## The recursive core -/

/-- Recursive core of HOL `inline_prog` over the canonical
    `HolFiniteMapExact` inline map.  `inlineable` is the map, `supportKeys`
    together with `support_spec` is the finite-support cardinality certificate
    used only for termination.  Every clause mirrors `inlineProgHOLCore`
    (`Pass.lean:827`) and the HOL equations at
    `crep_inlineScript.sml:203-257`, with `fs.lookup` for `FLOOKUP` and
    `fs.erase name` for `inlineable_fs \\ e`. -/
def inlineProgHOLCoreExact [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys) :
    CrepProgHOL width → CrepProgHOL width
  | .call none name arguments =>
      match _hlookup : inlineable.lookup name with
      | none => .call none name arguments
      | some (argumentNames, body) =>
          let inlinedCallee :=
            (unreachElimHOLExact
              (inlineProgHOLCoreExact (inlineable.erase name)
                (supportKeys.filter (fun k => k != name))
                (HolFiniteMapExact.erase_support inlineable supportKeys support_spec name)
                body)).1
          let maxArguments := (arguments.flatMap crepExpVarsHOL).foldl max 0
          let maxArgumentNames := argumentNames.foldl max 0
          let temporaryNames :=
            genlistSuccAddHOLExact (max maxArguments maxArgumentNames)
              argumentNames.length
          inlineTailHOLExact
            (argLoadHOLExact temporaryNames arguments argumentNames inlinedCallee)
  | .call (some (returnNames, none)) name arguments =>
      if !crepAllDistinct returnNames then
        .call (some (returnNames, none)) name arguments
      else
        match _hlookup : inlineable.lookup name with
        | none => .call (some (returnNames, none)) name arguments
        | some (argumentNames, body) =>
            let inlinedCallee :=
              (unreachElimHOLExact
                (inlineProgHOLCoreExact (inlineable.erase name)
                  (supportKeys.filter (fun k => k != name))
                  (HolFiniteMapExact.erase_support inlineable supportKeys support_spec name)
                  body)).1
            let maxArguments := (arguments.flatMap crepExpVarsHOL).foldl max 0
            let maxArgumentNames := argumentNames.foldl max 0
            let temporaryNames :=
              genlistSuccAddHOLExact (max maxArguments maxArgumentNames)
                argumentNames.length
            let maxReturnNames := returnNames.foldl max 0
            let maxInlinedCallee := crepVmaxProgHOLExact inlinedCallee
            let maxTemporaryNames := temporaryNames.foldl max 0
            let temporaryReturns :=
              genlistSuccAddHOLExact
                (max maxReturnNames (max maxInlinedCallee maxTemporaryNames))
                returnNames.length
            let transformedCallee :=
              if notBranchRetHOLExact inlinedCallee then
                .seq .tick (transformEocHOLExact temporaryReturns inlinedCallee)
              else
                .while (.const 1)
                  (transformBranchHOLExact 0 temporaryReturns inlinedCallee)
            inlineNontailHOLExact transformedCallee returnNames
              temporaryReturns temporaryNames arguments argumentNames
  | .call (some (returnNames, some (handler, body))) name arguments =>
      .call (some (returnNames, some (handler,
        inlineProgHOLCoreExact inlineable supportKeys support_spec body))) name arguments
  | .dec name value body =>
      .dec name value (inlineProgHOLCoreExact inlineable supportKeys support_spec body)
  | .seq first second =>
      .seq (inlineProgHOLCoreExact inlineable supportKeys support_spec first)
        (inlineProgHOLCoreExact inlineable supportKeys support_spec second)
  | .ite condition first second =>
      .ite condition
        (inlineProgHOLCoreExact inlineable supportKeys support_spec first)
        (inlineProgHOLCoreExact inlineable supportKeys support_spec second)
  | .while condition body =>
      .while condition (inlineProgHOLCoreExact inlineable supportKeys support_spec body)
  | program => program
termination_by program => (supportKeys.length, sizeOf program)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right; simp_wf; decreasing_trivial
    | apply Prod.Lex.left
      exact erase_support_length_lt inlineable supportKeys support_spec name
        (by simp [_hlookup])

/-! ## Clause equations

These state the defining equations of `inlineProgHOLCoreExact` on each
constructor, in the clause order of HOL `inline_prog_def`
(`crep_inlineScript.sml:203-249`).  They are kernel-checked facts about the
Lean core itself; they carry no `@[hol]` tag because the carrier review is
incomplete. -/

theorem inlineProgHOLCoreExact_skip [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec .skip = .skip := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_dec [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.dec name value body) =
      .dec name value
        (inlineProgHOLCoreExact inlineable supportKeys support_spec body) := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_seq [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (first second : CrepProgHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.seq first second) =
      .seq (inlineProgHOLCoreExact inlineable supportKeys support_spec first)
        (inlineProgHOLCoreExact inlineable supportKeys support_spec second) := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_ite [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (condition : CrepExpHOL width) (thenBranch elseBranch : CrepProgHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec
        (.ite condition thenBranch elseBranch) =
      .ite condition
        (inlineProgHOLCoreExact inlineable supportKeys support_spec thenBranch)
        (inlineProgHOLCoreExact inlineable supportKeys support_spec elseBranch) := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_while [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (condition : CrepExpHOL width) (body : CrepProgHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.while condition body) =
      .while condition
        (inlineProgHOLCoreExact inlineable supportKeys support_spec body) := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_call_handler [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (returnNames : List Nat) (handler : BitVec width) (body : CrepProgHOL width)
    (name : CrepInlineMapHOLName) (arguments : List (CrepExpHOL width)) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec
        (.call (some (returnNames, some (handler, body))) name arguments) =
      .call (some (returnNames, some (handler,
        inlineProgHOLCoreExact inlineable supportKeys support_spec body)))
        name arguments := by
  simp only [inlineProgHOLCoreExact]

/-- The `fs`-only entry point: the same recursive core with its finite-support
    certificate discharged from `HolFiniteMapExact.finiteSupport`.  This is
    noncomputable because the support witness is extracted classically; the
    returned `CrepProgHOL` does not depend on the certificate. -/
noncomputable def inlineProgHOLExact [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width)) :
    CrepProgHOL width → CrepProgHOL width :=
  inlineProgHOLCoreExact inlineable
    (Classical.choose inlineable.finiteSupport)
    (Classical.choose_spec inlineable.finiteSupport)

/-- The finite key list `domainKeys` of the unique-key list model is a valid
    certificate for the canonical `HolFiniteMapExact` view, so the exact
    recursive core can be run on `crepInlineMapHOL ... .toHolFiniteMapExact`
    without any extra hypothesis. -/
theorem domainKeys_spec [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (fs : CrepInlineFmapHOL width) :
    ∀ key, fs.toHolFiniteMapExact.lookup key ≠ none → key ∈ fs.domainKeys := by
  intro key h
  rw [CrepInlineFmapHOL.lookup_toHolFiniteMapExact] at h
  rw [CrepInlineFmapHOL.mem_domainKeys_iff_lookup]
  exact h

/-- Regression against the handler row of
    `scripts/hol-probes/crep_inline_code_inl_probe.out`: the canonical-carrier
    core keeps the handler arm untouched apart from recursing into its body,
    exactly as the list-model core and HOL `inline_prog` do. -/
theorem inlineProgHOLCoreExact_handler_example [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (fs : CrepInlineFmapHOL 8)
    (returnNames : List Nat) (handler : BitVec 8) (body : CrepProgHOL 8)
    (name : CrepInlineMapHOLName) (arguments : List (CrepExpHOL 8)) :
    inlineProgHOLCoreExact fs.toHolFiniteMapExact fs.domainKeys
        (domainKeys_spec fs)
        (.call (some (returnNames, some (handler, body))) name arguments) =
      .call (some (returnNames, some (handler,
        inlineProgHOLCoreExact fs.toHolFiniteMapExact fs.domainKeys
          (domainKeys_spec fs) body))) name arguments :=
  inlineProgHOLCoreExact_call_handler _ _ _ _ _ _ _ _

/-- Regression against the structural (non-call) rows: the canonical-carrier
    core maps `dec`/`seq` structurally, and irreducible atoms are left alone. -/
theorem inlineProgHOLCoreExact_structural_example [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName] (fs : CrepInlineFmapHOL 8) :
    inlineProgHOLCoreExact fs.toHolFiniteMapExact fs.domainKeys
        (domainKeys_spec fs)
        (.dec 1 (.const 2) (.seq .skip .skip) : CrepProgHOL 8) =
      .dec 1 (.const 2) (.seq .skip .skip) := by
  rw [inlineProgHOLCoreExact_dec, inlineProgHOLCoreExact_seq,
    inlineProgHOLCoreExact_skip]

/-! ### Exact `compile_inl_prog` / `compile_inl_top` wrappers

Untagged Flapjack-specific ports of HOL `compile_inl_prog_def` and
`compile_inl_top_def` (`cakeml/pancake/crep_inlineScript.sml:259,264`) over the
exact carriers: `mlstring` function names (`CrepInlineMapHOLName`), the
canonical finite-support inline map (`HolFiniteMapExact`), and `CrepProgHOL`
triple lists. No `@[hol]` tag is attached pending coordinator carrier review
(bead `flapjack-e7w.2.2`). -/

/-- Exact analogue of HOL `alist_to_fmap` (`alistScript.sml:21`), which is
    `FOLDR (fun (k,v) f => f |+ (k,v)) FEMPTY s`; equivalently `FUPDATE_LIST`
    applied right-to-left, so the FIRST occurrence of a key wins. -/
def alistToFmapHOLExact [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width))) :
    HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width) :=
  HolFiniteMapExact.empty.updateList entries.reverse

@[simp] theorem lookup_alistToFmapHOLExact [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width)))
    (key : CrepInlineMapHOLName) :
    (alistToFmapHOLExact entries).lookup key =
      FUPDATE_LIST (FEMPTY : FiniteMap CrepInlineMapHOLName
        (List Nat × CrepProgHOL width)) entries.reverse key := rfl

/-- Exact port of HOL `compile_inl_prog_def`: for every triple, inline the body
    under the map with that function's own name erased. -/
noncomputable def compileInlProgHOLExact [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    List (CrepInlineMapHOLName × List Nat × CrepProgHOL width) :=
  prog.map fun triple =>
    (triple.1, triple.2.1, inlineProgHOLExact (inl_fs.erase triple.1) triple.2.2)

/-- Exact port of HOL `compile_inl_top_def`: build the inline alist by filtering
    the program to the named functions (HOL `FILTER (fun (x, y) => MEM x
    inl_fname) prog`), then run `compile_inl_prog`. -/
noncomputable def compileInlTopHOLExact [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (inl_fname : List CrepInlineMapHOLName)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    List (CrepInlineMapHOLName × List Nat × CrepProgHOL width) :=
  let inl_fs :=
    alistToFmapHOLExact
      (prog.filter fun triple => inl_fname.contains triple.1)
  compileInlProgHOLExact inl_fs prog

/-! ### Regression against the direct HOL `alist_to_fmap` / DOMSUB probe

These replay the rows of `scripts/hol-probes/crep_inline_alist_map_probe.out`
(`alist_duplicate_first=SOME ([7],Skip)`, `alist_other_row=SOME ([],Skip)`,
`domsub_selected_f=NONE`, `domsub_preserves_g=SOME ([],Skip)`), pinning the
first-occurrence-wins behavior of HOL `alist_to_fmap` and the `\\` (DOMSUB)
selected/preserved lookups used by `compile_inl_top`. Untagged, bead
`flapjack-e7w.2.2`. -/

private def alistProbeRows : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL 8)) :=
  [(ofString "f", ([7], (.skip : CrepProgHOL 8))),
   (ofString "f", ([9], (.tick : CrepProgHOL 8))),
   (ofString "g", ([], (.skip : CrepProgHOL 8)))]

/-- HOL `alist_duplicate_first`: the first `(«f», …)` row wins. -/
theorem alist_duplicate_first :
    (alistToFmapHOLExact alistProbeRows).lookup (ofString "f") =
      some ([7], (.skip : CrepProgHOL 8)) := by
  have hff : (ofString "f" == ofString "f") = true := by decide
  have hgf : (ofString "g" == ofString "f") = false := by decide
  simp only [alistProbeRows, alistToFmapHOLExact, HolFiniteMapExact.lookup_updateList,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    FUPDATE_LIST_cons, FUPDATE_LIST_nil, FUPDATE, hff, hgf, Bool.false_eq_true,
    if_true, if_false]

/-- HOL `alist_other_row`. -/
theorem alist_other_row :
    (alistToFmapHOLExact alistProbeRows).lookup (ofString "g") =
      some ([], (.skip : CrepProgHOL 8)) := by
  have hfg : (ofString "f" == ofString "g") = false := by decide
  have hgg : (ofString "g" == ofString "g") = true := by decide
  simp only [alistProbeRows, alistToFmapHOLExact, HolFiniteMapExact.lookup_updateList,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    FUPDATE_LIST_cons, FUPDATE_LIST_nil, FUPDATE, hfg, hgg, Bool.false_eq_true,
    if_true, if_false]

/-- HOL `domsub_selected_f`: erasing `«f»` removes its row. -/
theorem domsub_selected_f :
    ((alistToFmapHOLExact alistProbeRows).erase (ofString "f")).lookup (ofString "f") =
      none := by
  have hff : (ofString "f" == ofString "f") = true := by decide
  simp only [HolFiniteMapExact.erase, FDOMSUB, hff, if_true]

/-- HOL `domsub_preserves_g`: erasing `«f»` preserves `«g»`. -/
theorem domsub_preserves_g :
    ((alistToFmapHOLExact alistProbeRows).erase (ofString "f")).lookup (ofString "g") =
      some ([], (.skip : CrepProgHOL 8)) := by
  have hfg : (ofString "f" == ofString "g") = false := by decide
  simp only [HolFiniteMapExact.erase, FDOMSUB, hfg, Bool.false_eq_true, if_false,
    alist_other_row]

end CrepInlineCanonical

end Flapjack
