import Flapjack.Pancake.CrepInline.Pass

/-!
# HOL `inline_prog` over the canonical `HolFiniteMapExact`

This module contains the tagged `inlineProgHOLExact` port of HOL
`inline_prog_def`, its Flapjack-specific termination core and support helpers,
and the tagged `compileInlTopHOLExact` wrapper for HOL `compile_inl_top_def`.
The parser-proved compiler entrypoint executes `compileInlTopHOLExact` through
`compileProgNativeWithMetadataRouted`, `compileProgNativeWithMetadata`, and
`compileProgDeclsHOLW`. Standard BitVec zero/one dictionaries select this native
route; custom literal dictionaries retain the compatibility compiler.
`CompileProgCorrespondence.lean` proves complete decoded output and metadata
agreement at the parser-supplied declaration byte-range boundary.

The Flapjack-specific recursive core implementing the HOL `inline_prog`
equations (`cakeml/pancake/crep_inlineScript.sml:203-257`) uses the canonical
finite-support carrier
`Flapjack.HolFiniteMapExact` (`Flapjack/Pancake/Semantics/CrepSem/HOLState.lean:34`)
rather than the untagged unique-key list model `CrepInlineFmapHOL`
(`Flapjack/Pancake/CrepInline/Pass.lean:495`).

The recursive core is intentionally untagged because it carries Lean-only
support-list termination evidence. Its support-independent wrapper and the
top-level exact wrapper are tagged; the top-level wrapper runs in the tested,
non-executed alternative `compileProgTopHOLProductionExactInline`. The wider
exact `compile_prog` output/metadata bridge remains tracked separately.

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

`inlineProgHOLExact` is the tagged `inline_prog_def` port over the reviewed
standalone finite-support map parameter and width-indexed Crep program
carriers.  `compileInlProgHOLExact` and `compileInlTopHOLExact` are tagged
definition ports with their own reviewed input and carrier shapes.  The
recursive core `inlineProgHOLCoreExact` remains Flapjack-specific because its
support list and proof are termination certificates absent from HOL's
statement. The exact wrappers preserve HOL's external signatures while the core
keeps those Lean-only termination certificates internal.
-/

namespace Flapjack

namespace CrepInlineCanonical

variable {α : Type} {β : Type} {width : Nat} [NeZero width]

open Flapjack.Basis.Pure.MlString

/-! ## Standalone map-parameter carrier witness

The HOL `inline_prog` argument is a standalone finite-map parameter rather
than a field of a state record.  The checker has a separate
`fmap_as_finite_support_parameters` qualifier for this shape.  This broad view
exposes exactly the same lookup function together with finite-support proof;
the witness below records both roundtrips without asserting a correspondence
for arbitrary, possibly infinite-support functions. -/

/-- Broad lookup-plus-support view used by the standalone HOL fmap parameter
qualifier. -/
structure CrepInlineMapBroad (α β : Type) where
  lookup : α → Option β
  finiteSupport : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys

namespace CrepInlineMapBroad

/-- View a canonical finite-support map as its broad lookup/support pair. -/
def toBroad {α β : Type} (map : HolFiniteMapExact α β) : CrepInlineMapBroad α β :=
  ⟨map.lookup, map.finiteSupport⟩

/-- Rebuild the canonical carrier from a broad map and its support proof. -/
def ofBroad {α β : Type} (map : CrepInlineMapBroad α β) : HolFiniteMapExact α β :=
  ⟨map.lookup, map.finiteSupport⟩

/-- Roundtrip from canonical map to the broad lookup/support view and back. -/
theorem ofBroad_toBroad {α β : Type} (map : HolFiniteMapExact α β) :
    ofBroad (toBroad map) = map := by
  cases map
  rfl

end CrepInlineMapBroad

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

/-- FLAPJACK-SPECIFIC computable implementation of the HOL `inline_prog`
    equations (`crep_inlineScript.sml:203-257`) over the canonical
    `HolFiniteMapExact` inline map.  It is NOT presented as an exact `@[hol]`
    port: relative to HOL it takes two extra inputs, `supportKeys` together with
    `support_spec`, an explicit finite-support cardinality certificate used only
    for termination (HOL's `CARD (FDOM fs)` measure is unavailable because
    `HolFiniteMapExact` stores its support existentially).  Every clause mirrors
    `inlineProgHOLCore` (`Pass.lean:827`) and the HOL equations, with `fs.lookup`
    for `FLOOKUP` and `fs.erase name` for `inlineable_fs \\ e`.  Tag withheld
    pending coordinator carrier review; the support-independent wrapper/port
    remains tracked by `flapjack-e7w.2.1.13`. -/
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

theorem inlineProgHOLCoreExact_call_none [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (name : CrepInlineMapHOLName) (arguments : List (CrepExpHOL width)) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec
        (.call none name arguments) =
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
            (argLoadHOLExact temporaryNames arguments argumentNames inlinedCallee) := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_call_returns [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (returnNames : List Nat) (name : CrepInlineMapHOLName)
    (arguments : List (CrepExpHOL width)) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec
        (.call (some (returnNames, none)) name arguments) =
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
              temporaryReturns temporaryNames arguments argumentNames := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_assign [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (name : Nat) (value : CrepExpHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.assign name value) =
      .assign name value := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_primitive [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (names : List Nat) (operator : PrimOp) (args : List Nat) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec
        (.primitive names operator args) =
      .primitive names operator args := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_store [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (address value : CrepExpHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.store address value) =
      .store address value := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_store32 [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (address value : CrepExpHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.store32 address value) =
      .store32 address value := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_storeByte [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (address value : CrepExpHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.storeByte address value) =
      .storeByte address value := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_storeGlob [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (address : BitVec 5) (value : CrepExpHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.storeGlob address value) =
      .storeGlob address value := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_break [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (label : Nat) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.break label) =
      .break label := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_continue [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (label : Nat) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.continue label) =
      .continue label := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_extCall [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (function : MlString) (configuration configurationLength array arrayLength : Nat) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec
        (.extCall function configuration configurationLength array arrayLength) =
      .extCall function configuration configurationLength array arrayLength := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_raise [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (exception : BitVec width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.raise exception) =
      .raise exception := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_return [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (values : List (CrepExpHOL width)) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.return values) =
      .return values := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_shMem [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (operator : WordMemOp) (name : Nat) (address : CrepExpHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec (.shMem operator name address) =
      .shMem operator name address := by
  simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_tick [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec .tick = .tick := by
  simp only [inlineProgHOLCoreExact]

/-- Canonical finite-support representation witness for the HOL map argument
    of `inlineProgHOLExact`. -/
theorem holFmapAsFiniteSupportParamWitness_inlineProgHOLExact_inlineable
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width)) (key : CrepInlineMapHOLName) :
    (CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inlineable)).lookup key =
        inlineable.lookup key ∧
      (CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inlineable)).finiteSupport =
        inlineable.finiteSupport ∧
      CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inlineable) = inlineable := by
  exact ⟨rfl, rfl, CrepInlineMapBroad.ofBroad_toBroad inlineable⟩

/-- HOL `inline_prog_def` (`crep_inlineScript.sml:203-257`) over the exact
    width-indexed `CrepProgHOL` carrier.  Its standalone finite-map parameter
    uses `HolFiniteMapExact`, the reviewed lookup-plus-finite-support model of
    HOL `|->`; `holFmapAsFiniteSupportParamWitness_inlineProgHOLExact_inlineable`
    records the carrier roundtrip.  The `[NeZero width]` word representation is
    recorded by `words_as_type_indexed_bitvec`.  Clause review against the HOL
    source found the Call handler recursion, return-distinct guard, `FLOOKUP`,
    `DOMSUB`, argument/temporary generation, and recursive structural clauses
    aligned.  The definition is noncomputable only because its support list is
    chosen from the finite-support witness for Lean termination; the output is
    independent of that certificate. -/
@[hol "cakeml/pancake/crep_inlineScript.sml" "inline_prog_def"
  (fmap_as_finite_support_parameters := [inlineable]) (words_as_type_indexed_bitvec)]
noncomputable def inlineProgHOLExact
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

Flapjack-specific analogues of HOL `compile_inl_prog_def` and `compile_inl_top_def`
(`cakeml/pancake/crep_inlineScript.sml:259,264`) over the exact carriers:
`mlstring` function names (`CrepInlineMapHOLName`), the canonical finite-support
inline map (`HolFiniteMapExact`), and `CrepProgHOL` triple lists.  Their
standalone finite-map argument and word-indexed carriers are explicitly
qualified below. `compileInlTopHOLExact` is executable; its direct HOL probe
replay is included in `canonicalOracleGuard`. -/

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

/-- A computable finite support for the map built by `alistToFmapHOLExact`: the
    key list is exactly the alist's keys, so the executable inline wrappers need
    no `Classical.choose` and `HolFiniteMapExact`'s existential `finiteSupport`
    is never inspected. Mirrors the `supportKeys` certificate used by
    `inlineProgHOLCoreExact`. -/
theorem supportKeys_alistToFmapHOLExact [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (entries : List (CrepInlineMapHOLName × (List Nat × CrepProgHOL width))) :
    ∀ key, (alistToFmapHOLExact entries).lookup key ≠ none →
      key ∈ entries.map Prod.fst := by
  intro key hkey
  by_cases hmem : key ∈ entries.map Prod.fst
  · exact hmem
  · exfalso
    have hrev : key ∉ entries.reverse.map Prod.fst := by
      intro hh
      rw [List.mem_map] at hh
      obtain ⟨entry, hentry, hfst⟩ := hh
      exact hmem (List.mem_map.mpr ⟨entry, List.mem_reverse.mp hentry, hfst⟩)
    have hnone : FLOOKUP (FUPDATE_LIST (FEMPTY : FiniteMap CrepInlineMapHOLName
        (List Nat × CrepProgHOL width)) entries.reverse) key = none := by
      rw [FLOOKUP_FUPDATE_LIST_not_mem _ _ _ hrev]
      rfl
    exact hkey (by rw [lookup_alistToFmapHOLExact]; exact hnone)

/-- FLAPJACK-SPECIFIC computable variant of HOL `compile_inl_prog_def`
    (`crep_inlineScript.sml:259`), carrying an explicit finite-support
    `supportKeys` / `support_spec` certificate so the definition stays
    executable (no `Classical.choose`).  This is an internal computability
    device, not the HOL-shaped statement; the support-independent wrapper
    `compileInlProgHOLExact` below matches HOL's two arguments. -/
def compileInlProgHOLExactWithSupport [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inl_fs.lookup key ≠ none → key ∈ supportKeys)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    List (CrepInlineMapHOLName × List Nat × CrepProgHOL width) :=
  prog.map fun triple =>
    (triple.1, triple.2.1,
      inlineProgHOLCoreExact (inl_fs.erase triple.1)
        (supportKeys.filter (fun key => key != triple.1))
        (HolFiniteMapExact.erase_support inl_fs supportKeys support_spec triple.1)
        triple.2.2)

/-- HOL `compile_inl_prog_def` (`crep_inlineScript.sml:259`) over the
    canonical finite-support inline map.  For each input triple it erases that
    function's own name from the map, applies `inlineProgHOLExact` to the body,
    and preserves list order exactly as HOL `MAP` does. The standalone map and
    width-indexed word carriers are recorded by the qualifiers. This definition
    is noncomputable because it extracts the support witness used only to
    establish termination; the executable top-level wrapper threads support
    keys explicitly. -/
theorem holFmapAsFiniteSupportParamWitness_compileInlProgHOLExact_inl_fs
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width)) (key : CrepInlineMapHOLName) :
    (CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inl_fs)).lookup key =
        inl_fs.lookup key ∧
      (CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inl_fs)).finiteSupport =
        inl_fs.finiteSupport ∧
      CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inl_fs) = inl_fs := by
  exact ⟨rfl, rfl, CrepInlineMapBroad.ofBroad_toBroad inl_fs⟩

@[hol "cakeml/pancake/crep_inlineScript.sml" "compile_inl_prog_def"
  (fmap_as_finite_support_parameters := [inl_fs]) (words_as_type_indexed_bitvec)]
noncomputable def compileInlProgHOLExact
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    List (CrepInlineMapHOLName × List Nat × CrepProgHOL width) :=
  prog.map fun triple =>
    (triple.1, triple.2.1,
      inlineProgHOLExact (inl_fs.erase triple.1) triple.2.2)

/-- HOL `compile_inl_top_def` (`crep_inlineScript.sml:264`):
    build the inline alist by filtering the program to the named functions (HOL
    `FILTER (fun (x, y) => MEM x inl_fname) prog`), turn it into the canonical
    finite-support map via `alistToFmapHOLExact` (HOL `alist_to_fmap`,
    first-occurrence-wins), then run the inline pass.  Two arguments, matching
    HOL exactly (`inl_fname`, `prog`); the inline map is a local intermediate and
    does not occur in the signature, and the finite support is derived from the
    filtered alist's keys. The word-indexed representation is recorded by the
    qualifier; source membership, alist first-binding behavior, and recursive
    inlining are checked by `canonicalOracleGuard`. The standard parser-proved
    compiler route executes this wrapper via `compileProgDeclsHOLW` and
    `compileProgNativeWithMetadataRouted`; complete output agreement with the
    compatibility route is proved in `CompileProgCorrespondence.lean`. -/
@[hol "cakeml/pancake/crep_inlineScript.sml" "compile_inl_top_def"
  (words_as_type_indexed_bitvec)]
def compileInlTopHOLExact
    (inl_fname : List CrepInlineMapHOLName)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    List (CrepInlineMapHOLName × List Nat × CrepProgHOL width) :=
  let entries := prog.filter fun triple => inl_fname.contains triple.1
  let inl_fs := alistToFmapHOLExact entries
  compileInlProgHOLExactWithSupport inl_fs (entries.map Prod.fst)
    (supportKeys_alistToFmapHOLExact entries) prog

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

/-! ### Executability regression for `compile_inl_top`

The support certificate is derived from the filtered alist, not from
`Classical.choose`, so `compileInlTopHOLExact` really evaluates. This mirrors the
production `compileInlTopOracle` in `Flapjack/Test/CompileProgParity.lean`
(inline `first` calling `second`, whose body is a constant return). -/

private def inlTopProbeProg :
    List (CrepInlineMapHOLName × List Nat × CrepProgHOL 8) :=
  [(ofString "first", ([], (.call none (ofString "second") [] : CrepProgHOL 8))),
   (ofString "second", ([], (.return [.const 9] : CrepProgHOL 8)))]

private def inlTopProbeOracle : Bool :=
  match compileInlTopHOLExact [ofString "first", ofString "second"] inlTopProbeProg with
  | [first, second] =>
      (match first.2.2 with
       | .seq .tick (.return [.const 9]) => true
       | _ => false) &&
      (match second.2.2 with
       | .return [.const 9] => true
       | _ => false)
  | _ => false

#guard inlTopProbeOracle

/-! ### Direct canonical-core replay of the `inline_prog` HOL probe rows

Every row of `scripts/hol-probes/crep_inline_code_inl_probe.out` is replayed
through `inlineProgHOLCoreExact` on the canonical `HolFiniteMapExact` carrier
view: hit (`inlined_call`), miss (`no_match_call`), DOMSUB self-call
(`inline_nested_call`), argument loading with generated temporary names
(`inline_arg_call`), duplicate overwrite (`lookup_dup_f`/`inline_dup_call`) and
handler call (`handler_call_untouched`). Untagged, bead `flapjack-e7w.2.1.13`. -/

private def canonicalOracleBodyA : CrepProgHOL 8 := .dec 1 (.const 1) .skip

private def canonicalOracleBodyB : CrepProgHOL 8 := .dec 9 (.const 3) .skip

private def canonicalOracleCore (fs : CrepInlineFmapHOL 8) (program : CrepProgHOL 8) :
    CrepProgHOL 8 :=
  inlineProgHOLCoreExact fs.toHolFiniteMapExact fs.domainKeys (domainKeys_spec fs) program

private def canonicalOracleGuard : Bool :=
  let key := ofString "f"
  let absent := ofString "g"
  let base := CrepInlineFmapHOL.insert key ([7], canonicalOracleBodyA) CrepInlineFmapHOL.empty
  -- HOL `flookup_f` / `inlined_call`: `Seq Tick Skip`.
  let hit := match canonicalOracleCore base (.call none key []) with
    | .seq .tick .skip => true
    | _ => false
  -- HOL `no_match_call`: a missed name is left untouched.
  let miss := match canonicalOracleCore base (.call none absent []) with
    | .call none name [] => name == absent
    | _ => false
  -- HOL `inline_nested_call`: `\\` (DOMSUB) before recursing leaves the self-call.
  let nestedBase := CrepInlineFmapHOL.insert key ([], .call none key []) CrepInlineFmapHOL.empty
  let nested := match canonicalOracleCore nestedBase (.call none key []) with
    | .seq .tick (.call none name []) => name == key
    | _ => false
  -- HOL `inline_arg_call`: `arg_load`/`GENLIST` generated temporary names.
  let args := match canonicalOracleCore base (.call none key [.const 5]) with
    | .seq .tick (.dec 8 (.const 5) (.dec 7 (.var 8) (.dec 1 (.const 1) .skip))) => true
    | _ => false
  -- HOL `lookup_dup_f`: `|+` overwrites, so the later binding is selected. This
  -- direct lookup assertion is the primary evidence for overwrite semantics.
  let dupBase := CrepInlineFmapHOL.insert key ([9], canonicalOracleBodyB) base
  let dupLookup : Bool :=
    match dupBase.lookup key with
    | some value =>
        (value.1 == [9]) &&
          (match value.2 with | .dec 9 (.const 3) .skip => true | _ => false)
    | none => false
  -- HOL `inline_dup_call`: with the original argument names the empty argument
  -- list makes `arg_load` discard the body (`Seq Tick Skip`), reproducing the
  -- probe row.
  let dup := match canonicalOracleCore dupBase (.call none key []) with
    | .seq .tick .skip => true
    | _ => false
  -- Distinguishing shadowing fixture: with empty argument names `arg_load`
  -- preserves the body, so the inlined program is observable. Choosing the
  -- stale `bodyA` binding would yield `Seq Tick (Dec 1 (Const 1) Skip)` and
  -- fail this check, which the `dup` row above cannot detect.
  let obsDupBase := CrepInlineFmapHOL.insert key ([], canonicalOracleBodyB) base
  let dupInlinesNew : Bool :=
    match canonicalOracleCore obsDupBase (.call none key []) with
    | .seq .tick p =>
        (match p with | .dec 9 (.const 3) .skip => true | _ => false)
    | _ => false
  -- HOL `handler_call_untouched`: the handler is inlined, the call is unchanged.
  let handler := match canonicalOracleCore base
      (.call (some ([1], some (2, (.skip : CrepProgHOL 8)))) key []) with
    | .call (some ([1], some (2, .skip))) name [] => name == key
    | _ => false
  hit && miss && nested && args && dup && dupLookup && dupInlinesNew && handler

#guard canonicalOracleGuard

/-! ## Support-independence of the inline core

These facts justify the executable HOL-shaped wrappers above: the recursive
`inlineProgHOLCoreExact` result does not depend on the certificate list/proof it
is run with, so the certified executable `compileInlProgHOLExactWithSupport`
(used by the tagged `compileInlTopHOLExact`) agrees with the HOL-shaped
`compileInlProgHOLExact`, which extracts the existential support classically.
Untagged Flapjack-specific infrastructure (bead flapjack-e7w.2.2.1). -/

theorem inlineProgHOLCoreExact_support_independent [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (supportKeys₁ : List CrepInlineMapHOLName)
    (support₁ : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys₁)
    (supportKeys₂ : List CrepInlineMapHOLName)
    (support₂ : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys₂)
    (program : CrepProgHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys₁ support₁ program =
      inlineProgHOLCoreExact inlineable supportKeys₂ support₂ program := by
  refine @inlineProgHOLCoreExact.induct width _ _ _
    (fun inlineable supportKeys support_spec prog =>
      ∀ (supportKeys₂ : List CrepInlineMapHOLName)
        (support₂ : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys₂),
        inlineProgHOLCoreExact inlineable supportKeys support_spec prog =
          inlineProgHOLCoreExact inlineable supportKeys₂ support₂ prog)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    inlineable supportKeys₁ support₁ program supportKeys₂ support₂
  · intro inlineable supportKeys support_spec name arguments hl supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact]
    rw [hl]
  · intro inlineable supportKeys support_spec name arguments argumentNames body hl ih
      supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact]
    rw [hl]
    simp only []
    rw [ih (supportKeys₂.filter (fun k => k != name))
      (HolFiniteMapExact.erase_support inlineable supportKeys₂ support₂ name)]
  · intro inlineable supportKeys support_spec returnNames name arguments hd supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact, hd, if_true]
  · intro inlineable supportKeys support_spec returnNames name arguments hd hl supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact]
    simp only [if_neg hd]
    rw [hl]
  · intro inlineable supportKeys support_spec returnNames name arguments hd argumentNames body hl ih
      supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact]
    simp only [if_neg hd]
    rw [hl]
    simp only []
    rw [ih (supportKeys₂.filter (fun k => k != name))
      (HolFiniteMapExact.erase_support inlineable supportKeys₂ support₂ name)]
  · intro inlineable supportKeys support_spec returnNames handler body name arguments ih
      supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact]
    rw [ih supportKeys₂ support₂]
  · intro inlineable supportKeys support_spec name value body ih supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact]
    rw [ih supportKeys₂ support₂]
  · intro inlineable supportKeys support_spec first second ih1 ih2 supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact]
    rw [ih1 supportKeys₂ support₂, ih2 supportKeys₂ support₂]
  · intro inlineable supportKeys support_spec condition first second ih1 ih2 supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact]
    rw [ih1 supportKeys₂ support₂, ih2 supportKeys₂ support₂]
  · intro inlineable supportKeys support_spec condition body ih supportKeys₂ support₂
    simp only [inlineProgHOLCoreExact]
    rw [ih supportKeys₂ support₂]
  · intro inlineable supportKeys support_spec program hcn hcs hch hdec hseq hite hwhile
      supportKeys₂ support₂
    cases program with
    | call ret name args =>
        cases ret with
        | none => exact absurd rfl (hcn name args)
        | some p =>
            obtain ⟨rn, hb⟩ := p
            cases hb with
            | none => exact absurd rfl (hcs rn name args)
            | some hb' =>
                obtain ⟨handler, body⟩ := hb'
                exact absurd rfl (hch rn handler body name args)
    | dec name value body => exact absurd rfl (hdec name value body)
    | seq first second => exact absurd rfl (hseq first second)
    | ite c a b => exact absurd rfl (hite c a b)
    | «while» c b => exact absurd rfl (hwhile c b)
    | skip => simp only [inlineProgHOLCoreExact]
    | assign name value => simp only [inlineProgHOLCoreExact]
    | primitive names operator args => simp only [inlineProgHOLCoreExact]
    | store address value => simp only [inlineProgHOLCoreExact]
    | store32 address value => simp only [inlineProgHOLCoreExact]
    | storeByte address value => simp only [inlineProgHOLCoreExact]
    | storeGlob address value => simp only [inlineProgHOLCoreExact]
    | «break» label => simp only [inlineProgHOLCoreExact]
    | «continue» label => simp only [inlineProgHOLCoreExact]
    | extCall function configuration configurationLength array arrayLength =>
        simp only [inlineProgHOLCoreExact]
    | raise exception => simp only [inlineProgHOLCoreExact]
    | «return» values => simp only [inlineProgHOLCoreExact]
    | shMem operator name address => simp only [inlineProgHOLCoreExact]
    | tick => simp only [inlineProgHOLCoreExact]

theorem inlineProgHOLCoreExact_eq_inlineProgHOLExact
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (program : CrepProgHOL width) :
    inlineProgHOLCoreExact inlineable supportKeys support_spec program =
      inlineProgHOLExact inlineable program := by
  unfold inlineProgHOLExact
  exact inlineProgHOLCoreExact_support_independent inlineable supportKeys support_spec
    (Classical.choose inlineable.finiteSupport)
    (Classical.choose_spec inlineable.finiteSupport) program

theorem compileInlProgHOLExactWithSupport_eq_compileInlProgHOLExact
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inl_fs.lookup key ≠ none → key ∈ supportKeys)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    compileInlProgHOLExactWithSupport inl_fs supportKeys support_spec prog =
      compileInlProgHOLExact inl_fs prog := by
  simp only [compileInlProgHOLExactWithSupport, compileInlProgHOLExact]
  apply List.map_congr_left
  intro triple _
  rw [inlineProgHOLCoreExact_eq_inlineProgHOLExact]

theorem compileInlTopHOLExact_eq_compileInlProgHOLExact
    (inl_fname : List CrepInlineMapHOLName)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    compileInlTopHOLExact inl_fname prog =
      compileInlProgHOLExact
        (alistToFmapHOLExact (prog.filter fun triple => inl_fname.contains triple.1)) prog := by
  unfold compileInlTopHOLExact
  exact compileInlProgHOLExactWithSupport_eq_compileInlProgHOLExact _ _ _ _

end CrepInlineCanonical

end Flapjack
