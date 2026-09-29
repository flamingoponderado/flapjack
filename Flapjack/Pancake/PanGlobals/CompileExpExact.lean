import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Prog
import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
Exact-carrier port of `pan_globals$compile_exp_def`.

HOL (`cakeml/pancake/pan_globalsScript.sml:10-16`, `:18-46`) compiles a
`panLang$exp` against a `'a pan_globals$context`, whose sole finite-map field
`globals : varname |-> shape # 'a word` is keyed by `mlstring` names.  The
context carrier below reproduces that record with the reviewed canonical
`HolFiniteMapExact` translation of the HOL `|->` field, `MlS` keys, `ShapeHOL`
payloads, and `BitVec width` (`'a word`) values; the function port runs over
the exact `ExpHOL width` carrier.

The `fmap_as_finite_support` qualifier records only the finite-support map
representation and the `words_as_type_indexed_bitvec` qualifier only the
type-indexed `'a word` / positive-width `BitVec width` translation; neither
changes a quantifier, hypothesis, side condition, or conclusion of the HOL
clauses.

The kernel-checked bridge `compileExpCake_cakeContextOfExact` at the end of this
module connects the executed String-backed production compiler `compileExpCake`
to this exact definition under the byte-range hypothesis `ExpByteRanged` that
the parser supplies: the production result is exactly the `expOfHOL` image of
`compileExpExactHOL` run on the `expToHOL` image of the input.  It follows the
`progToHOL`/`progOfHOL` codec pattern: the production `compileExpCake` remains
untagged, and the exact `compileExpExactHOL` is reached through the
`cakeContextOfExact` adapter.  It is a bridge, not textual routing: the
executed `compileDecsCake`/`compileProgCake`/`compileExpCake` chain still
computes the production function directly.  A total textual route is blocked
because a production `CakeContext` carries an arbitrary `String → Option _`
globals function with no finite-support witness for the exact
`HolFiniteMapExact` field, and because decoding an output name needs the
byte-range premise; the remaining production routing is tracked by
`flapjack-pxn.18.3.5.8.29`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
  (MlS ShapeHOL ExpHOL expToHOL expOfHOL ExpByteRanged ListExpByteRanged shapeOfHOL
    shapeValHOL mlstrAppend ProgHOL freeVarIdsHOL varExpHOL)

/-- Broad function-backed representation paired with support evidence, used
    only to state the finite-support representation roundtrip for
    `PanGlobalsContextExact`. -/
structure PanGlobalsContextBroad (width : Nat) where
  globalsLookup : MlS → Option (ShapeHOL × BitVec width)
  globalsFiniteSupport :
    ∃ keys : List MlS, ∀ key, globalsLookup key ≠ none → key ∈ keys
  globalsSize : BitVec width
  maxGlobalsSize : BitVec width

/-- Exact HOL `pan_globals$context` record
    (`cakeml/pancake/pan_globalsScript.sml:10-16`):
    `context = <| globals : varname |-> shape # 'a word;
    globals_size : 'a word; max_globals_size : 'a word |>`.

    The `globals` field uses the reviewed `HolFiniteMapExact` translation of
    the HOL `|->` finite map, keyed by `MlS` (`varname` = `mlstring`) with
    `ShapeHOL × BitVec width` values; the two size fields are `BitVec width`
    (`'a word`).  The `fmap_as_finite_support` and `words_as_type_indexed_bitvec`
    qualifiers record only those two representations. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "context"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
structure PanGlobalsContextExact (width : Nat) [NeZero width] where
  globals : HolFiniteMapExact MlS (ShapeHOL × BitVec width)
  globalsSize : BitVec width
  maxGlobalsSize : BitVec width

namespace PanGlobalsContextExact

/-- Forget the finite-map wrapper while retaining its finite-support evidence. -/
def toBroad {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextBroad width where
  globalsLookup := context.globals.lookup
  globalsFiniteSupport := context.globals.finiteSupport
  globalsSize := context.globalsSize
  maxGlobalsSize := context.maxGlobalsSize

/-- Reconstruct the canonical finite-support carrier from its broad record. -/
def ofBroad {width : Nat} [NeZero width] (context : PanGlobalsContextBroad width) :
    PanGlobalsContextExact width where
  globals := ⟨context.globalsLookup, context.globalsFiniteSupport⟩
  globalsSize := context.globalsSize
  maxGlobalsSize := context.maxGlobalsSize

/-- Canonical finite-support witness required by the `fmap_as_finite_support`
    qualifier: the `toBroad`/`ofBroad` roundtrip on `PanGlobalsContextExact`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) :
    ofBroad (toBroad context) = context := by
  cases context
  rfl

/-- Production `CakeContext` induced by an exact `pan_globals` context.  Names
    are encoded with the total `ofString` and payload shapes are decoded with
    `shapeOfHOL`; the two size fields agree definitionally.  This is the
    production counterpart of the codec bridge below, not a HOL declaration. -/
def cakeContextOfExact {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) : CakeContext width where
  globals := fun key =>
    (context.globals.lookup (ofString key)).map
      (fun entry => (shapeOfHOL entry.1, entry.2))
  globalsSize := context.globalsSize
  maxGlobalsSize := context.maxGlobalsSize

end PanGlobalsContextExact

open PanGlobalsContextExact

/-! ### Exact-carrier `compile_exp_def`

Every one of the fifteen HOL clauses plus the catch-all is reproduced in HOL's
order over `ExpHOL width` and `PanGlobalsContextExact width`: `Var Local` is
the identity; `Var Global` looks the `MlS` name up in the exact finite map and
yields `Load sh (Op Sub [TopAddr; Const addr])` on a hit and `Const 0w` on a
miss; `RStruct`/`RField` recurse; `NStruct`/`NField` yield `Const 0w`;
`Load`/`LoadByte`/`Load32` recurse into the address; `Op`/`Panop` map over the
arguments; `Cmp`/`Shift` recurse into both operands; `TopAddr` becomes
`Op Sub [TopAddr; Const max_globals_size]`; and the remaining constructors
(`Const`, `BaseAddr`, `BytesInWord`) are the catch-all `compile_exp ctxt e = e`.

The direct HOL-EVAL fixture `scripts/hol-probes/pan_globals_compile_exp_probe.out`
(`local`, `global_hit`, `global_miss`, `top_addr`, `nested`) is replayed at the
exact carrier by `Flapjack/Test/PanGlobalsCompileExpExactParity.lean`. -/
mutual
  /-- Exact width-indexed port of HOL `pan_globals$compile_exp_def`
      (`cakeml/pancake/pan_globalsScript.sml:18-46`). -/
  @[hol "cakeml/pancake/pan_globalsScript.sml" "compile_exp_def"
    (fmap_as_finite_support := [globals])
    (words_as_type_indexed_bitvec)]
  def compileExpExactHOL {width : Nat} [NeZero width]
      (context : PanGlobalsContextExact width) :
      ExpHOL width → ExpHOL width
    | .const value => .const value
    | .var .local name => .var .local name
    | .var .global name =>
        match context.globals.lookup name with
        | some (shape, address) =>
            .load shape (.op .sub [.topAddr, .const address])
        | none => .const (0 : BitVec width)
    | .rstruct fields => .rstruct (compileExpExactHOLList context fields)
    | .rfield index value => .rfield index (compileExpExactHOL context value)
    | .nstruct _ _ => .const (0 : BitVec width)
    | .nfield _ _ => .const (0 : BitVec width)
    | .load shape address => .load shape (compileExpExactHOL context address)
    | .load32 address => .load32 (compileExpExactHOL context address)
    | .loadByte address => .loadByte (compileExpExactHOL context address)
    | .op operator args => .op operator (compileExpExactHOLList context args)
    | .panop operator args => .panop operator (compileExpExactHOLList context args)
    | .cmp operator left right =>
        .cmp operator (compileExpExactHOL context left)
          (compileExpExactHOL context right)
    | .shift operator left right =>
        .shift operator (compileExpExactHOL context left)
          (compileExpExactHOL context right)
    | .baseAddr => .baseAddr
    | .topAddr => .op .sub [.topAddr, .const context.maxGlobalsSize]
    | .bytesInWord => .bytesInWord
  termination_by expression => sizeOf expression
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  /-- `MAP (compile_exp ctxt)` in HOL's `RStruct`/`Op`/`Panop` equations. -/
  def compileExpExactHOLList {width : Nat} [NeZero width]
      (context : PanGlobalsContextExact width) :
      List (ExpHOL width) → List (ExpHOL width)
    | [] => []
    | expression :: expressions =>
        compileExpExactHOL context expression ::
          compileExpExactHOLList context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-! ### Exact-carrier `pan_globals$compile_def`

HOL's program compiler is separate from `compile_exp_def`: it recursively
rewrites control flow and uses the exact global map for global destinations
and shared-memory loads.  Keep this port on `ProgHOL` and
`PanGlobalsContextExact`; the production `compileProgCake` is String-backed
and does not establish this declaration. The exact fresh-name clause reuses
the already-reviewed `freshNameMlS` port. -/

/-- Exact-carrier port of HOL `pan_globals$compile_def`
    (`pan_globalsScript.sml:69-149`).  Its constructor equations and final
    catch-all are copied from the source, with HOL `compile_exp` represented by the
    reviewed `compileExpExactHOL`, `free_var_ids` by `freeVarIdsHOL`, and
    `shape_val` by `shapeValHOL`.  In particular, global call destinations
    preserve the source's missing-entry fallbacks, handled calls allocate the
    source-fresh result and flag names, and a global `ShMemLoad` is lowered
    only for a `One` global. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_def"
  (fmap_as_finite_support := [globals])
  (words_as_type_indexed_bitvec)]
def compileProgExactHOL {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) : ProgHOL width → ProgHOL width
  | .skip => .skip
  | .dec name shape value body =>
      .dec name shape (compileExpExactHOL context value) (compileProgExactHOL context body)
  | .assign .global name value =>
      match context.globals.lookup name with
      | some (_shape, address) =>
          .store (.op .sub [.topAddr, .const address]) (compileExpExactHOL context value)
      | none => .skip
  | .assign .local name value => .assign .local name (compileExpExactHOL context value)
  | .primitive name operator args =>
      .primitive name operator (compileExpExactHOLList context args)
  | .store address value =>
      .store (compileExpExactHOL context address) (compileExpExactHOL context value)
  | .store32 address value =>
      .store32 (compileExpExactHOL context address) (compileExpExactHOL context value)
  | .storeByte address value =>
      .storeByte (compileExpExactHOL context address) (compileExpExactHOL context value)
  | .seq first second =>
      .seq (compileProgExactHOL context first) (compileProgExactHOL context second)
  | .ite condition thenBranch elseBranch =>
      .ite (compileExpExactHOL context condition)
        (compileProgExactHOL context thenBranch) (compileProgExactHOL context elseBranch)
  | .while condition body =>
      .while (compileExpExactHOL context condition) (compileProgExactHOL context body)
  | .call info function args =>
      let cargs := compileExpExactHOLList context args
      match info with
      | none => .call none function cargs
      | some (none, none) => .call (some (none, none)) function cargs
      | some (none, some (exception, handlerVar, handler)) =>
          .call (some (none, some (exception, handlerVar,
            compileProgExactHOL context handler))) function cargs
      | some (some (.local, name), none) =>
          .call (some (some (.local, name), none)) function cargs
      | some (some (.local, name), some (exception, handlerVar, handler)) =>
          .call (some (some (.local, name), some (exception, handlerVar,
            compileProgExactHOL context handler))) function cargs
      | some (some (.global, name), none) =>
          match context.globals.lookup name with
          | some (shape, address) =>
              .decCall (ofString "") shape function cargs
                (.store (.op .sub [.topAddr, .const address]) (.var .local (ofString "")))
          | none => .call (some (none, none)) function cargs
      | some (some (.global, name), some (exception, handlerVar, handler)) =>
          match context.globals.lookup name with
          | some (shape, address) =>
              let compiledHandler := compileProgExactHOL context handler
              let names := handlerVar :: freeVarIdsHOL compiledHandler ++
                cargs.flatMap varExpHOL
              let resultName := freshNameMlS (ofString "") names
              let flagName := freshNameMlS (ofString "vn'") (resultName :: names)
              let handlerBody :=
                .seq compiledHandler (.assign .local flagName (.const (BitVec.ofNat width 1)))
              let callInfo := some (some (.local, resultName),
                some (exception, handlerVar, handlerBody))
              let storeAddress := .op .sub [.topAddr, .const address]
              .dec resultName shape (shapeValHOL shape)
                (.dec flagName .one (.const (BitVec.ofNat width 0))
                  (.seq (.call callInfo function cargs)
                    (.ite (.var .local flagName) .skip
                      (.store storeAddress (.var .local resultName)))))
          | none =>
              .call (some (none, some (exception, handlerVar,
                compileProgExactHOL context handler))) function cargs
  | .decCall name shape function args body =>
      .decCall name shape function (compileExpExactHOLList context args)
        (compileProgExactHOL context body)
  | .extCall function config configLength array arrayLength =>
      .extCall function (compileExpExactHOL context config)
        (compileExpExactHOL context configLength) (compileExpExactHOL context array)
        (compileExpExactHOL context arrayLength)
  | .raise exception value => .raise exception (compileExpExactHOL context value)
  | .return value => .return (compileExpExactHOL context value)
  | .shMemLoad size .local name address =>
      .shMemLoad size .local name (compileExpExactHOL context address)
  | .shMemLoad size .global name address =>
      match context.globals.lookup name with
      | some (.one, globalAddress) =>
          let localName := mlstrAppend name (ofString "'")
          .dec name .one (compileExpExactHOL context address)
            (.dec localName .one (.const (BitVec.ofNat width 0))
              (.seq (.shMemLoad size .local localName (.var .local name))
                (.store (.op .sub [.topAddr, .const globalAddress]) (.var .local localName))))
      | _ => .skip
  | .shMemStore size address value =>
      .shMemStore size (compileExpExactHOL context address) (compileExpExactHOL context value)
  | program => program
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- Kernel-checked codec bridge between the executed String-backed production
    compiler `compileExpCake` and the reviewed exact `compileExpExactHOL`.  For
    every exact context and every byte-ranged production expression, running the
    production compiler on `cakeContextOfExact context` yields exactly the
    `expOfHOL` image of `compileExpExactHOL context` run on `expToHOL
    expression`.  This is Flapjack bridge infrastructure (no HOL declaration has
    this paired representation statement); the production compiler stays
    untagged.

    It follows the `progToHOL`/`progOfHOL` codec pattern: the `ExpByteRanged`
    hypothesis is exactly the parser-supplied round-trip premise
    (`expOfHOL_expToHOL`); the global lookup uses `ofString` on both sides and
    the emitted shape is decoded by `shapeOfHOL`, so no further premise is
    needed.  This is a bridge, not textual routing: `compileDecsCake` and
    `compileProgCake` still call `compileExpCake` textually. -/
@[simp] theorem compileExpCake_cakeContextOfExact {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) :
    (expression : Exp (BitVec width)) → ExpByteRanged expression →
      compileExpCake (cakeContextOfExact context) expression
        = expOfHOL (compileExpExactHOL context (expToHOL expression)) :=
  Flapjack.Exp.rec
    (motive_1 := fun expression =>
      ExpByteRanged expression →
        compileExpCake (cakeContextOfExact context) expression
          = expOfHOL (compileExpExactHOL context (expToHOL expression)))
    (motive_2 := fun expressions =>
      ListExpByteRanged expressions →
        compileExpCake.compileExpCakeList (cakeContextOfExact context) expressions
          = (compileExpExactHOLList context (expressions.map expToHOL)).map expOfHOL)
    (motive_3 := fun _ => True)
    (motive_4 := fun _ => True)
    (fun _value _ => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake])
    (fun kind name hname => by
      cases kind with
      | «local» =>
          simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]
          rw [toStringOfBytes_ofString_of_bytes name hname]
      | global =>
          simp only [expToHOL, compileExpExactHOL, compileExpCake,
            PanGlobalsContextExact.cakeContextOfExact, FLOOKUP]
          cases h : context.globals.lookup (ofString name) with
          | none => simp only [Option.map_none, expOfHOL]; try rfl
          | some entry =>
              obtain ⟨shape, address⟩ := entry
              simp only [Option.map_some, expOfHOL, List.map_cons, List.map_nil]
              try rfl)
    (fun expressions ih hexpressions => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]
      rw [ih hexpressions])
    (fun index value ih hvalue => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]
      rw [ih hvalue])
    (fun name fields _ih _ => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]; try rfl)
    (fun name value _ih _ => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]; try rfl)
    (fun shape address ih hload => by
      obtain ⟨hshape, haddress⟩ := hload
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake,
        Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL shape hshape]
      rw [ih haddress])
    (fun address ih haddress => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]
      rw [ih haddress])
    (fun address ih haddress => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]
      rw [ih haddress])
    (fun operator args ih hargs => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]
      rw [ih hargs])
    (fun operator args ih hargs => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]
      rw [ih hargs])
    (fun operator left right ihl ihr hcmp => by
      obtain ⟨hl, hr⟩ := hcmp
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]
      rw [ihl hl, ihr hr])
    (fun operator left right ihl ihr hshift => by
      obtain ⟨hl, hr⟩ := hshift
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake]
      rw [ihl hl, ihr hr])
    (fun _ => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake])
    (fun _ => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake,
        PanGlobalsContextExact.cakeContextOfExact, List.map_cons, List.map_nil])
    (fun _ => by
      simp only [expToHOL, expOfHOL, compileExpExactHOL, compileExpCake])
    (fun _ => by
      simp only [compileExpCake.compileExpCakeList, compileExpExactHOLList,
        List.map_nil])
    (fun head tail ihHead ihTail hlist => by
      obtain ⟨hhead, htail⟩ := hlist
      simp only [compileExpCake.compileExpCakeList, compileExpExactHOLList,
        List.map_cons]
      rw [ihHead hhead, ihTail htail])
    True.intro
    (fun _ _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
end Flapjack
