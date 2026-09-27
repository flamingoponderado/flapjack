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
clauses.  The direct String-backed production `globalCompileExp` remains an
untagged compatibility path (its adapter to the canonical context lives beside
it in `PanGlobals.lean`); routing the executed compiler through this exact
definition is tracked by `flapjack-pxn.18.3.5.8`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL)

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

end PanGlobalsContextExact

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

end Flapjack
