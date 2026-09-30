import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
Nonrecursive constructor cases of HOL `ret_to_tail_correct` (the theorem at
pan_simpProofScript.sml:190, with suspended cases at 285-341). Each statement
retains the theorem's source non-Error hypothesis and entire evaluation pair.
The exact syntax compiler leaves these constructors unchanged. This does not
assemble the recursive Dec/Seq/If/While/Call/DecCall cases.
-/

namespace Flapjack.PanSimp.RetToTailCorrect

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

/-- Flapjack-only finite-map codec witness, forwarding the reviewed state
roundtrip; HOL has no separate declaration about this Lean representation. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- The HOL skip constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_skip {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ)  :
    (evaluateHOLFiniteState s (.skip : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.skip : ProgHOL width)) =
        evaluateHOLFiniteState s (.skip : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL break constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_break {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ)  :
    (evaluateHOLFiniteState s (.break : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.break : ProgHOL width)) =
        evaluateHOLFiniteState s (.break : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL continue constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_continue {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ)  :
    (evaluateHOLFiniteState s (.continue : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.continue : ProgHOL width)) =
        evaluateHOLFiniteState s (.continue : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL annot constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_annot {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (tag text : MlS) :
    (evaluateHOLFiniteState s (.annot tag text : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.annot tag text : ProgHOL width)) =
        evaluateHOLFiniteState s (.annot tag text : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL tick constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_tick {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ)  :
    (evaluateHOLFiniteState s (.tick : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.tick : ProgHOL width)) =
        evaluateHOLFiniteState s (.tick : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL assign constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_assign {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (kind : VarKind) (name : MlS) (value : ExpHOL width) :
    (evaluateHOLFiniteState s (.assign kind name value : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.assign kind name value : ProgHOL width)) =
        evaluateHOLFiniteState s (.assign kind name value : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL primitive constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_primitive {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (name : MlS) (operator : PrimOp) (args : List (ExpHOL width)) :
    (evaluateHOLFiniteState s (.primitive name operator args : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.primitive name operator args : ProgHOL width)) =
        evaluateHOLFiniteState s (.primitive name operator args : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL store constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_store {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (address value : ExpHOL width) :
    (evaluateHOLFiniteState s (.store address value : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.store address value : ProgHOL width)) =
        evaluateHOLFiniteState s (.store address value : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL store32 constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_store32 {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (address value : ExpHOL width) :
    (evaluateHOLFiniteState s (.store32 address value : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.store32 address value : ProgHOL width)) =
        evaluateHOLFiniteState s (.store32 address value : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL storeByte constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_storeByte {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (address value : ExpHOL width) :
    (evaluateHOLFiniteState s (.storeByte address value : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.storeByte address value : ProgHOL width)) =
        evaluateHOLFiniteState s (.storeByte address value : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL shMemLoad constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_shMemLoad {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (size : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width) :
    (evaluateHOLFiniteState s (.shMemLoad size kind name address : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.shMemLoad size kind name address : ProgHOL width)) =
        evaluateHOLFiniteState s (.shMemLoad size kind name address : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL shMemStore constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_shMemStore {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (size : OpSize) (address value : ExpHOL width) :
    (evaluateHOLFiniteState s (.shMemStore size address value : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.shMemStore size address value : ProgHOL width)) =
        evaluateHOLFiniteState s (.shMemStore size address value : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL return constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_return {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (value : ExpHOL width) :
    (evaluateHOLFiniteState s (.return value : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.return value : ProgHOL width)) =
        evaluateHOLFiniteState s (.return value : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL raise constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_raise {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (exception : MlS) (value : ExpHOL width) :
    (evaluateHOLFiniteState s (.raise exception value : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.raise exception value : ProgHOL width)) =
        evaluateHOLFiniteState s (.raise exception value : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

/-- The HOL extCall constructor case, with the original non-Error premise. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "ret_to_tail_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem retToTailCorrect_extCall {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (function : MlS) (configuration configurationLength array arrayLength : ExpHOL width) :
    (evaluateHOLFiniteState s (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).1 ≠ some .error →
      evaluateHOLFiniteState s (retToTailHOL (.extCall function configuration configurationLength array arrayLength : ProgHOL width)) =
        evaluateHOLFiniteState s (.extCall function configuration configurationLength array arrayLength : ProgHOL width) := by
  intro _h
  simp only [retToTailHOL]

end Flapjack.PanSimp.RetToTailCorrect
