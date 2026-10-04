import Flapjack.Pancake.Proofs.PanToWord.PanToCrepValidity
namespace Flapjack.PanToCrepCompileExpValidity
open Pancake.PanLang
/-- Internal list-length fact for the complete native compiler; no separate HOL declaration. -/
private theorem compileList_length {width : Nat} {contextWidth : Nat} [NeZero width] [NeZero contextWidth]
    (ctxt : PanToCrepContextExact contextWidth) (es : List (ExpHOL width)) :
    (compileExpExactHOLWList ctxt es).length = es.length := by
  induction es with
  | nil => simp [compileExpExactHOLWList]
  | cons e es ih => simp [compileExpExactHOLWList, ih]
/-- Internal successful-head-extraction length fact; no separate HOL declaration. -/
private theorem heads_length {α : Type} (ces : List (List α)) (es : List α)
    (h : cexpHeads ces = some es) : es.length = ces.length := by
  induction ces generalizing es with
  | nil => simpa [cexpHeads] using h.symm
  | cons cs css ih =>
    cases cs with
    | nil => simp [cexpHeads] at h
    | cons c cs =>
      cases found : cexpHeads css with
      | none => simp [cexpHeads, found] at h
      | some rest =>
        simp only [cexpHeads, found, Option.some.injEq] at h
        subst es
        simpa using ih rest found
/-- Internal mutual-induction factoring of the full source theorem below. -/
private theorem compile_valid {width : Nat} {contextWidth : Nat} [NeZero width] [NeZero contextWidth]
    (ctxt : PanToCrepContextExact contextWidth) (e : ExpHOL width) :
    everyExpHOL panopArityTwoHOL e = true →
    crepBinaryListNative (compileExpExactHOLW ctxt e).1 := by
  apply compileExpExactHOLW.induct ctxt
    (motive1 := fun e => everyExpHOL panopArityTwoHOL e = true →
      crepBinaryListNative (compileExpExactHOLW ctxt e).1)
    (motive2 := fun es => everyExpListHOL panopArityTwoHOL es = true →
      ∀ cs ∈ (compileExpExactHOLWList ctxt es).map Prod.fst, crepBinaryListNative cs)
  all_goals try solve | intros; simp_all [compileExpExactHOLW, compileExpExactHOLWList,
    everyExpHOL, everyExpListHOL, panopArityTwoHOL,
    crepBinaryListNative, crepBinaryExpNative, crepEveryExpHOL,
    crepEveryExpListHOL_iff]
  case case5 =>
    intro es ih guard
    have hv := ih (by simpa [everyExpHOL, panopArityTwoHOL] using guard)
    simp only [compileExpExactHOLW, crepBinaryListNative, List.mem_flatMap]
    intro x hx
    obtain ⟨pair, hp, hx⟩ := hx
    exact hv pair.1 (List.mem_map.mpr ⟨pair, hp, rfl⟩) x hx
  case case6 =>
    intro index expression
    dsimp only
    intro shapes shape ih guard
    have hv := ih (by simpa [everyExpHOL, panopArityTwoHOL] using guard)
    change (compileExpExactHOLW ctxt expression).2 = .comb shapes at shape
    simp only [compileExpExactHOLW, shape]
    exact everyInstOkLess_compField index shapes _ _ _ hv rfl
  case case7 =>
    intro index expression
    dsimp only
    intro notShape ih guard
    change (∀ shapes, (compileExpExactHOLW ctxt expression).2 = .comb shapes → False) at notShape
    simp only [compileExpExactHOLW]
    simp [crepBinaryListNative, crepBinaryExpNative, crepEveryExpHOL]
  case case10 =>
    intro shape expression address tail sh compiled ih guard
    have hv := ih (by simpa [everyExpHOL, panopArityTwoHOL] using guard)
    rw [compiled] at hv
    simp only [compileExpExactHOLW, compiled]
    exact everyInstOkLess_loadShape _ _ _ (hv address (List.mem_cons_self))
  case case16 =>
    intro op es heads found ih guard
    have hv := ih (by simpa [everyExpHOL, panopArityTwoHOL] using guard)
    have hh := everyInstOkLess_cexpHeads _ heads hv found
    simpa [compileExpExactHOLW, found, crepBinaryListNative,
      crepBinaryExpNative, crepEveryExpHOL, crepEveryExpListHOL_iff] using hh
  case case18 =>
    intro op es heads found ih guard
    have hg : es.length = 2 ∧ everyExpListHOL panopArityTwoHOL es = true := by
      simpa [everyExpHOL, panopArityTwoHOL] using guard
    have hh := everyInstOkLess_cexpHeads _ heads (ih hg.2) found
    have hl : heads.length = 2 := by
      rw [heads_length _ _ found, List.length_map, compileList_length, hg.1]
    simpa [compileExpExactHOLW, found, crepBinaryListNative,
      crepBinaryExpNative, crepEveryExpHOL, crepEveryExpListHOL_iff, hl] using hh
  case case28 =>
    intro expression es ih ihs guard cs member
    have hg : everyExpHOL panopArityTwoHOL expression = true ∧
        everyExpListHOL panopArityTwoHOL es = true := by
      simpa [everyExpListHOL] using guard
    simp only [compileExpExactHOLWList, List.map_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact ih hg.1
    · exact ihs hg.2 cs member
/-- Canonical imported context representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad ctxt) = ctxt :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness ctxt

/-- Full original expression validity implication (source lines 974–1007).
The input Boolean traversal is the existing constructor-for-constructor Pan
predicate: only Panop argument lists must have length two. The output uses the
shared native Prop-valued Crep predicate and membership EVERY. Context maps use
the reviewed canonical finite-support representation; all input/output binders,
original source guard, and actual compiler pair equation are retained. Context
and expression dimensions are independently quantified, as in the original
fully typed capture (alpha context and beta expression). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml"
  "every_inst_ok_less_pan_to_crep_compile_exp"
  (fmap_as_finite_support := [vars, funcs, eids])
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_panToCrepCompileExp {width : Nat} {contextWidth : Nat}
    [NeZero width] [NeZero contextWidth]
    (ctxt : PanToCrepContextExact contextWidth) (e : ExpHOL width)
    (es : List (CrepExpHOL width)) (sh : ShapeHOL)
    (guard : everyExpHOL panopArityTwoHOL e = true)
    (compiled : compileExpExactHOLW ctxt e = (es, sh)) :
    crepBinaryListNative es := by
  have valid := compile_valid ctxt e guard
  simpa only [compiled] using valid

end Flapjack.PanToCrepCompileExpValidity
