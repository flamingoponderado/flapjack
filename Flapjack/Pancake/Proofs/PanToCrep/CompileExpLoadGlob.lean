module

public import Flapjack.Pancake.PanToCrep.CompileExact
public import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
public import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport

@[expose] public section

/-!
# `compile_exp_not_mem_load_glob` over the exact compiler

Exact port of HOL `compile_exp_not_mem_load_glob`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2013-2030`) over the
reviewed exact carriers: `compile_exp` is `compileExpExactHOLW`, `exps` is the
tagged `crepExpsHOL` (`crepLang exps_def`), `state_rel`/`code_rel`/`locals_rel`
are the tagged exact relations, and the word index `ad` is HOL's `word5`
(`BitVec 5`).

HOL's proof is an induction over `compile_exp_ind` showing that no clause ever
emits a `LoadGlob` node. The same structural fact is proved here as
`compileExpExactHOLW_noLoadGlob`, which does not need the three state premises;
the tagged theorem keeps them because HOL's statement has them.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Flapjack predicate: a Crep expression has no global-load node anywhere in
its `exps` subexpression list. -/
def NoLoadGlobHOL {width : Nat} [NeZero width] (expression : CrepExpHOL width) : Prop :=
  ∀ ad, CrepExpHOL.loadGlob ad ∉ crepExpsHOL expression

/-- Flapjack predicate: a Crep expression list has no global-load node in the
flattened `exps` of its members (HOL's `~MEM (LoadGlob ad) (FLAT (MAP exps es))`). -/
def NoLoadGlobListHOL {width : Nat} [NeZero width]
    (expressions : List (CrepExpHOL width)) : Prop :=
  ∀ ad, CrepExpHOL.loadGlob ad ∉ expressions.flatMap crepExpsHOL

theorem noLoadGlobListHOL_nil {width : Nat} [NeZero width] :
    NoLoadGlobListHOL ([] : List (CrepExpHOL width)) := by
  intro ad
  simp

theorem noLoadGlobListHOL_append {width : Nat} [NeZero width]
    (first second : List (CrepExpHOL width))
    (hfirst : NoLoadGlobListHOL first) (hsecond : NoLoadGlobListHOL second) :
    NoLoadGlobListHOL (first ++ second) := by
  intro ad hmem
  simp only [List.flatMap_append, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact hfirst ad hmem
  · exact hsecond ad hmem

theorem noLoadGlobListHOL_singleton {width : Nat} [NeZero width]
    (expression : CrepExpHOL width) (h : NoLoadGlobHOL expression) :
    NoLoadGlobListHOL [expression] := by
  intro ad hmem
  exact h ad (by simpa using hmem)

theorem noLoadGlobHOL_of_mem {width : Nat} [NeZero width]
    (expressions : List (CrepExpHOL width)) (expression : CrepExpHOL width)
    (hlist : NoLoadGlobListHOL expressions) (hmem : expression ∈ expressions) :
    NoLoadGlobHOL expression := by
  intro ad hgl
  exact hlist ad (List.mem_flatMap.mpr ⟨expression, hmem, hgl⟩)

theorem noLoadGlobListHOL_take {width : Nat} [NeZero width]
    (expressions : List (CrepExpHOL width)) (h : NoLoadGlobListHOL expressions)
    (count : Nat) : NoLoadGlobListHOL (expressions.take count) := by
  intro ad hmem
  obtain ⟨expression, hmemExpression, hgl⟩ := List.mem_flatMap.mp hmem
  exact h ad (List.mem_flatMap.mpr
    ⟨expression, List.mem_of_mem_take hmemExpression, hgl⟩)

theorem noLoadGlobListHOL_drop {width : Nat} [NeZero width]
    (expressions : List (CrepExpHOL width)) (h : NoLoadGlobListHOL expressions)
    (count : Nat) : NoLoadGlobListHOL (expressions.drop count) := by
  intro ad hmem
  obtain ⟨expression, hmemExpression, hgl⟩ := List.mem_flatMap.mp hmem
  exact h ad (List.mem_flatMap.mpr
    ⟨expression, List.mem_of_mem_drop hmemExpression, hgl⟩)

theorem noLoadGlobListHOL_const {width : Nat} [NeZero width] (value : BitVec width) :
    NoLoadGlobListHOL ([CrepExpHOL.const value] : List (CrepExpHOL width)) := by
  intro ad hmem
  simp [crepExpsHOL] at hmem

theorem noLoadGlobListHOL_var {width : Nat} [NeZero width] (name : Nat) :
    NoLoadGlobListHOL ([CrepExpHOL.var name] : List (CrepExpHOL width)) := by
  intro ad hmem
  simp [crepExpsHOL] at hmem

theorem noLoadGlobListHOL_varList {width : Nat} [NeZero width] (names : List Nat) :
    NoLoadGlobListHOL (names.map (CrepExpHOL.var (width := width))) := by
  induction names with
  | nil => exact noLoadGlobListHOL_nil
  | cons name names ih =>
      simp only [List.map_cons]
      exact noLoadGlobListHOL_append _ _ (noLoadGlobListHOL_var name) ih

theorem noLoadGlobListHOL_baseAddr {width : Nat} [NeZero width] :
    NoLoadGlobListHOL ([CrepExpHOL.baseAddr] : List (CrepExpHOL width)) := by
  intro ad hmem
  simp [crepExpsHOL] at hmem

theorem noLoadGlobListHOL_topAddr {width : Nat} [NeZero width] :
    NoLoadGlobListHOL ([CrepExpHOL.topAddr] : List (CrepExpHOL width)) := by
  intro ad hmem
  simp [crepExpsHOL] at hmem

theorem noLoadGlobHOL_load {width : Nat} [NeZero width] (address : CrepExpHOL width)
    (h : NoLoadGlobHOL address) : NoLoadGlobHOL (.load address) := by
  intro ad hgl
  exact h ad (by simpa [crepExpsHOL] using hgl)

theorem noLoadGlobHOL_op_add_const {width : Nat} [NeZero width]
    (left : CrepExpHOL width) (value : BitVec width) (h : NoLoadGlobHOL left) :
    NoLoadGlobHOL (.op BinOp.add [left, .const value]) := by
  intro ad hgl
  simp only [crepExpsHOL, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil] at hgl
  rcases List.mem_append.mp hgl with hgl | hgl
  · exact h ad hgl
  · simp only [List.mem_singleton] at hgl
    exact absurd hgl (by
      intro heq
      cases heq)

theorem compFieldHOL_noLoadGlob {width : Nat} [NeZero width]
    (index : Nat) (shapes : List ShapeHOL) (expressions : List (CrepExpHOL width))
    (h : NoLoadGlobListHOL expressions) :
    NoLoadGlobListHOL (compFieldHOL index shapes expressions).1 := by
  induction shapes generalizing index expressions with
  | nil => exact noLoadGlobListHOL_const 0
  | cons shape shapes ih =>
      by_cases hindex : index = 0
      · simp only [compFieldHOL, hindex, if_true]
        exact noLoadGlobListHOL_take expressions h (sizeOfShapeHOL shape)
      · simp only [compFieldHOL, hindex, if_false]
        exact ih (index - 1) _
          (noLoadGlobListHOL_drop expressions h (sizeOfShapeHOL shape))

theorem loadShapeBytesHOLW_noLoadGlob {width : Nat} [NeZero width]
    (address : BitVec width) (count : Nat) (value : CrepExpHOL width)
    (h : NoLoadGlobHOL value) :
    NoLoadGlobListHOL (loadShapeBytesHOLW address count value) := by
  induction count generalizing address with
  | zero => simpa [loadShapeBytesHOLW] using noLoadGlobListHOL_nil (width := width)
  | succ count ih =>
      simp only [loadShapeBytesHOLW]
      by_cases hzero : address == 0
      · rw [if_pos hzero]
        refine noLoadGlobListHOL_append
          ([CrepExpHOL.load value] : List (CrepExpHOL width)) _
          (noLoadGlobListHOL_singleton _ (noLoadGlobHOL_load value h))
          (ih (address + BitVec.ofNat width (width / 8)))
      · rw [if_neg hzero]
        refine noLoadGlobListHOL_append
          ([CrepExpHOL.load (CrepExpHOL.op BinOp.add [value, CrepExpHOL.const address])] :
            List (CrepExpHOL width)) _
          (noLoadGlobListHOL_singleton _
            (noLoadGlobHOL_load _ (noLoadGlobHOL_op_add_const value address h)))
          (ih (address + BitVec.ofNat width (width / 8)))

theorem noLoadGlobListHOL_cexpHeads {width : Nat} [NeZero width] :
    ∀ (entries : List (List (CrepExpHOL width))) (heads : List (CrepExpHOL width)),
      NoLoadGlobListHOL entries.flatten →
      cexpHeads entries = some heads →
      NoLoadGlobListHOL heads
  | [], heads, _, hheads => by
      simp only [cexpHeads, Option.some.injEq] at hheads
      subst hheads
      exact noLoadGlobListHOL_nil
  | entry :: entries, heads, hflat, hheads => by
      cases entry with
      | nil => simp [cexpHeads] at hheads
      | cons head tail =>
          cases hrest : cexpHeads entries with
          | none => simp [cexpHeads, hrest] at hheads
          | some restHeads =>
              simp only [cexpHeads, hrest, Option.some.injEq] at hheads
              subst hheads
              have hhead : NoLoadGlobHOL head :=
                noLoadGlobHOL_of_mem ((head :: tail) :: entries).flatten head hflat (by
                  simp only [List.flatten_cons, List.mem_append]
                  exact Or.inl (List.mem_cons_self))
              have hrest : NoLoadGlobListHOL restHeads :=
                noLoadGlobListHOL_cexpHeads entries restHeads (by
                  intro ad hmem
                  exact hflat ad (by
                    simp only [List.flatten_cons, List.flatMap_append, List.mem_append]
                    exact Or.inr hmem)) hrest
              exact noLoadGlobListHOL_append _ _
                (noLoadGlobListHOL_singleton head hhead) hrest

theorem flatten_map_eq_flatMap {α β : Type} (f : α → List β) (entries : List α) :
    (entries.map f).flatten = entries.flatMap f := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]

theorem noLoadGlobHOL_op {width : Nat} [NeZero width] (operator : BinOp)
    (arguments : List (CrepExpHOL width)) (h : NoLoadGlobListHOL arguments) :
    NoLoadGlobHOL (.op operator arguments) := by
  intro ad hgl
  have hmem : CrepExpHOL.loadGlob ad ∈ arguments.flatMap crepExpsHOL :=
    by simpa [crepExpsHOL, flatten_map_eq_flatMap] using hgl
  exact h ad hmem

theorem noLoadGlobHOL_crepOp {width : Nat} [NeZero width] (operator : CrepOp)
    (arguments : List (CrepExpHOL width)) (h : NoLoadGlobListHOL arguments) :
    NoLoadGlobHOL (.crepOp operator arguments) := by
  intro ad hgl
  have hmem : CrepExpHOL.loadGlob ad ∈ arguments.flatMap crepExpsHOL :=
    by simpa [crepExpsHOL, flatten_map_eq_flatMap] using hgl
  exact h ad hmem

theorem noLoadGlobHOL_load32 {width : Nat} [NeZero width] (address : CrepExpHOL width)
    (h : NoLoadGlobHOL address) : NoLoadGlobHOL (.load32 address) := by
  intro ad hgl
  exact h ad (by simpa [crepExpsHOL] using hgl)

theorem noLoadGlobHOL_loadByte {width : Nat} [NeZero width] (address : CrepExpHOL width)
    (h : NoLoadGlobHOL address) : NoLoadGlobHOL (.loadByte address) := by
  intro ad hgl
  exact h ad (by simpa [crepExpsHOL] using hgl)

theorem noLoadGlobHOL_cmp {width : Nat} [NeZero width] (operator : Cmp)
    (left right : CrepExpHOL width) (hleft : NoLoadGlobHOL left)
    (hright : NoLoadGlobHOL right) : NoLoadGlobHOL (.cmp operator left right) := by
  intro ad hgl
  simp only [crepExpsHOL, List.mem_append] at hgl
  rcases hgl with hgl | hgl
  · exact hleft ad hgl
  · exact hright ad hgl

theorem noLoadGlobHOL_shift {width : Nat} [NeZero width] (operator : Shift)
    (left right : CrepExpHOL width) (hleft : NoLoadGlobHOL left)
    (hright : NoLoadGlobHOL right) : NoLoadGlobHOL (.shift operator left right) := by
  intro ad hgl
  simp only [crepExpsHOL, List.mem_append] at hgl
  rcases hgl with hgl | hgl
  · exact hleft ad hgl
  · exact hright ad hgl

/-- Flapjack-specific structural fact: every `compileExpExactHOLW` result list is
    free of global loads. HOL proves the same fact inside
    `compile_exp_not_mem_load_glob` by induction over `compile_exp_ind`; this
    theorem isolates the induction and therefore has no standalone HOL
    declaration. The tagged port is `compileExpNotMemLoadGlobHOL`. -/
theorem compileExpExactHOLW_noLoadGlob {width ctxtWidth : Nat} [NeZero width]
    [NeZero ctxtWidth] (ct : PanToCrepContextExact ctxtWidth) (e : ExpHOL width) :
    NoLoadGlobListHOL (compileExpExactHOLW ct e).1 := by
  apply compileExpExactHOLW.induct (context := ct)
    (motive1 := fun e => NoLoadGlobListHOL (compileExpExactHOLW ct e).1)
    (motive2 := fun es => NoLoadGlobListHOL ((compileExpExactHOLWList ct es).flatMap Prod.fst))
  case case1 =>
    intro value
    simp only [compileExpExactHOLW]
    exact noLoadGlobListHOL_const value
  case case2 =>
    intro name shape names hlookup
    simp only [compileExpExactHOLW, hlookup]
    exact noLoadGlobListHOL_varList names
  case case3 =>
    intro name hlookup
    simp only [compileExpExactHOLW, hlookup]
    exact noLoadGlobListHOL_const 0
  case case4 =>
    intro name
    simp only [compileExpExactHOLW]
    exact noLoadGlobListHOL_const 0
  case case5 =>
    intro expressions ih
    simp only [compileExpExactHOLW]
    exact ih
  case case6 =>
    intro index expression
    dsimp only
    intro shapes hcompiled ih
    simp only [compileExpExactHOLW, hcompiled]
    exact compFieldHOL_noLoadGlob index shapes _ ih
  case case7 =>
    intro index expression
    dsimp only
    intro hnotcomb ih
    cases h : compileExpExactHOLW ct expression with
    | mk compiledExpressions compiledShape =>
        cases compiledShape with
        | comb shapes =>
            exact absurd (congrArg Prod.snd h) (hnotcomb shapes)
        | one =>
            simp only [compileExpExactHOLW, h]
            exact noLoadGlobListHOL_const 0
        | named name =>
            simp only [compileExpExactHOLW, h]
            exact noLoadGlobListHOL_const 0
  case case8 =>
    intro name fields
    simp only [compileExpExactHOLW]
    exact noLoadGlobListHOL_const 0
  case case9 =>
    intro name value
    simp only [compileExpExactHOLW]
    exact noLoadGlobListHOL_const 0
  case case10 =>
    intro shape expression address tail snd hcompiled ih
    simp only [compileExpExactHOLW, hcompiled]
    exact loadShapeBytesHOLW_noLoadGlob 0 (sizeOfShapeHOL shape) address
      (noLoadGlobHOL_of_mem _ address ih (by
        rw [hcompiled]
        exact List.mem_cons_self))
  case case11 =>
    intro shape expression snd hcompiled ih
    simp only [compileExpExactHOLW, hcompiled]
    exact noLoadGlobListHOL_const 0
  case case12 =>
    intro expression address tail hcompiled ih
    simp only [compileExpExactHOLW, hcompiled]
    exact noLoadGlobListHOL_singleton _ (noLoadGlobHOL_load32 address
      (noLoadGlobHOL_of_mem _ address ih (by
        rw [hcompiled]
        exact List.mem_cons_self)))
  case case13 =>
    intro expression hnotcons ih
    cases h : compileExpExactHOLW ct expression with
    | mk compiledExpressions compiledShape =>
        cases compiledExpressions with
        | nil =>
            simp only [compileExpExactHOLW, h]
            exact noLoadGlobListHOL_const 0
        | cons address tail =>
            cases compiledShape with
            | one => exact absurd h (hnotcons address tail)
            | comb shapes =>
                simp only [compileExpExactHOLW, h]
                exact noLoadGlobListHOL_const 0
            | named name =>
                simp only [compileExpExactHOLW, h]
                exact noLoadGlobListHOL_const 0
  case case14 =>
    intro expression address tail hcompiled ih
    simp only [compileExpExactHOLW, hcompiled]
    exact noLoadGlobListHOL_singleton _ (noLoadGlobHOL_loadByte address
      (noLoadGlobHOL_of_mem _ address ih (by
        rw [hcompiled]
        exact List.mem_cons_self)))
  case case15 =>
    intro expression hnotcons ih
    cases h : compileExpExactHOLW ct expression with
    | mk compiledExpressions compiledShape =>
        cases compiledExpressions with
        | nil =>
            simp only [compileExpExactHOLW, h]
            exact noLoadGlobListHOL_const 0
        | cons address tail =>
            cases compiledShape with
            | one => exact absurd h (hnotcons address tail)
            | comb shapes =>
                simp only [compileExpExactHOLW, h]
                exact noLoadGlobListHOL_const 0
            | named name =>
                simp only [compileExpExactHOLW, h]
                exact noLoadGlobListHOL_const 0
  case case16 =>
    intro operator expressions heads hheads ih
    simp only [compileExpExactHOLW, hheads]
    exact noLoadGlobListHOL_singleton _ (noLoadGlobHOL_op operator heads
      (noLoadGlobListHOL_cexpHeads (List.map Prod.fst (compileExpExactHOLWList ct expressions))
        heads (by
          rw [flatten_map_eq_flatMap]
          exact ih) hheads))
  case case17 =>
    intro operator expressions hheads ih
    simp only [compileExpExactHOLW, hheads]
    exact noLoadGlobListHOL_const 0
  case case18 =>
    intro operator expressions heads hheads ih
    simp only [compileExpExactHOLW, hheads]
    exact noLoadGlobListHOL_singleton _ (noLoadGlobHOL_crepOp (compilePanOp operator) heads
      (noLoadGlobListHOL_cexpHeads (List.map Prod.fst (compileExpExactHOLWList ct expressions))
        heads (by
          rw [flatten_map_eq_flatMap]
          exact ih) hheads))
  case case19 =>
    intro operator expressions hheads ih
    simp only [compileExpExactHOLW, hheads]
    exact noLoadGlobListHOL_const 0
  case case20 =>
    intro operator left right leftHead leftTail leftShape rightHead rightTail rightShape
      hright hleft ihLeft ihRight
    simp only [compileExpExactHOLW, hleft, hright]
    exact noLoadGlobListHOL_singleton _ (noLoadGlobHOL_cmp operator leftHead rightHead
      (noLoadGlobHOL_of_mem _ leftHead ihLeft (by
        rw [hleft]
        exact List.mem_cons_self))
      (noLoadGlobHOL_of_mem _ rightHead ihRight (by
        rw [hright]
        exact List.mem_cons_self)))
  case case21 =>
    intro operator left right hnotcons ihLeft ihRight
    cases hLeft : compileExpExactHOLW ct left with
    | mk leftExpressions leftShape =>
        cases hRight : compileExpExactHOLW ct right with
        | mk rightExpressions rightShape =>
            cases leftExpressions with
            | nil =>
                simp only [compileExpExactHOLW, hLeft]
                exact noLoadGlobListHOL_const 0
            | cons leftHead leftTail =>
                cases rightExpressions with
                | nil =>
                    simp only [compileExpExactHOLW, hLeft, hRight]
                    exact noLoadGlobListHOL_const 0
                | cons rightHead rightTail =>
                    exact absurd hRight (hnotcons leftHead leftTail leftShape
                      rightHead rightTail rightShape hLeft)
  case case22 =>
    intro operator left right leftHead leftTail leftShape rightHead rightTail rightShape
      hright hleft ihLeft ihRight
    simp only [compileExpExactHOLW, hleft, hright]
    exact noLoadGlobListHOL_singleton _ (noLoadGlobHOL_shift operator leftHead rightHead
      (noLoadGlobHOL_of_mem _ leftHead ihLeft (by
        rw [hleft]
        exact List.mem_cons_self))
      (noLoadGlobHOL_of_mem _ rightHead ihRight (by
        rw [hright]
        exact List.mem_cons_self)))
  case case23 =>
    intro operator left right hnotcons ihLeft ihRight
    cases hLeft : compileExpExactHOLW ct left with
    | mk leftExpressions leftShape =>
        cases hRight : compileExpExactHOLW ct right with
        | mk rightExpressions rightShape =>
            cases leftExpressions with
            | nil =>
                simp only [compileExpExactHOLW, hLeft]
                exact noLoadGlobListHOL_const 0
            | cons leftHead leftTail =>
                cases rightExpressions with
                | nil =>
                    simp only [compileExpExactHOLW, hLeft, hRight]
                    exact noLoadGlobListHOL_const 0
                | cons rightHead rightTail =>
                    exact absurd hRight (hnotcons leftHead leftTail leftShape
                      rightHead rightTail rightShape hLeft)
  case case24 =>
    simp only [compileExpExactHOLW]
    exact noLoadGlobListHOL_baseAddr
  case case25 =>
    simp only [compileExpExactHOLW]
    exact noLoadGlobListHOL_topAddr
  case case26 =>
    simp only [compileExpExactHOLW]
    exact noLoadGlobListHOL_const _
  case case27 =>
    simp only [compileExpExactHOLWList, List.flatMap_nil]
    exact noLoadGlobListHOL_nil
  case case28 =>
    intro expression expressions ihExpression ihExpressions
    simp only [compileExpExactHOLWList, List.flatMap_cons]
    exact noLoadGlobListHOL_append _ _ ihExpression ihExpressions

/-! Same-module canonical carrier witnesses for the `fmap_as_finite_support_relation`
    qualifier on `compileExpNotMemLoadGlobHOL`. Each carrier roundtrips through
    its broad counterpart. -/
namespace CompileExpLoadGlobWitnesses

theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact {width : Nat}
    [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness context

end CompileExpLoadGlobWitnesses

/-- Exact port of HOL `compile_exp_not_mem_load_glob`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2013-2030`). The typed
    capture binds `ct e s t es sh ad` and gives ONE four-conjunct premise
    (compile equation, `state_rel`, `code_rel`, `locals_rel`), right-associated;
    `es`/`sh` are free binders, not existentials, and `ad` is HOL's `word5`.
    The conclusion renders HOL's `FLAT (MAP exps es)` literally. The three
    state premises are retained because HOL's statement has them, although the
    structural fact `compileExpExactHOLW_noLoadGlob` does not need them. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_exp_not_mem_load_glob"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids]) (words_as_type_indexed_bitvec)]
theorem compileExpNotMemLoadGlobHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (ct : PanToCrepContextExact width) (e : ExpHOL width)
      (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (es : List (CrepExpHOL width)) (sh : ShapeHOL) (ad : BitVec 5),
      compileExpExactHOLW ct e = (es, sh) ∧
        panToCrepStateRelFiniteExact s t ∧
        codeRelExactHOLW ct s.code t.code ∧
        panToCrepLocalsRelFiniteExact ct s.locals t.locals →
      ¬ (CrepExpHOL.loadGlob ad ∈ (es.map crepExpsHOL).flatten) := by
  rintro ct e s t es sh ad ⟨hcompiled, -, -, -⟩
  have hfst : (compileExpExactHOLW ct e).1 = es := by rw [hcompiled]
  have hno := compileExpExactHOLW_noLoadGlob ct e
  rw [hfst] at hno
  simpa [flatten_map_eq_flatMap] using hno ad

end Flapjack
