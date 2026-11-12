module

public import Flapjack.FiniteMap
public import Flapjack.HolRef
public import Flapjack.PanBst
public import Flapjack.PanEmptyLocals
public import Flapjack.PanLocalised
public import Flapjack.PanValueFlatten
public import Flapjack.Pancake.PanToCrep
public import Flapjack.Pancake.Semantics.CrepProps
public import Flapjack.Pancake.Semantics.CrepSem
public import Flapjack.Pancake.Semantics.CrepSem.HOLState
public import Flapjack.Pancake.Semantics.CrepRuntimeTarget
public import Flapjack.Pancake.Semantics.PanSem
public import Flapjack.Pancake.Semantics.PanSem.DeclContextExact
public import Flapjack.Pancake.Semantics.PanSemStateEval
public import Flapjack.Pancake.Semantics.PanCommonProps
public import Flapjack.Pancake.Semantics.PanProps
public import Flapjack.Pancake.Semantics.PanSem.ValueHOL
public import Flapjack.Pancake.PanToCrep.Compile
public import Flapjack.Pancake.PanToCrep.CompileProg
public import Flapjack.Pancake.PanToCrep.CompileExact
public import Flapjack.Pancake.PanToCrep.ContextExact
public import Flapjack.Pancake.Proofs.PanToCrep.CompileExactVarSupport
public import Flapjack.CrepeCompileExpVariables
public import Flapjack.PanToCrepMaxList

@[expose] public section

/-!
Faithful HOL-facing relations and contexts for the Pancake `pan_to_crep`
correctness proof.  The definitions here use the extensional finite-map model
from `Flapjack.FiniteMap`, rather than the list-backed executable compiler
context.
-/

namespace Flapjack

/-! HOL `pc_compile_correct` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-490`)
has quantified inputs `v`, `v1`, `res`, `s1`, `t`, and `ctxt`. Its seven
premises are `evaluate (v,v1) = (res,s1)`, `res ≠ SOME Error`, `state_rel v1 t`,
`code_rel ctxt v1.code t.code`, `excp_rel ctxt.eids v1.eshapes`,
`locals_rel ctxt v1.locals t.locals`, and `localised_prog v`. It concludes that
there exist `res1` and `t1` with the target evaluation of `(compile ctxt v,t)`;
the post-state, code, and exception relations; and the complete HOL result
case split (`NONE`, `Error` excluded, timeout, break, continue, flattened
return, bounded exception lookup, and final FFI).

The HOL proof applies `recInduct panSemTheory.evaluate_ind` and resumes all 21
source constructors: `Skip`, `Break`, `Continue`, `Annot`, `Tick`, `Assign`,
`Primitive`, `Dec`, `Store`, `Store32`, `StoreByte`, `ShMemLoad`, `ShMemStore`,
`Return`, `Raise`, `ExtCall`, `Seq`, `If`, `While`, `Call`, and `DecCall`.
The recursive induction obligations are for `Dec`, `Seq`, `If`, `While`,
`Call`, and `DecCall`; `Call` additionally splits tail-call, timeout, return,
exception, and final-FFI outcomes. These source proof branches are assembled in
`Proofs/PanToCrep/PcCompileCorrect/Assembly.lean`.

The relation hypotheses also have distinct source definitions in this same
HOL proof file: `state_rel_def` (line 45) equates total word memory, both
memory domains, clock, endianness, FFI, and address bounds while requiring
empty source structs/globals; `code_rel_def` (line 32) relates every source
code entry to `compile (ctxt_fc ...)` in target code; `excp_rel_def` (line 16)
requires equal exception-map domains and injective compiler codes; and
`locals_rel_def` (line 71) combines context well-formedness with slot lookup,
`OPT_MMAP`, flattening, and well-formed-shape obligations. The existing
`stateRel`, `codeRel`, `excpRel`, and `localsRel` definitions have analogous
logical clauses but use production `String`, `Shape`, `PanValue`, optional
memory, and `CrepRuntimeState` carriers. Their current similarity does not
discharge the exact-carrier prerequisites recorded on `.5.16.1`.

The assembled HOL-shaped theorem is in `PcCompileCorrect/Assembly.lean`.
The `stateRel` below is a production-carrier relation and does not itself
establish the exact HOL state relation. -/

/-! Flapjack analogue of HOL `globals_lookup_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:435-438`). The lookup
    algorithm uses the same 5-bit indices, shape-size count, and optional-map
    traversal. It is deliberately untagged: HOL's input is a `panSem$value`
    and a `crepSem$state` (the direct probe instantiates an
    `((8),unit) crepSem$state` with `ValWord`/`RStruct` values), whereas this
    uses the production `PanValue α` with String-backed struct/field names,
    the untagged production `panSemShapeOf`/`Shape.shapeSize` in place of HOL
    `shape_of`/`size_of_shape`, and `CrepRuntimeState α σ`, which is only a
    production projection of the HOL state. The `names_as_string` qualifier
    cannot authorize the value/shape/state carriers, and its required
    same-module `NameRanged` witness cannot be stated for an
    `Option (List (PanWordLab α))` output. Direct HOL-EVAL rows
    (`lookup_success`, `lookup_missing`, `lookup_struct`) are recorded in
    `scripts/hol-probes/globals_lookup_probe.out` and reproduced by
    `Flapjack/Test/PanToCrepGlobalsLookupParity.lean`. Exact-carrier
    replacement is tracked by `flapjack-pxn.18.3.5.8.8`.

    HOL `evaluate_nested_decs_load_globals`
    (`pan_to_crepProofScript.sml:4139-4176`) implicitly universally quantifies
    `s`, `rv`, `rvs`, `vs`, and `p`. Its four premises are successful
    `globals_lookup s rv`, the 32-cell bound on `size_of_shape (shape_of rv)`,
    distinct `vs`, and equality of `LENGTH vs` with that shape size. Its
    conclusion equates `evaluate (nested_decs vs (load_globals 0w ...) p, s)`
    with evaluation of `p` after the globals are installed, followed by the
    exact `FOLDL res_var` restoration from the original locals. Lean has the
    exact syntax helpers `loadGlobalsHOL` and `nestedDecsHOL` and positive-width
    `ValueHOL`/`CrepSemHOLState` carriers, but no full `evaluate` over
    `CrepProgHOL` and `CrepSemHOLState`, nor an exact `globals_lookup` bridge.
    The available `evalCrepClockProg` is a restricted evaluator over
    `CrepClockProg`/`CrepExp`/`CrepHolState`; this `globalsLookup` is the
    production String-backed projection described above. Neither can state the
    HOL equation or its exact premises, so no theorem tag is claimed. The exact
    `globals_lookup_def` port over the faithful carriers is the tagged
    `globalsLookupHOL` (`Proofs/PanToCrep/EvaluateNestedDecs.lean`); this
    production-carrier declaration is Flapjack-specific infrastructure and
    carries no manifest row. The faithful theorem replacement remains tracked by
    `flapjack-4ac.5.60.1`, gated on `flapjack-4ac.5.82` and
    `flapjack-pxn.18.3.5.8.8`. -/
def globalsLookup (state : CrepRuntimeState α σ) (value : PanValue α) :
    Option (List (PanWordLab α)) :=
  (List.range (Shape.shapeSize (panSemShapeOf value))).mapM
    (fun index => state.globals (BitVec.ofNat 5 index))

/-! Exact utility theorem ports used by the `pan_to_crep` proof development. -/

/-- Exact port of the duplicate Cake `EL_load_globals` theorem
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4102`). The finite
    word offset and bounded total index have the same shape as HOL's `n2w` and
    `EL`; the proof reuses the primary semantics counterpart. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "EL_load_globals"]
theorem elLoadGlobals {α : Type u}
    (n count : Nat) (address : BitVec 5) (h : n < count) :
    (loadGlobals (α := α) address count)[n]'(by
      simpa only [loadGlobals_length] using h) =
        .loadGlob (address + BitVec.ofNat 5 n) := by
  exact loadGlobals_getElem (α := α) address count n h

/-- Flapjack-specific bridge: the source-semantics shape function agrees with
    the pre-existing value shape function at the empty structure context.
    HOL has one `shape_of` function, so this bridge has no HOL original. -/
theorem panSemShapeOf_eq_panValueShape_nil (value : PanValue α) :
    panSemShapeOf value = panValueShape [] value := by
  induction value using panSemShapeOf.induct with
  | case1 _ => simp [panSemShapeOf, panValueShape]
  | case2 values ih =>
      simpa [panSemShapeOf, panValueShape] using ih
  | case3 _ _ => simp [panSemShapeOf, panValueShape]

/-! Flapjack support: `panShapeMatches` is an exact structural shape check, so
success entails equality of its two shape arguments. This is used to expose
the indexed formal/argument shape fact from `lookup_code`'s successful check. -/
/- Indexed-list form of the HOL Call premise
`LIST_REL (fun formal arg => formal.shape = shape_of arg) parameters arguments`.
The source-facing equality is kept untagged until the complete Call theorem is
ported. -/
/-! Flapjack support: `panShapeMatches` is an exact structural shape check, so
success entails equality of its two shape arguments. This is used to expose
the indexed formal/argument shape fact from `lookup_code`'s successful check. -/

mutual
  theorem panShapeMatches_eq (left right : Shape)
      (hmatch : panShapeMatches left right = true) : left = right := by
    cases left with
    | one => cases right <;> simp [panShapeMatches] at hmatch ⊢
    | named leftName =>
        cases right with
        | named rightName =>
            simp only [panShapeMatches] at hmatch
            have hname : leftName = rightName := beq_iff_eq.mp hmatch
            subst rightName
            rfl
        | one => simp [panShapeMatches] at hmatch
        | comb _ => simp [panShapeMatches] at hmatch
    | comb leftFields =>
        cases right with
        | comb rightFields =>
            simp only [panShapeMatches] at hmatch
            have hfields := panShapeListMatches_eq leftFields rightFields hmatch
            subst rightFields
            rfl
        | one => simp [panShapeMatches] at hmatch
        | named _ => simp [panShapeMatches] at hmatch

  theorem panShapeListMatches_eq (left right : List Shape)
      (hmatch : panShapeMatches.panShapeListMatches left right = true) :
      left = right := by
    cases left with
    | nil => cases right <;> simp [panShapeMatches.panShapeListMatches] at hmatch ⊢
    | cons leftHead leftTail =>
        cases right with
        | nil => simp [panShapeMatches.panShapeListMatches] at hmatch
        | cons rightHead rightTail =>
            simp only [panShapeMatches.panShapeListMatches, Bool.and_eq_true]
              at hmatch
            rcases hmatch with ⟨hhead, htail⟩
            rw [panShapeMatches_eq leftHead rightHead hhead,
              panShapeListMatches_eq leftTail rightTail htail]
end

/-! The exact HOL theorems `res_var_commutes'`, `MEM_compile_exp_vmax`,
    and `genlist_vmax_distinct_lists_compiled_exps` remain to be ported over
    the faithful finite-map and expression carriers. -/

/-- Flapjack-only optional-indexing support for HOL `load_shape_el_rel`.
    HOL's `EL` is stated without an Option because its index premise gives
    the required bound; the exact tagged statement follows below. -/
private theorem loadShapeBytes_getElemOpt_rel {width : Nat}
    (address : BitVec width) (count index : Nat)
    (value : CrepExp (BitVec width)) (hindex : index < count) :
    (loadShapeBytes address count value)[index]? =
      some (if address + CrepBytesInWord.bytesInWord *
            BitVec.ofNat width index == 0 then .load value
        else .load (.op .add [value, .const
          (address + CrepBytesInWord.bytesInWord * BitVec.ofNat width index)])) := by
  induction count generalizing address index with
  | zero => omega
  | succ count ih =>
      cases index with
      | zero => simp [loadShapeBytes]
      | succ index =>
          have htail : index < count := by omega
          rw [loadShapeBytes]
          simp only [List.getElem?_cons_succ]
          rw [ih (address + CrepBytesInWord.bytesInWord) index htail]
          have haddr :
              (address + CrepBytesInWord.bytesInWord) +
                  CrepBytesInWord.bytesInWord * BitVec.ofNat width index =
                address + CrepBytesInWord.bytesInWord *
                  BitVec.ofNat width (index + 1) := by
            rw [BitVec.ofNat_add]
            simp [BitVec.mul_add]
            ac_rfl
          simp [haddr]

/-- The fixed-stride loader emits exactly one expression per requested word.
    This is Flapjack-only support for converting optional indexing to HOL `EL`. -/
private theorem loadShapeBytes_length {width : Nat}
    (address : BitVec width) (count : Nat)
    (value : CrepExp (BitVec width)) :
    (loadShapeBytes address count value).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadShapeBytes, ih]

/-- HOL `load_shape_el_rel`: the bounded `EL` of the fixed-stride loader uses
    word offset `address + bytes_in_word * n2w index`. The dependent Lean index
    carries the HOL premise `index < count` without an Option result. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "load_shape_el_rel"]
theorem loadShapeBytes_getElem_rel {width : Nat} [NeZero width]
    (count index : Nat) (address : BitVec width)
    (value : CrepExp (BitVec width)) (hindex : index < count) :
    (loadShapeBytes address count value)[index]'(by
      simpa [loadShapeBytes_length] using hindex) =
      if address + CrepBytesInWord.bytesInWord * BitVec.ofNat width index == 0
      then .load value
      else .load (.op .add [value, .const
        (address + CrepBytesInWord.bytesInWord * BitVec.ofNat width index)]) := by
  have hopt := loadShapeBytes_getElemOpt_rel address count index value hindex
  have hvalid : index < (loadShapeBytes address count value).length := by
    simpa [loadShapeBytes_length] using hindex
  rw [List.getElem?_eq_getElem hvalid] at hopt
  exact Option.some.inj hopt

/-! Local support for `MAP_SOME_MEM_lemma`, kept in its HOL counterpart
    module. This drops the source theorem's unused Nat witness; the exact
    tagged theorem below restores that witness in its original position. -/
theorem mapFlattenMemSomeSupport {α β : Type} (f : α → Option β)
    (xs : List (List α)) (ys : List (List β)) (zs : List α) (z : α)
    (h : xs.flatten.map f = ys.flatten.map some)
    (hzs : zs ∈ xs) (hz : z ∈ zs) :
    ∃ y, f z = some y ∧ y ∈ ys.flatten := by
  have hzflat : z ∈ xs.flatten := List.mem_flatten.mpr ⟨zs, hzs, hz⟩
  have hzmap : f z ∈ xs.flatten.map f := List.mem_map.mpr ⟨z, hzflat, rfl⟩
  rw [h] at hzmap
  obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hzmap
  exact ⟨y, hfy.symm, hy⟩

/-- Faithful port of Cake `pan_to_crepProof$MAP_SOME_MEM_lemma`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4060`). The unused HOL
    existential `r` has type `num`: the source proof instantiates it with the
    flattened-list index `m` (or `LENGTH h + _`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAP_SOME_MEM_lemma"]
theorem mapSomeMemLemma {α β : Type} (f : α → Option β)
    (xs : List (List α)) (ys : List (List β)) (zs : List α) (z : α)
    (h : xs.flatten.map f = ys.flatten.map some)
    (hzs : zs ∈ xs) (hz : z ∈ zs) :
    ∃ (_r : Nat) (y : β), f z = some y ∧ y ∈ ys.flatten := by
  obtain ⟨y, hfy, hy⟩ := mapFlattenMemSomeSupport f xs ys zs z h hzs hz
  exact ⟨0, y, hfy, hy⟩

/-! HOL `shape_of_alt` and `cexp_heads_eq` remain to be ported with their
    original word-label and polymorphic list carriers, respectively. -/

/-- HOL `MAX_LIST_APPEND`: the maximum of an appended list is the maximum
    of the two constituent maxima. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAX_LIST_APPEND"]
theorem maxListAppendHol (first second : List Nat) :
    maxList (first ++ second) = max (maxList first) (maxList second) :=
  maxList_append first second

/-- HOL `MAX_LIST_NOT_MEM`: a natural number above the list maximum is not
    present in that list. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAX_LIST_NOT_MEM"]
theorem maxListNotMemHol (x : Nat) (values : List Nat)
    (h : x > maxList values) : x ∉ values :=
  maxList_not_mem x values h

/-! HOL `flookup_res_var_thm_quant` remains to be ported over a finite-map
    carrier. The former raw-function statement admitted infinite maps and
    required Boolean equality instances. -/

/-! The `mem_comp_field` proof helper over the faithful HOL carriers. -/
private theorem compFieldHOL_mem_of_index_lt {width : Nat} [NeZero width]
    (index : Nat) (shapes : List Flapjack.Pancake.PanLang.ShapeHOL)
    (expressions : List (CrepExpHOL width)) (candidate : CrepExpHOL width)
    (hindex : index < shapes.length)
    (hmem : candidate ∈ (compFieldHOL index shapes expressions).1) :
    candidate ∈ expressions := by
  induction shapes generalizing index expressions with
  | nil => simp at hindex
  | cons shape shapes ih =>
      cases index with
      | zero =>
          exact List.mem_of_mem_take (by simpa [compFieldHOL] using hmem)
      | succ index =>
          have hindex' : index < shapes.length := by simpa using hindex
          have hmem' : candidate ∈
              (compFieldHOL index shapes
                (expressions.drop
                  (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape))).1 := by
            simpa [compFieldHOL] using hmem
          exact List.mem_of_mem_drop (ih index
            (expressions.drop
              (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape)) hindex' hmem')

/-- Exact port of HOL `mem_comp_field`
    (`pan_to_crepProofScript.sml:666-672`). The value, shape, and expression
    carriers are `ValueHOL`, `ShapeHOL`, and `CrepExpHOL`; the typed capture
    `mem_comp_field_typed` (`pan_to_crep_proof_typed_probe.out:14`) gives
    `e :α crepLang$exp list` and `vs :β v list`, so the expression width α and
    the value width β are independent. HOL has the single five-part
    conjunctive premise
    `i < LENGTH vs ∧ LENGTH e = size_of_shape (shape_of (RStruct vs)) ∧
     comp_field i sh e = (es,shp) ∧ Comb sh = shape_of (RStruct vs) ∧
     MEM ce es`; the port takes that one premise and destructures it
    (task 152 item 3). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mem_comp_field"
  (words_as_type_indexed_bitvec)]
theorem memCompFieldHOLExact {width : Nat} [NeZero width]
    {valueWidth : Nat} [NeZero valueWidth]
    (shapes : List Flapjack.Pancake.PanLang.ShapeHOL) (index : Nat)
    (expressions : List (CrepExpHOL width))
    (selectedShape : Flapjack.Pancake.PanLang.ShapeHOL)
    (candidate : CrepExpHOL width) (selected : List (CrepExpHOL width))
    (values : List (ValueHOL valueWidth))
    (h : index < values.length ∧
      expressions.length =
        Flapjack.Pancake.PanLang.sizeOfShapeHOL
          (shapeOfHOLExact (.rStruct values)) ∧
      compFieldHOL index shapes expressions = (selected, selectedShape) ∧
      Flapjack.Pancake.PanLang.ShapeHOL.comb shapes =
        shapeOfHOLExact (.rStruct values) ∧
      candidate ∈ selected) :
    candidate ∈ expressions := by
  obtain ⟨hindex, _hlength, hcompiled, hshape, hmem⟩ := h
  have hshapes : shapes = values.map shapeOfHOLExact :=
    Flapjack.Pancake.PanLang.ShapeHOL.comb.inj
      (by simpa [shapeOfHOLExact] using hshape)
  have hindex' : index < shapes.length := by
    simpa [hshapes] using hindex
  have hmem' : candidate ∈ (compFieldHOL index shapes expressions).1 := by
    simpa [hcompiled] using hmem
  exact compFieldHOL_mem_of_index_lt index shapes expressions candidate hindex' hmem'

/-- Untagged curried wrapper for callers that hold the five premises
    separately; the tagged theorem takes HOL's single conjunction. -/
theorem memCompFieldHOLExact_curried {width : Nat} [NeZero width]
    {valueWidth : Nat} [NeZero valueWidth]
    (shapes : List Flapjack.Pancake.PanLang.ShapeHOL) (index : Nat)
    (expressions : List (CrepExpHOL width))
    (selectedShape : Flapjack.Pancake.PanLang.ShapeHOL)
    (candidate : CrepExpHOL width) (selected : List (CrepExpHOL width))
    (values : List (ValueHOL valueWidth))
    (hindex : index < values.length)
    (hlength : expressions.length =
      Flapjack.Pancake.PanLang.sizeOfShapeHOL
        (shapeOfHOLExact (.rStruct values)))
    (hcompiled : compFieldHOL index shapes expressions =
      (selected, selectedShape))
    (hshape : Flapjack.Pancake.PanLang.ShapeHOL.comb shapes =
      shapeOfHOLExact (.rStruct values))
    (hmem : candidate ∈ selected) :
    candidate ∈ expressions :=
  memCompFieldHOLExact shapes index expressions selectedShape candidate selected
    values ⟨hindex, hlength, hcompiled, hshape, hmem⟩

/-- Exact port of HOL `mem_comp_field_lem`
    (`pan_to_crepProofScript.sml:397-406`), which states
    `!i l es x. MEM x (FST (comp_field i l es)) ==> MEM x es \/ x = Const 0w`.
    The binder order `index`, `shapes`, `expressions`, `expression` follows
    HOL's `i`, `l`, `es`, `x`; the shape and expression carriers are the exact
    `ShapeHOL` and width-indexed `CrepExpHOL width`, and HOL's `Const 0w`
    word literal is `CrepExpHOL.const (0 : BitVec width)`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mem_comp_field_lem"
  (words_as_type_indexed_bitvec)]
theorem memCompFieldHOLExact_or_zero {width : Nat} [NeZero width]
    (index : Nat) (shapes : List Flapjack.Pancake.PanLang.ShapeHOL)
    (expressions : List (CrepExpHOL width)) (expression : CrepExpHOL width)
    (hmem : expression ∈ (compFieldHOL index shapes expressions).1) :
    expression ∈ expressions ∨ expression = CrepExpHOL.const (0 : BitVec width) := by
  induction shapes generalizing index expressions with
  | nil =>
      simp [compFieldHOL] at hmem
      exact Or.inr hmem
  | cons shape shapes ih =>
      cases index with
      | zero =>
          left
          exact List.mem_of_mem_take hmem
      | succ index =>
          have hdrop : expression ∈
              (compFieldHOL index shapes
                (expressions.drop
                  (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape))).1 := by
            simpa [compFieldHOL] using hmem
          rcases ih index
              (expressions.drop
                (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape)) hdrop with
            hinput | hzero
          · exact Or.inl (List.mem_of_mem_drop hinput)
          · exact Or.inr hzero

/-- HOL `filter_not_mem_self`: filtering a list by non-membership in that
    same list removes every element. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "filter_not_mem_self"]
theorem filter_not_mem_self {α : Type} [DecidableEq α] (l : List α) :
    l.filter (fun x => decide (x ∉ l)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp [hx]

/-! Cake `not_none_then_some` (`pan_to_crepProofScript.sml:3593`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "not_none_then_some"]
theorem option_ne_none_iff_exists {α : Type} (x : Option α) :
    x ≠ none ↔ ∃ a, x = some a := by
  constructor
  · intro h
    cases x with
    | none => exact absurd rfl h
    | some a => exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact Option.some_ne_none a

/-! Cake `mod_eq_lt_eq` (`pan_to_crepProofScript.sml:4621`): below the
modulus, reduction is the identity. The HOL conjunction of three premises is
represented by Lean's curried theorem arguments. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mod_eq_lt_eq"]
theorem mod_eq_of_lt_eq {n x m : Nat} (hn : n < x) (hm : m < x)
    (h : n % x = m % x) : n = m := by
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at h
  exact h

/-! Cake `pair_map_I` (`pan_to_crepProofScript.sml:4630`): the uncurried pair
constructor is the identity on pairs. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pair_map_I"]
theorem prod_mk_pair_eq_id {α β : Type} :
    (fun p : α × β => (p.1, p.2)) = id := by
  funext p
  cases p
  rfl

/-! The HOL proof context record used by `ctxt_fc_def`. -/
structure PanToCrepProofContext (α : Type) where
  vars : FiniteMap String (Shape × List Nat)
  funcs : FiniteMap String (List (String × Shape) × Shape)
  eids : FiniteMap String α
  vmax : Nat

/-! ### HOL `get_eids_imp_excp_rel` (Flapjack-specific; tag withdrawn since
    `flapjack-pxn.18.3.5.7.2`)

    Flapjack-specific list support for the port below: membership in a zip
    yields aligned indices (HOL `MEM_ZIP`). -/
theorem mem_zip_getElem? {names : List α} {values : List β} {key : α} {value : β}
    (h : (key, value) ∈ names.zip values) :
    ∃ i : Nat, names[i]? = some key ∧ values[i]? = some value := by
  induction names generalizing values with
  | nil => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons val values =>
          rw [List.zip_cons_cons, List.mem_cons] at h
          rcases h with h | h
          · obtain ⟨rfl, rfl⟩ := h
            exact ⟨0, rfl, rfl⟩
          · obtain ⟨i, hni, hvi⟩ := ih h
            exact ⟨i + 1, by rw [List.getElem?_cons_succ]; exact hni,
              by rw [List.getElem?_cons_succ]; exact hvi⟩

/-- Flapjack-specific support: an exception table is no longer than the
    exception-identifier count of the same declaration list. -/
theorem exceptionEntries_length_le_sizeOfEids (pc : List (Decl (BitVec width))) :
    (exceptionEntries pc).length ≤ sizeOfEids pc := by
  induction pc with
  | nil => simp [exceptionEntries, sizeOfEids]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [exceptionEntries, sizeOfEids_cons, isExnDecl] <;> omega

/-- Flapjack-specific support: `BitVec.ofNat width` is injective below
    `2 ^ width`, which is where HOL's `LESS_MOD` step is used. -/
theorem bitVecOfNat_inj {width i j : Nat} (hi : i < 2 ^ width) (hj : j < 2 ^ width)
    (h : BitVec.ofNat width i = BitVec.ofNat width j) : i = j := by
  have hmod : i % 2 ^ width = j % 2 ^ width := by
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat] using this
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod

/-- Flapjack-specific unfolding of the `get_eids_from_decls`-shaped port (currently untagged). -/
theorem panToCrepGetEidsFromDeclsHOL_eq (declarations : List (Decl (BitVec width))) :
    panToCrepGetEidsFromDeclsHOL declarations =
      FUPDATE_LIST FEMPTY
        (((exceptionEntries declarations).map Prod.fst).zip
          ((List.range ((exceptionEntries declarations).map Prod.fst).length).map
            (BitVec.ofNat width))).reverse := rfl

/-- Flapjack-specific inverse lookup fact: a successful exception-code lookup
    comes from one of the zipped source entries. -/
theorem panToCrepGetEidsFromDeclsHOL_lookup_mem
    (declarations : List (Decl (BitVec width))) (exception : ExceptionId)
    (code : BitVec width)
    (h : FLOOKUP (panToCrepGetEidsFromDeclsHOL declarations) exception = some code) :
    (exception, code) ∈ ((exceptionEntries declarations).map Prod.fst).zip
        ((List.range ((exceptionEntries declarations).map Prod.fst).length).map
          (BitVec.ofNat width)) := by
  rw [panToCrepGetEidsFromDeclsHOL_eq declarations] at h
  rcases flookupFupdateList_mem_or_base (FEMPTY : FiniteMap ExceptionId (BitVec width))
      _ exception code h with ⟨entry, hentry, hkey, hvalue⟩ | hbase
  · rw [List.mem_reverse] at hentry
    have heq : entry = (exception, code) := by
      rw [← hkey, ← hvalue]
    rwa [heq] at hentry
  · exact absurd hbase (by simp)

/-! HOL `ctxt_fc_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:25`).
    `FUPDATE_LIST` and `withShape` preserve the source definition's ZIP
    truncation and TAKE/DROP slicing, and `maxList` is Cake's `MAX_LIST`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact port over the faithful carriers is the tagged
-- `ctxtFcExactHOL` in this module; this production-carrier declaration is
-- Flapjack-specific infrastructure and carries no manifest row. The MlString
-- identifier carrier work remains tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
def ctxtFc
    (compilerFunctions : FiniteMap String (List (String × Shape) × Shape))
    (exceptionCodes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) : PanToCrepProofContext α :=
  { vars := FUPDATE_LIST FEMPTY
      (variables.zip (shapes.zip (withShape shapes names)))
    funcs := compilerFunctions
    eids := exceptionCodes
    vmax := maxList names }

/-- Flapjack-specific support for the HOL `MAX_LIST_i_genlist` step: dropping
    the first `n` entries of `List.range m` is the same as mapping `n + ·` over
    `List.range (m - n)` (used to line up `ctxt_fc`'s `with_shape` slices with
    `compileParamVars`'s per-parameter slot ranges). -/
theorem drop_range_map (m n : Nat) (h : n ≤ m) :
    (List.range m).drop n = (List.range (m - n)).map (fun index => n + index) := by
  rw [show m = n + (m - n) from (Nat.add_sub_cancel' h).symm]
  rw [List.range_add, List.drop_append_of_le_length (by simp [List.length_range])]
  simp

/-- Flapjack-specific bridge used by HOL `mk_ctxt_code_imp_code_rel`: the
    production parameter map built by `compileParamVars` and the proof-side
    `ctxt_fc` variable map agree after shifting the slot ranges by `offset`.
    This is the correspondence the HOL proof discharges with
    `gvs[ctxt_fc_def, make_vmap_def]`; HOL `make_vmap` is `panToCrepMakeVmapHOL`. -/
theorem compileParamVars_range_withShape (params : List (VarName × Shape)) (offset : Nat) :
    (compileParamVars params offset).1 =
      (params.map Prod.fst).zip
        ((params.map Prod.snd).zip
          (withShape (params.map Prod.snd)
            ((List.range (Shape.shapeSize (.comb (params.map Prod.snd)))).map
              (fun index => offset + index)))) := by
  induction params generalizing offset with
  | nil => simp [compileParamVars, withShape]
  | cons param params ih =>
      obtain ⟨name, shape⟩ := param
      simp only [compileParamVars, List.map_cons]
      rw [shapeSize_comb_cons]
      have htake :
          List.take (Shape.shapeSize shape)
              (List.map (fun index => offset + index)
                (List.range (Shape.shapeSize shape +
                  Shape.shapeSize (.comb (params.map Prod.snd))))) =
            List.map (fun index => offset + index)
              (List.range (Shape.shapeSize shape)) := by
        rw [← List.map_take, List.take_range]
        simp
      have hdrop :
          List.drop (Shape.shapeSize shape)
              (List.map (fun index => offset + index)
                (List.range (Shape.shapeSize shape +
                  Shape.shapeSize (.comb (params.map Prod.snd))))) =
            List.map (fun index => (offset + Shape.shapeSize shape) + index)
              (List.range (Shape.shapeSize (.comb (params.map Prod.snd)))) := by
        rw [← List.map_drop]
        rw [drop_range_map
          (Shape.shapeSize shape + Shape.shapeSize (.comb (params.map Prod.snd)))
          (Shape.shapeSize shape) (Nat.le_add_right _ _)]
        rw [Nat.add_sub_cancel_left]
        rw [List.map_map]
        congr 1
        funext index
        simp [Nat.add_assoc]
      simp only [withShape]
      rw [htake, hdrop, ih (offset + Shape.shapeSize shape)]
      simp only [List.zip_cons_cons]

/-- Flapjack-specific bridge used by HOL `mk_ctxt_code_imp_code_rel`: the
    production parameter map `panToCrepMakeVmapHOL` equals the `vars` field of
    the proof-side `ctxt_fc` context at the standard slot window. -/
theorem panToCrepMakeVmapHOL_eq_ctxtFcVars
    (params : List (VarName × Shape))
    (functions : FiniteMap FunName (List (VarName × Shape) × Shape))
    (exceptionCodes : FiniteMap ExceptionId α) :
    panToCrepMakeVmapHOL params =
      (ctxtFc functions exceptionCodes (params.map Prod.fst) (params.map Prod.snd)
        (panToCrepVars params)).vars := by
  simp only [panToCrepMakeVmapHOL, ctxtFc, panToCrepVars_eq]
  rw [compileParamVars_range_withShape params 0]
  simp

/-- HOL `slc_def` (`pan_to_crepProofScript.sml:2313-2315`):
    `slc vshs args = FEMPTY |++ ZIP (MAP FST vshs, args)`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn, bead flapjack-4ac.5.36):
-- the production `slc` keys by `VarName = String` and stores the raw `PanValue α`
-- payload, while HOL keys by `varname = mlstring` and stores `'a v` (whose `Val`
-- constructor carries `'a word_lab`). The `names_as_string` qualifier cannot
-- authorize the value carrier, and `PanValue` is explicitly not statement-exact
-- (`.word` stores `α`, not `'a word_lab`). Faithful exact port tracked by
-- `flapjack-pxn.18.3.5.8` (MlString names) and `flapjack-0lj` (word_lab).
-- Untagged non-Proofs def, so no theorem-map entry is possible.
def slc (parameters : List (String × Shape))
    (arguments : List (PanValue α)) : FiniteMap String (PanValue α) :=
  FUPDATE_LIST FEMPTY ((parameters.map Prod.fst).zip arguments)

private theorem updatePanValueMap_eq_FUPDATE
    (locals : VarName → Option (PanValue α)) (name : VarName)
    (value : PanValue α) :
    updatePanValueMap locals name value = FUPDATE locals (name, value) := by
  funext key
  by_cases hkey : key = name
  · subst key
    simp [updatePanValueMap, FUPDATE]
  · have hkeyName : (key == name) = false :=
      beq_eq_false_iff_ne.mpr hkey
    have hnameKey : (name == key) = false :=
      beq_eq_false_iff_ne.mpr (Ne.symm hkey)
    simp [updatePanValueMap, FUPDATE, hkeyName, hnameKey]

theorem withShapeGetElemNodupOfSlotsNodup (shapes : List Shape) (slots : List Nat)
    (index : Nat) (hslots : slots.Nodup)
    (hsize : slots.length = Shape.shapeSize (.comb shapes))
    (hindex : index < shapes.length) :
    ((withShape shapes slots)[index]'(by rw [withShape_length]; exact hindex)).Nodup := by
  rw [withShape_getElem_eq_take_drop shapes slots index hsize hindex]
  exact (List.take_sublist _ _).nodup ((List.drop_sublist _ _).nodup hslots)

theorem withShapeGetElemMemOfSlotsMem (shapes : List Shape) (slots : List Nat)
    (index slot : Nat) (hsize : slots.length = Shape.shapeSize (.comb shapes))
    (hindex : index < shapes.length)
    (hmem : slot ∈ (withShape shapes slots)[index]'
      (by rw [withShape_length]; exact hindex)) :
    slot ∈ slots := by
  rw [withShape_getElem_eq_take_drop shapes slots index hsize hindex] at hmem
  exact (List.drop_sublist _ _).subset ((List.take_sublist _ _).subset hmem)

/-- Target-state view of `tlc`: the finite map stores the HOL `word_lab`
constructor required by `locals_rel`, while the source-facing shape premise
remains `panSem$shape_of`/`is_wf_shape_v_nil`. -/
def tlcWordLab (slots : List Nat) (arguments : List (PanValue α)) :
    FiniteMap Nat (PanWordLab α) :=
  FUPDATE_LIST FEMPTY
    (slots.zip ((arguments.flatMap panValueFlatten).map PanWordLab.word))

/-! HOL `state_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:45`).
    The source Pancake state and target Crepe state agree on their memory
    domains, clock, endianness, FFI state, and address bounds; the source has
    no struct context (`s.structs = []`) and no globals (`s.globals = FEMPTY`).
    `word_lab` is a single-constructor type, so the target's raw word cells
    reconstruct the source `PanValue` cells with `PanValue.word`; a source cell
    that stored a structure could not be recovered from the target memory and
    therefore does not satisfy the relation. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact port over the faithful carriers is the tagged
-- `panToCrepStateRelFiniteExact` (`Proofs/PanToCrep/StateRelFiniteSupport.lean`);
-- this production-carrier declaration is Flapjack-specific infrastructure and
-- carries no manifest row. The MlString identifier carrier work remains tracked
-- by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
def stateRel (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ) : Prop :=
  s.memory = (fun address => some (PanValue.word (panTheWord (t.memory address)))) ∧
    s.memaddrs = t.memaddrs ∧
    s.sharedMemaddrs = t.shMemaddrs ∧ s.structs = [] ∧
    s.globals = (FEMPTY : FiniteMap VarName (PanValue α)) ∧
    s.clock = t.clock ∧ s.be = t.bigEndian ∧ s.ffi = t.ffi ∧
    s.baseAddress = t.baseAddress ∧ s.topAddress = t.topAddress

/-! The executable source state's memory is optional and carries `PanValue`,
whereas HOL `panSem$state.memory` is total and carries `word_lab`.  Under
`stateRel`, every source cell is exactly the target's word cell and the
`memaddrs`/endianness fields agree.  These untagged adapters expose that
boundary for the fixed RV64 source evaluator's byte and 32-bit loads.  They are
case lemmas, not claims that the enclosing `pc_compile_correct` proof is done. -/

/-- A source `LoadByte (Const address)` under the Pan-to-Crep state relation
uses the state-owned address domain, byte order, and total word memory found in
the related target state.  This is a RISC-V evaluator-case adapter, not a
standalone HOL theorem. -/
theorem panToCrepSourceLoadByteHOLCase
    [NeZero 64] [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0]
    [OfNat (RiscV.Word 64) 1] [OfNat (RiscV.Word 64) 2]
    [OfNat (RiscV.Word 64) 3] [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)]
    [Sub (RiscV.Word 64)] [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) (hstate : stateRel source target) :
    evalPanSemStateExp source (.loadByte (.const address)) =
      (panMemLoadByteHOL (width := 64)
        (fun current => match target.memory current with
          | .word value => .word value)
        (fun current =>
          (source.memaddrs current && panValueWordDefined source.memory current) = true)
        source.be address).map
          (fun byte => PanValue.word (BitVec.ofNat 64 byte.toNat)) := by
  rcases hstate with ⟨hmemory, _, _, _, _, _, _, _, _, _⟩
  simp only [evalPanSemStateExp, evalPanValueExp]
  change ((panSemBitVec64MemoryAccess source).readByte
      (panSemBitVec64MemoryAccess source).domain source.memory
      panSemBitVec64BytesInWord address).map PanValue.word = _
  rw [panSemBitVec64ReadByte_eq_panMemLoadByteHOL source source.memory address]
  have hmemoryView :
      (fun current => match target.memory current with
        | .word value => .word value) = panValueWordHOL source.memory := by
    funext current
    simp [panValueWordHOL, hmemory, panTheWord]
  rw [hmemoryView]
  have hdomainView :
      (fun current =>
        (source.memaddrs current && decide (panValueWordDefined source.memory current = true)) = true) =
      (fun current =>
        (source.memaddrs current && panValueWordDefined source.memory current) = true) := by
    funext current
    simp
  simp only [hdomainView]
  simp only [Option.map_map]
  rfl

/-- A source `Load32 (Const address)` under the Pan-to-Crep state relation
uses the related target's word cells, address domain, and byte order.  This is
an untagged RISC-V evaluator-case adapter. -/
theorem panToCrepSourceLoad32HOLCase
    [NeZero 64] [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0]
    [OfNat (RiscV.Word 64) 1] [OfNat (RiscV.Word 64) 2]
    [OfNat (RiscV.Word 64) 3] [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)]
    [Sub (RiscV.Word 64)] [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) (hstate : stateRel source target) :
    evalPanSemStateExp source (.load32 (.const address)) =
      (panMemLoad32HOL (width := 64)
        (fun current => match target.memory current with
          | .word value => .word value)
        (fun current =>
          (source.memaddrs current && panValueWordDefined source.memory current) = true)
        source.be address).map
          (fun value => PanValue.word (BitVec.ofNat 64 value.toNat)) := by
  rcases hstate with ⟨hmemory, _, _, _, _, _, _, _, _, _⟩
  simp only [evalPanSemStateExp, evalPanValueExp]
  change ((panSemBitVec64MemoryAccess source).read32
      (panSemBitVec64MemoryAccess source).domain source.memory
      panSemBitVec64BytesInWord address).map PanValue.word = _
  rw [panSemBitVec64Read32_eq_panMemLoad32HOL source source.memory address]
  have hmemoryView :
      (fun current => match target.memory current with
        | .word value => .word value) = panValueWordHOL source.memory := by
    funext current
    simp [panValueWordHOL, hmemory, panTheWord]
  rw [hmemoryView]
  have hdomainView :
      (fun current =>
        (source.memaddrs current && decide (panValueWordDefined source.memory current = true)) = true) =
      (fun current =>
        (source.memaddrs current && panValueWordDefined source.memory current) = true) := by
    funext current
    simp
  simp only [hdomainView]
  simp only [Option.map_map]
  rfl

/-- Source-shaped port of HOL `state_rel_globals[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:65`), a projection of
    `state_rel`.

    FLAPJACK-SPECIFIC (not an exact HOL port; review `flapjack-pxn.18.3.7.1.3`): the
    hypothesis is the Flapjack-specific `stateRel` over production `PanSemState`/
    `CrepRuntimeState`, not HOL `state_rel`, and the conclusion is stated over the
    production carrier `FiniteMap VarName (PanValue α)` rather than HOL
    `varname |-> 'a v`. The mismatch is not limited to the String-vs-`mlstring` domain
    key (`VarName` vs `varname`): `stateRel` also relates an optional `PanValue`
    source memory to a total `word_lab` target memory and the value type is
    `PanValue α` vs `'a v` (see `stateRel_structs` above and the `state_rel_def` note),
    so the `(names_as_string := ...)` qualifier does not apply. The exact projection
    is the tagged `panToCrepStateRelFiniteExact_globals`
    (`Proofs/PanToCrep/StateRelFiniteSupport.lean`); this production-carrier
    declaration is Flapjack-specific infrastructure and carries no manifest row.
    Carrier work remains tracked by `flapjack-pxn.18.3.5.8`. -/
theorem stateRel_globals (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ)
    (hrel : stateRel s t) : s.globals = (FEMPTY : FiniteMap VarName (PanValue α)) := by
  rcases hrel with ⟨_, _, _, _, hglobals, _, _, _, _, _⟩
  exact hglobals

/-- Canonicalizing the target with `riscv64CrepRuntimeTarget` does not change
    the state relation: it only edits fields (`bytesInWord`, `memoryModel`,
    `ffiContext`) that `stateRel` does not constrain, together with `bigEndian`,
    which agrees with the source once the source is little-endian. Flapjack-only
    convenience for the canonical RISC-V 64 target; no HOL original. -/
theorem stateRel_riscv64CrepRuntimeTarget_iff
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (hbe : base.bigEndian = false) :
    stateRel source (riscv64CrepRuntimeTarget base) ↔ stateRel source base := by
  constructor
  · intro hrel
    unfold stateRel at hrel ⊢
    obtain ⟨hm, hma, hsm, hst, hg, hcl, hbe', hffi, hba, hta⟩ := hrel
    exact ⟨hm, hma, hsm, hst, hg, hcl, hbe'.trans hbe.symm, hffi, hba, hta⟩
  · intro hrel
    unfold stateRel at hrel ⊢
    obtain ⟨hm, hma, hsm, hst, hg, hcl, hbe', hffi, hba, hta⟩ := hrel
    exact ⟨hm, hma, hsm, hst, hg, hcl, hbe'.trans hbe, hffi, hba, hta⟩

/-- Flapjack-specific bridge for the target memory representation. HOL
    `crepSem$state.memory` and executable `CrepRuntimeState.memory` are both
    total `word → word_lab` functions; the separate `memaddrs` set guards
    accessible addresses (`crepSemScript.sml:24-26`). This relation states
    equality of the complete memories and is the target-side hypothesis of
    the `mem_load_def` correspondence below. -/
def crepMemoryRel (state : CrepRuntimeState α σ) (total : α → PanWordLab α) : Prop :=
  state.memory = total

/-- First branch of HOL `mem_load_def`
    (`cakeml/pancake/semantics/crepSemScript.sml:48-51`): a load at an address in
    `memaddrs` returns the total memory cell, reconstructed as a `word_lab`. -/
theorem crepRuntimeLoad_eq_some_of_crepMemoryRel {state : CrepRuntimeState α σ}
    {total : α → PanWordLab α} (hrel : crepMemoryRel state total) {address : α}
    (hvalid : state.memaddrs address = true) :
    crepRuntimeLoad state address = some (panTheWord (total address)) := by
  change state.memory = total at hrel
  rw [crepRuntimeLoad]
  simp [hvalid, hrel]

/-- Second branch of HOL `mem_load_def`: an address outside `memaddrs` has no
    loadable cell. -/
theorem crepRuntimeLoad_eq_none_of_memaddrs_false {state : CrepRuntimeState α σ}
    {address : α} (hinvalid : state.memaddrs address = false) :
    crepRuntimeLoad state address = none := by
  rw [crepRuntimeLoad]
  simp [hinvalid]

/-- First branch of HOL `panSem$mem_store`
    (`cakeml/pancake/semantics/panSemScript.sml:373-378`) as used by
    `crepSem$evaluate`'s store case: a store at an address in `memaddrs`
    succeeds and updates exactly that address, keeping the rest of the memory
    function. -/
theorem crepRuntimeStore_eq_some_of_memaddrs_true [BEq α]
    {state : CrepRuntimeState α σ} {address value : α}
    (hvalid : state.memaddrs address = true) :
    crepRuntimeStore state address value =
      some { state with memory := updateCrepRuntimeMemory state.memory address (.word value) } := by
  rw [crepRuntimeStore]
  simp [hvalid]

/-- Second branch of HOL `panSem$mem_store`: a store outside `memaddrs` fails. -/
theorem crepRuntimeStore_eq_none_of_memaddrs_false [BEq α]
    {state : CrepRuntimeState α σ} {address value : α}
    (hinvalid : state.memaddrs address = false) :
    crepRuntimeStore state address value = none := by
  rw [crepRuntimeStore]
  simp [hinvalid]

/-- Storing a value preserves `crepMemoryRel` when the total memory function is
    updated at the same address: the stored cell becomes the `word_lab` of the
    value, and every other guarded address is untouched. -/
theorem crepMemoryRel_store [BEq α] {state : CrepRuntimeState α σ}
    {total : α → PanWordLab α} (hrel : crepMemoryRel state total) {address : α}
    (_hvalid : state.memaddrs address = true) (value : α) :
    crepMemoryRel
      { state with memory := updateCrepRuntimeMemory state.memory address (.word value) }
      (fun current => if current == address then .word value else total current) := by
  unfold crepMemoryRel at hrel ⊢
  rw [hrel]
  funext current
  by_cases hsame : current == address
  · simp [updateCrepRuntimeMemory, hsame]
  · simp [updateCrepRuntimeMemory, hsame]

/-- HOL `locals_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:71`):
    the proof context's variable map is well formed, and every live source
    variable is recovered in the target locals by mapping its slot list through
    the target map, with the flattened value equal to the produced word list and
    the variable's shape well formed against the empty struct context. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId` = `String` (or embeds a
-- `PanToCrepProofContext`/`PanToCrepHOLContext` whose finite maps are `String`-keyed),
-- while HOL `pan_to_crepProofScript.sml` keys names by `funname`/`varname`/`eid` =
-- `mlstring`. The exact port over the faithful carriers is the tagged
-- `panToCrepLocalsRelFiniteExact` (`Proofs/PanToCrep/StateRelFiniteSupport.lean`);
-- this production-carrier declaration is Flapjack-specific infrastructure and
-- carries no manifest row. The MlString identifier carrier work remains tracked
-- by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
def localsRel (context : PanToCrepProofContext α)
    (sLocals : FiniteMap String (PanValue α))
    (tLocals : FiniteMap Nat (PanWordLab α)) : Prop :=
  noOverlap context.vars ∧ ctxtMax context.vmax context.vars ∧
    ∀ vname v, FLOOKUP sLocals vname = some v →
      ∃ ns vs, FLOOKUP context.vars vname = some (panValueShape [] v, ns) ∧
        ns.mapM (FLOOKUP tLocals) = some vs ∧
        (panValueFlatten v).map PanWordLab.word = vs ∧
        isWfShape [] (panValueShape [] v) = true

/-! Source-reviewed disposition of HOL
    `evaluate_shape_invariant_ret_inst`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:3016`). HOL assumes the
    exact result equation `evaluate (p, s) = (SOME v, s')`, source/target
    `state_rel s t`, and `locals_rel ctxt s.locals t_locs`; it concludes that
    the `Return` payload or `Exception` payload in `v` satisfies
    `is_wf_shape_v_nil`. Its proof uses HOL's
    `evaluate_is_wf_shape_invariant` to transfer the state invariant through
    whole-program evaluation, then `locals_rel_wf_shape` and the HOL
    `state_rel` fields to establish its premises.

    The source-reviewed exact port is now tagged in
    `PanToCrep/StateRelFiniteSupport.lean` as
    `panToCrepFiniteEvaluateShapeInvariantRetInst`. It preserves HOL's three
    premises and Return/Exception conclusion over the exact PanSem and Crep
    carriers. Its input facts come from the tagged
    `panToCrepLocalsRelWfShapeFiniteExact` theorem and exact `state_rel` fields;
    the target `t_locs` map stays independent of target state `t`.

    The evaluator premise has HOL's successful-result semantics, not just its
    pair shape. `evaluateHOLFiniteState` uses classical choice only to supply
    Lean membership deciders for `memaddrs` and `shMemaddrs`. The outer
    recursive assembly marker is proved total by
    `evalPanSemRecursiveCallFiniteContext_total`, and
    `evaluateHOLFinite_ne_none` proves the wrapper's `(none, state)` fallback
    unreachable. `evaluateHOLFiniteResult_eq_iff` connects pair equality to a
    successful evaluator output; the kernel-checked 66-case
    `evalPanSemRecursiveCallFiniteContext_projection` then identifies its
    result and post-state with `evalPanSemRecursiveCallContextHOLExact` on the
    canonical finite-map projection. All 21 evaluator clauses were compared
    with `panSemScript.sml:556-761`; nonrecursive clauses use the reviewed
    exact helpers and reconstruct finite-support post-states. The separate
    tagged `evaluateIsWfShapeInvariantFiniteExact` in
    `PanProps/EvaluateResultInvariant.lean` supplies the whole-program result
    invariant. Bead `flapjack-4ac.5.83` tracks this final theorem path and its
    invariant/local-relation dependencies; it remains open pending coordinator
    acceptance.
    The expression-level prerequisite `eval_is_wf_shape_v` is tagged over the
    reviewed finite-map carrier in `PanProps/EvalInvariant.lean`.

    Separate source-reviewed disposition for HOL
    `evaluate_shape_invariant_ret_inst2` (`pan_to_crepProofScript.sml:3031-3044`):
    its five premises are `OPT_MMAP (eval s) argexps = SOME args`, successful
    `lookup_code s.code fname args = SOME (p2,newlocals,rsh)`, successful
    evaluation of `p` from `dec_clock s` with `newlocals`, `state_rel s t`,
    and `locals_rel ctxt s.locals t_locs`. It concludes the same Return or
    Exception payload `is_wf_shape_v_nil` disjunction, with true for other
    results. The proof uses `lookup_code_wf_shape_invariant_step` to establish
    the newly bound locals invariant before `evaluate_is_wf_shape_invariant`;
    these are proved facts, not additional theorem premises.
    This second theorem remains untagged while its distinct port is tracked by
    `flapjack-4ac.5.47.1`: it also needs the exact successful
    `OPT_MMAP (eval s)` and `lookup_code` premises, the `dec_clock`/locals update,
    and code/local facts that establish well-formedness of `newlocals`. That
    bead depends on `flapjack-4ac.3.52.1`, this theorem-path bead
    `flapjack-4ac.5.83`, and exact PanSem state/name carriers. The exact lookup
    invariant is tracked separately by `flapjack-4ac.4.66.1`. -/

/-! Execute the finite-map compiler with the HOL proof context. Every map is
    passed directly to `compileProgHOL`; no queried-name projection to an
    `InfoMap` is performed. -/
def compileCodeRelProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α] (context : PanToCrepProofContext α) (program : Prog α) :
    CrepProg α :=
  compileProgHOL
    { vars := context.vars, funcs := context.funcs, eids := context.eids,
      vmax := context.vmax }
    program

/-! Flapjack's code relation, shaped after HOL `code_rel_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:32`). It quantifies over
    every source code entry, requires localisation and the exact
    parameter/return-shape lookup in `ctxt.funcs`, derives parameter slots
    from `GENLIST I (size_of_shape (Comb shs))`, and constructs the target
    context with `ctxt_fc`.

    This production relation is untagged: it uses generic word values,
    String identifiers, and production syntax rather than the HOL carriers.  The
    exact port over the faithful carriers is the tagged `codeRelExactHOLW`
    (`Proofs/PanToCrep/CodeRelExact.lean`); this production-carrier declaration
    is Flapjack-specific infrastructure and carries no manifest row. -/

def codeRel [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α)) : Prop :=
  ∀ function variableShapes program returnShape,
    FLOOKUP sourceCode function = some (variableShapes, program, returnShape) →
      localisedProg program ∧
      FLOOKUP context.funcs function = some (variableShapes, returnShape) ∧
      let variables := variableShapes.map Prod.fst
      let shapes := variableShapes.map Prod.snd
      let names := List.range (Shape.shapeSize (.comb shapes))
      let nextContext := ctxtFc context.funcs context.eids variables shapes names
      FLOOKUP targetCode function = some
        (names, compileCodeRelProg nextContext program)

/-! The exact HOL lemmas `compile_exp_not_mem_load_glob` and
    `rewritten_context_unassigned` remain to be ported over the faithful carriers. -/

/-- Exact-carrier port of HOL `first_compile_to_crep_all_distinct`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4566-4573`). The input
    and output have the exact `DeclHOL`/`CrepProgHOL` carriers; the premise and
    conclusion are the HOL `ALL_DISTINCT (MAP FST ...)` clauses rendered as
    `List.Nodup`. The only representation qualifier is the standard positive
    type-indexed word to `BitVec width` translation. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml"
  "first_compile_to_crep_all_distinct" (words_as_type_indexed_bitvec)]
theorem firstCompileToCrepAllDistinctExact {width : Nat} [NeZero width]
    (declarations : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (hdistinct :
      (Flapjack.Pancake.PanLang.functionsHOL declarations).map Prod.fst |>.Nodup) :
    ((show List (Flapjack.Pancake.PanLang.MlS × List Nat × CrepProgHOL width) from
        compileToCrepExactHOLW declarations).map Prod.fst).Nodup := by
  simpa [compileToCrepExactHOLW, List.map_map, Function.comp_def] using hdistinct

/-! Flapjack-specific finite-map support: reversing an association list before
    `FUPDATE_LIST` makes the first source occurrence win, exactly like
    `List.lookup` (HOL `ALOOKUP`). This is list infrastructure, not a standalone
    HOL theorem port. -/
theorem FLOOKUP_FUPDATE_LIST_reverse_eq_lookup [BEq α] [LawfulBEq α]
    (entries : List (α × β)) (key : α) :
    FLOOKUP (FUPDATE_LIST FEMPTY entries.reverse) key = List.lookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨entryKey, entryValue⟩ := entry
      rw [List.reverse_cons, FUPDATE_LIST_append, FUPDATE_LIST_cons,
        FUPDATE_LIST_nil, FLOOKUP_update, List.lookup_cons]
      by_cases h : entryKey = key
      · subst h
        simp
      · have h1 : (entryKey == key) = false := beq_eq_false_iff_ne.mpr h
        have h2 : (key == entryKey) = false :=
          beq_eq_false_iff_ne.mpr (fun he => h he.symm)
        simp [h1, h2, ih]

/-- Flapjack-specific finite-map support: the HOL-equality `FUPDATE_LIST_HOL`
    fold over a reversed association list agrees with `List.lookup`, i.e. the
    first source occurrence wins, exactly like HOL `alist_to_fmap`. -/
private theorem fupdateListHOL_reverse_eq_foldr {α β : Type} [DecidableEq α]
    (entries : List (α × β)) :
    FUPDATE_LIST_HOL (FEMPTY : FiniteMap α β) entries.reverse =
      List.foldr (fun entry map => FUPDATE_HOL map entry) FEMPTY entries := by
  simp only [FUPDATE_LIST_HOL, List.foldl_reverse]

theorem FUPDATE_LIST_HOL_reverse_apply_eq_lookup [DecidableEq α] [BEq α]
    [LawfulBEq α] (entries : List (α × β)) (key : α) :
    (FUPDATE_LIST_HOL (FEMPTY : FiniteMap α β) entries.reverse) key =
      List.lookup key entries := by
  rw [fupdateListHOL_reverse_eq_foldr]
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨entryKey, entryValue⟩ := entry
      rw [List.foldr_cons, List.lookup_cons]
      by_cases h : key = entryKey
      · subst h
        simp [FUPDATE_HOL]
      · have h1 : (key == entryKey) = false := beq_eq_false_iff_ne.mpr h
        simp [FUPDATE_HOL, h, h1, ih]

/-- Flapjack-specific list fact: mapping a key-preserving projection through an
    association list commutes with `List.lookup` (the list-level `ALOOKUP_MAP`
    step used by HOL inside `mk_ctxt_code_imp_code_rel`). -/
theorem lookup_map_preserveFst [BEq α] [LawfulBEq α] (functions : List (α × β))
    (project : β → γ) (key : α) :
    List.lookup key (functions.map (fun entry => (entry.1, project entry.2))) =
      (List.lookup key functions).map project := by
  induction functions with
  | nil => rfl
  | cons entry functions ih =>
      obtain ⟨entryKey, entryValue⟩ := entry
      rw [List.map_cons, List.lookup_cons, List.lookup_cons]
      by_cases h : (key == entryKey) = true
      · simp [h]
      · simp [h, ih]

/-- Flapjack-specific lookup link for HOL `make_funcs`: a source function entry
    (name, params, body, return) is visible in the `make_funcs` finite map with
    the parameter list and return shape (the body is dropped). -/
theorem makeFuncsHOL_lookup_of_lookup
    (functions : List (FunName × List (VarName × Shape) × Prog α × Shape))
    (start : FunName) (vshs : List (VarName × Shape)) (prog : Prog α) (rshape : Shape)
    (h : List.lookup start functions = some (vshs, (prog, rshape))) :
    FLOOKUP (makeFuncsHOL functions) start = some (vshs, rshape) := by
  have hrewrite : FLOOKUP (makeFuncsHOL functions) start =
      List.lookup start
        (functions.map (fun entry => (entry.1, (entry.2.1, entry.2.2.2)))) := by
    rw [makeFuncsHOL]
    exact FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _
  rw [hrewrite, lookup_map_preserveFst
    (project := fun value : List (VarName × Shape) × Prog α × Shape =>
      (value.1, value.2.2))]
  rw [h]
  rfl

/-- `state_rel` records that source and target ffi states coincide; installing the
    same `call_FFI` result on both therefore preserves the whole relation (the
    other components are untouched, so they reduce definitionally). -/
theorem stateRel_ffiUpdate (source : PanSemState α (FfiState σ))
    (target : CrepRuntimeState α σ) (ffi : FfiState σ)
    (hrel : stateRel source target) :
    stateRel { source with ffi := ffi } { target with ffi := ffi } := by
  unfold stateRel at hrel ⊢
  obtain ⟨hm, hma, hsm, hst, hg, hcl, hbe, hffi, hba, hta⟩ := hrel
  exact ⟨hm, hma, hsm, hst, hg, hcl, hbe, rfl, hba, hta⟩

/-- Failing-read target-evaluation step for `ExtCall`: a failed configuration or
    array read returns `Error` with the target state unchanged (HOL `_ => (SOME
    Error, s)`), independently of the ffi state, and therefore also for a source
    state related by `stateRel`. -/
theorem crepRuntimeExtCallValues_stateRel_error
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (_hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (h : riscv64ReadByteArray base configuration configurationLength.toNat = none ∨
         riscv64ReadByteArray base array arrayLength.toNat = none) :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.error, riscv64CrepRuntimeTarget base) :=
  crepRuntimeExtCallValues_target_error base function configuration
    configurationLength array arrayLength h

/-- Source/target dispatch equation for `ExtCall` on the canonical
    RISC-V 64 target.  Given `stateRel source (riscv64CrepRuntimeTarget base)` and
    both argument reads, the production `crepRuntimeExtCallValues` step follows
    the Lean `callFfi` (HOL `call_FFI`) on the *source* ffi state: `FFI_return`
    yields `Normal` with the returned bytes written back and the returned ffi
    installed on the target, while `FFI_final` yields `FinalFFI` unchanged.  The
    separate `stateRel_ffiUpdate` lemma covers an ffi-only update; the write-back
    post-state is `crepRuntimeExtCallValues_stateRel_returned` (and the assembled
    dispatched form is `crepRuntimeExtCallValues_stateRel_dispatch_returned`).
    The failing-read case is `crepRuntimeExtCallValues_stateRel_error`, so the
    equations cover every production `ExtCall` dispatch outcome. -/
theorem crepRuntimeExtCallValues_stateRel_dispatch
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (configurationBytes arrayBytes : List UInt8)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configuration configurationLength.toNat =
      some configurationBytes)
    (ha : riscv64ReadByteArray base array arrayLength.toNat = some arrayBytes) :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (match callFfi source.ffi (.extCall function) configurationBytes arrayBytes with
       | .returned ffi bytes =>
           (.normal, riscv64WriteState { base with ffi := ffi } array bytes)
       | .final event => (.finalFfi event, riscv64CrepRuntimeTarget base)) := by
  have hffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  rw [crepRuntimeExtCallValues_target_dispatch base function configuration
    configurationLength array arrayLength configurationBytes arrayBytes hc ha, hffi]
  rfl

/-- Post-state `stateRel` for the `FFI_return` write-back branch of `ExtCall`.
    Given the source/target relation, the source `write_bytearray`
    (`panSemWriteBytearray` over the source memory) and the target
    `riscv64WriteState` (HOL `write_bytearray` over the canonical RISC-V target)
    remain related, with the returned ffi installed on both.  The memory
    conjunct is `panSemWriteBytearray_target_eq_riscv` (valid for every memory
    domain, including the HOL failed-store fallback); the remaining conjuncts are
    unchanged target fields.  This is the write-back companion of
    `stateRel_ffiUpdate`; the dispatched step result is
    `crepRuntimeExtCallValues_stateRel_dispatch_returned`. -/
theorem crepRuntimeExtCallValues_stateRel_returned
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (array : RiscV.Word 64) (bytes : List UInt8) (ffi : FfiState σ)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base)) :
    stateRel
      { source with
        memory := panSemWriteBytearray
          (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
          (riscv64PanValueFfiContext base.shMemaddrs) source.memory
          (8 : RiscV.Word 64) array bytes,
        ffi := ffi }
      (riscv64WriteState { base with ffi := ffi } array bytes) := by
  unfold stateRel at hstate ⊢
  obtain ⟨hm, hma, hsm, hst, hg, hcl, hbe, _hffi0, hba, hta⟩ := hstate
  have hmView : source.memory = panValueMemoryView base.memory := by
    rw [hm]; rfl
  have hmemT : (riscv64WriteState { base with ffi := ffi } array bytes).memory =
      (riscv64WriteState base array bytes).memory := by
    rw [riscv64WriteState_withFfi]
  have hffiT : (riscv64WriteState { base with ffi := ffi } array bytes).ffi = ffi := by
    rw [riscv64WriteState_withFfi]
  have hmaT : (riscv64WriteState { base with ffi := ffi } array bytes).memaddrs =
      base.memaddrs := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have hsmT : (riscv64WriteState { base with ffi := ffi } array bytes).shMemaddrs =
      base.shMemaddrs := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have hclkT : (riscv64WriteState { base with ffi := ffi } array bytes).clock =
      base.clock := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have hbeT : (riscv64WriteState { base with ffi := ffi } array bytes).bigEndian =
      false := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have hbaT : (riscv64WriteState { base with ffi := ffi } array bytes).baseAddress =
      base.baseAddress := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  have htaT : (riscv64WriteState { base with ffi := ffi } array bytes).topAddress =
      base.topAddress := by
    rw [riscv64WriteState_withFfi, riscv64WriteState_eq_setMemory]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmView, panSemWriteBytearray_target_eq_riscv base array bytes, hmemT]
    rfl
  · rw [hmaT]; exact hma
  · rw [hsmT]; exact hsm
  · exact hst
  · exact hg
  · rw [hclkT]; exact hcl
  · rw [hbeT]; exact hbe
  · rw [hffiT]
  · rw [hbaT]; exact hba
  · rw [htaT]; exact hta

/-- The dispatched production `ExtCall` step when `call_ffi` returns
    (`FFI_return`): the target step is `Normal` with the returned bytes written
    back, and the source/target post-states are related (`stateRel`).  Connects
    the read/handler premises of `crepRuntimeExtCallValues_target_returned` to
    the post-state relation of `crepRuntimeExtCallValues_stateRel_returned`. -/
theorem crepRuntimeExtCallValues_stateRel_dispatch_returned
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (configurationBytes arrayBytes : List UInt8) (ffi : FfiState σ)
    (bytes : List UInt8)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configuration configurationLength.toNat =
      some configurationBytes)
    (ha : riscv64ReadByteArray base array arrayLength.toNat = some arrayBytes)
    (hr : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .returned ffi bytes) :
    (crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.normal, riscv64WriteState { base with ffi := ffi } array bytes)) ∧
    stateRel
      { source with
        memory := panSemWriteBytearray
          (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
          (riscv64PanValueFfiContext base.shMemaddrs) source.memory
          (8 : RiscV.Word 64) array bytes,
        ffi := ffi }
      (riscv64WriteState { base with ffi := ffi } array bytes) :=
  ⟨crepRuntimeExtCallValues_target_returned base function configuration
      configurationLength array arrayLength configurationBytes arrayBytes hc ha
      ffi bytes hr,
   crepRuntimeExtCallValues_stateRel_returned source base array bytes ffi hstate⟩

/-- Four-local production `ExtCall` wrapper dispatch.  The actual Crep runtime
    entry point `crepRuntimeExtCall` looks the four arguments up in the target
    `locals` (Nat-indexed, the target image of HOL `FLOOKUP s.locals`), reads the
    configuration/array bytes from the target memory, and runs the same
    `crepRuntimeExtCallValues` step.  Given those four local lookups (each holding
    a `.word`) and the canonical-target argument reads, the wrapper's `FFI_return`
    result is `Normal` with the returned bytes written back, and the source
    `PanSemState` (`panSemWriteBytearray` over the source memory) and the target
    `riscv64WriteState` post-states stay related, with the returned ffi installed
    on both.  This is the four-local companion of
    `crepRuntimeExtCallValues_stateRel_dispatch_returned`: the source post-state is
    built by the theorem, not assumed.  Flapjack-only bridge (no HOL original). -/
theorem crepRuntimeExtCall_stateRel_dispatch_returned
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (configurationBytes arrayBytes : List UInt8) (ffi : FfiState σ)
    (bytes : List UInt8)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configurationValue
      configurationLengthValue.toNat = some configurationBytes)
    (ha : riscv64ReadByteArray base arrayValue arrayLengthValue.toNat =
      some arrayBytes)
    (hr : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .returned ffi bytes) :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.normal, riscv64WriteState { base with ffi := ffi } arrayValue bytes)) ∧
    stateRel
      { source with
        memory := panSemWriteBytearray
          (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
          (riscv64PanValueFfiContext base.shMemaddrs) source.memory
          (8 : RiscV.Word 64) arrayValue bytes,
        ffi := ffi }
      (riscv64WriteState { base with ffi := ffi } arrayValue bytes) := by
  have hlocals : (riscv64CrepRuntimeTarget base).locals = base.locals := rfl
  have hwrapper : crepRuntimeExtCall riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget base) function configuration configurationLength
      array arrayLength =
      crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function configurationValue
        configurationLengthValue arrayValue arrayLengthValue := by
    simp only [crepRuntimeExtCall, hlocals]
    rw [hconfiguration, hconfigurationLength, harray, harrayLength]
    rfl
  rw [hwrapper]
  exact crepRuntimeExtCallValues_stateRel_dispatch_returned source base function
    configurationValue configurationLengthValue arrayValue arrayLengthValue
    configurationBytes arrayBytes ffi bytes hstate hc ha hr

/-- Non-returned `FFI_final` dispatch of `crepRuntimeExtCallValues`.  When the
    handler reports a `final` event, HOL `call_FFI` returns `(SOME (FinalFFI
    outcome), s)` with the state unchanged, so the target step is `FinalFFI` with
    `riscv64CrepRuntimeTarget base` and the source/target states stay exactly the
    related pre-states.  This is the non-returned companion of
    `crepRuntimeExtCallValues_stateRel_dispatch_returned`; the failing-read case
    is `crepRuntimeExtCallValues_stateRel_error`. -/
theorem crepRuntimeExtCallValues_stateRel_dispatch_final
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (configurationBytes arrayBytes : List UInt8) (event : FfiFinalEvent)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configuration configurationLength.toNat =
      some configurationBytes)
    (ha : riscv64ReadByteArray base array arrayLength.toNat = some arrayBytes)
    (hf : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .final event) :
    (crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.finalFfi event, riscv64CrepRuntimeTarget base)) ∧
    stateRel source (riscv64CrepRuntimeTarget base) :=
  ⟨crepRuntimeExtCallValues_target_final base function configuration
      configurationLength array arrayLength configurationBytes arrayBytes hc ha
      event hf,
   hstate⟩

/-- Four-local production `ExtCall` wrapper dispatch for the failing-read branch
    (HOL `_ => (SOME Error, s)`).  The wrapper's argument lookups succeed but the
    configuration or array read fails, so the step is `Error` with the target state
    unchanged and the source/target states stay related.  Flapjack-only bridge (no
    HOL original). -/
theorem crepRuntimeExtCall_stateRel_error
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (h : riscv64ReadByteArray base configurationValue configurationLengthValue.toNat =
        none ∨
         riscv64ReadByteArray base arrayValue arrayLengthValue.toNat = none) :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.error, riscv64CrepRuntimeTarget base)) ∧
    stateRel source (riscv64CrepRuntimeTarget base) := by
  have hlocals : (riscv64CrepRuntimeTarget base).locals = base.locals := rfl
  have hwrapper : crepRuntimeExtCall riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget base) function configuration configurationLength
      array arrayLength =
      crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function configurationValue
        configurationLengthValue arrayValue arrayLengthValue := by
    simp only [crepRuntimeExtCall, hlocals]
    rw [hconfiguration, hconfigurationLength, harray, harrayLength]
    rfl
  rw [hwrapper]
  exact ⟨crepRuntimeExtCallValues_target_error base function configurationValue
      configurationLengthValue arrayValue arrayLengthValue h, hstate⟩

/-- Four-local production `ExtCall` wrapper dispatch for the non-returned
    `FFI_final` branch: the wrapper resolves its four locals, the reads succeed and
    the handler reports a `final` event, so the step is `FinalFFI` with the target
    state unchanged and the source/target states stay related.  This is the
    four-local companion of `crepRuntimeExtCallValues_stateRel_dispatch_final`.
    Flapjack-only bridge (no HOL original). -/
theorem crepRuntimeExtCall_stateRel_dispatch_final
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (configurationBytes arrayBytes : List UInt8) (event : FfiFinalEvent)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hc : riscv64ReadByteArray base configurationValue
      configurationLengthValue.toNat = some configurationBytes)
    (ha : riscv64ReadByteArray base arrayValue arrayLengthValue.toNat =
      some arrayBytes)
    (hf : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .final event) :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.finalFfi event, riscv64CrepRuntimeTarget base)) ∧
    stateRel source (riscv64CrepRuntimeTarget base) := by
  have hlocals : (riscv64CrepRuntimeTarget base).locals = base.locals := rfl
  have hwrapper : crepRuntimeExtCall riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget base) function configuration configurationLength
      array arrayLength =
      crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function configurationValue
        configurationLengthValue arrayValue arrayLengthValue := by
    simp only [crepRuntimeExtCall, hlocals]
    rw [hconfiguration, hconfigurationLength, harray, harrayLength]
    rfl
  rw [hwrapper]
  exact crepRuntimeExtCallValues_stateRel_dispatch_final source base function
    configurationValue configurationLengthValue arrayValue arrayLengthValue
    configurationBytes arrayBytes event hstate hc ha hf

/-- One-shot dispatch of the four-local production `crepRuntimeExtCall` wrapper on
    the canonical RISC-V 64 target.  This is the four-local companion of
    `crepRuntimeExtCallValues_target_dispatch_any`: after resolving the four source
    locals it reduces to `crepRuntimeExtCallValues`, so its result is the Lean
    `callFfi` (HOL `call_FFI`) match over the two `read_bytearray`s: `FFI_return`
    yields `Normal` with the returned bytes written back and the returned ffi
    installed, `FFI_final` yields `FinalFFI`, and a failed read yields `Error`.
    Flapjack-only bridge (no HOL original); it assembles the branch lemmas
    `crepRuntimeExtCall_stateRel_dispatch_returned`,
    `crepRuntimeExtCall_stateRel_dispatch_final` and `crepRuntimeExtCall_stateRel_error`. -/
theorem crepRuntimeExtCall_dispatch
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue)) :
    crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (match riscv64ReadByteArray base configurationValue configurationLengthValue.toNat,
             riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
       | some configurationBytes, some arrayBytes =>
           (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | .returned ffi bytes =>
                (.normal, riscv64WriteState { base with ffi := ffi } arrayValue bytes)
            | .final event => (.finalFfi event, riscv64CrepRuntimeTarget base))
       | _, _ => (.error, riscv64CrepRuntimeTarget base)) := by
  have hlocals : (riscv64CrepRuntimeTarget base).locals = base.locals := rfl
  simp only [crepRuntimeExtCall, hlocals]
  rw [hconfiguration, hconfigurationLength, harray, harrayLength]
  exact crepRuntimeExtCallValues_target_dispatch_any base function configurationValue
    configurationLengthValue arrayValue arrayLengthValue

/-- Assembled four-local `ExtCall` dispatch with source/target post-state relation:
    the wrapper's one-shot dispatch matches the `call_FFI`-shaped branch selection,
    and the corresponding post-states remain related (`stateRel`).  The source
    post-state is built by the theorem (the `write_bytearray`-based memory update on
    `FFI_return`, otherwise unchanged), never assumed; there is no target-run or
    post-state premise.  This packages every branch of
    `crepRuntimeExtCall_stateRel_dispatch_returned`/`_dispatch_final`/`_error` into a
    single case-split.  Flapjack-only bridge (no HOL original). -/
theorem crepRuntimeExtCall_stateRel_dispatch
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (hstate : stateRel source (riscv64CrepRuntimeTarget base)) :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (match riscv64ReadByteArray base configurationValue configurationLengthValue.toNat,
             riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
       | some configurationBytes, some arrayBytes =>
           (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | .returned ffi bytes =>
                (.normal, riscv64WriteState { base with ffi := ffi } arrayValue bytes)
            | .final event => (.finalFfi event, riscv64CrepRuntimeTarget base))
       | _, _ => (.error, riscv64CrepRuntimeTarget base))) ∧
    stateRel
      (match riscv64ReadByteArray base configurationValue configurationLengthValue.toNat,
             riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
       | some configurationBytes, some arrayBytes =>
           (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | .returned ffi bytes =>
                { source with
                  memory := panSemWriteBytearray
                    (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
                    (riscv64PanValueFfiContext base.shMemaddrs) source.memory
                    (8 : RiscV.Word 64) arrayValue bytes,
                  ffi := ffi }
            | .final _event => source)
       | _, _ => source)
      (match riscv64ReadByteArray base configurationValue configurationLengthValue.toNat,
             riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
       | some configurationBytes, some arrayBytes =>
           (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | .returned ffi bytes =>
                riscv64WriteState { base with ffi := ffi } arrayValue bytes
            | .final _event => riscv64CrepRuntimeTarget base)
       | _, _ => riscv64CrepRuntimeTarget base) := by
  constructor
  · exact crepRuntimeExtCall_dispatch base function configuration configurationLength
      array arrayLength configurationValue configurationLengthValue arrayValue
      arrayLengthValue hconfiguration hconfigurationLength harray harrayLength
  · cases hc : riscv64ReadByteArray base configurationValue configurationLengthValue.toNat with
    | none => simpa only [hc] using hstate
    | some configurationBytes =>
        cases ha : riscv64ReadByteArray base arrayValue arrayLengthValue.toNat with
        | none => simpa only [hc, ha] using hstate
        | some arrayBytes =>
            cases hf : callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | returned ffi bytes =>
                simpa only [hc, ha, hf] using
                  crepRuntimeExtCallValues_stateRel_returned source base arrayValue bytes ffi
                    hstate
            | final _event => simpa only [hc, ha, hf] using hstate

/-- Source-evaluator ExtCall step: from a genuine `panValueFfiExtCall` outcome
    (`FFI_return` write-back) on a source state related to the canonical RISC-V
    64 target, derive the target `crepRuntimeExtCall` result and the post-state
    `stateRel`.  No hypothesis states the target result or the post-relation;
    the returned bytes are derived from the source `call_FFI` outcome. -/
theorem panValueFfiExtCall_stateRel_target
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue :
      RiscV.Word 64)
    (hconfiguration : base.locals configuration = some (.word configurationValue))
    (hconfigurationLength : base.locals configurationLength =
      some (.word configurationLengthValue))
    (harray : base.locals array = some (.word arrayValue))
    (harrayLength : base.locals arrayLength = some (.word arrayLengthValue))
    (nextMemory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (nextFfi : FfiState σ)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hsource : panValueFfiExtCall
        (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
        (riscv64PanValueFfiContext base.shMemaddrs) source.memory
        (8 : RiscV.Word 64) source.ffi function
        configurationValue configurationLengthValue arrayValue arrayLengthValue =
      some (.returned nextMemory nextFfi)) :
    ∃ arrayBytes bytes,
      riscv64ReadByteArray base arrayValue arrayLengthValue.toNat = some arrayBytes ∧
      crepRuntimeExtCall riscv64ExtCallCallFfiHandler
          (riscv64CrepRuntimeTarget base) function
          configuration configurationLength array arrayLength =
        (.normal, riscv64WriteState { base with ffi := nextFfi } arrayValue bytes) ∧
      nextMemory =
        panValueMemoryView
          (riscv64WriteState { base with ffi := nextFfi } arrayValue bytes).memory ∧
      stateRel { source with memory := nextMemory, ffi := nextFfi }
        (riscv64WriteState { base with ffi := nextFfi } arrayValue bytes) := by
  obtain ⟨configurationBytes, arrayBytes, bytes, hcr, har, hffiR, hmem⟩ :=
    panValueFfiExtCall_returned_inv
      (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
      (riscv64PanValueFfiContext base.shMemaddrs) source.memory
      (8 : RiscV.Word 64) source.ffi function
      configurationValue configurationLengthValue arrayValue arrayLengthValue
      nextMemory nextFfi hsource
  have hmemView : source.memory = panValueMemoryView base.memory := hstate.1
  rw [hmemView] at hcr har
  rw [riscv64PanValueFfiContext_valueToNat_eq_riscv] at hcr har
  rw [panValueFfiReadBytes_view_eq_riscv] at hcr har
  have hbaseffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  have hfBase : callFfi base.ffi (.extCall function)
      configurationBytes arrayBytes = .returned nextFfi bytes := by
    rw [hbaseffi]; exact hffiR
  have hdispatch := crepRuntimeExtCall_stateRel_dispatch source base
    function configuration configurationLength array arrayLength
    configurationValue configurationLengthValue arrayValue arrayLengthValue
    hconfiguration hconfigurationLength harray harrayLength hstate
  refine ⟨arrayBytes, bytes, har, ?_, ?_, ?_⟩
  · rw [hdispatch.1]
    simp only [hcr, har, hfBase]
  · rw [hmem, panValueFfiWriteBytes_eq_panSemWriteBytearray, hmemView,
      panSemWriteBytearray_target_eq_riscv]
    conv => rhs; rw [riscv64WriteState_withFfi]
  · rw [hmem, panValueFfiWriteBytes_eq_panSemWriteBytearray]
    simpa only [hcr, har, hfBase] using hdispatch.2

/-- The source `sh_mem_load` `FFI_final` outcome drives the target shared-memory
    `load` dispatch to `FinalFFI` with the locals cleared and the pre-state
    relation (HOL `(SOME FinalFFI, empty_locals s)`).  Direct oracle:
    `scripts/hol-probes/crep_runtime_shared_mem_probe.out` (`load_final`). -/
theorem panValueFfiSharedLoad_stateRel_final
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (size : OpSize) (name : Nat) (address : RiscV.Word 64)
    (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hsource : panValueFfiSharedLoad (riscv64PanValueFfiContext base.shMemaddrs)
        source.ffi size address = some (.final nextFfi event)) :
    crepRuntimeSharedMem riscv64SharedMemCallFfiHandler
        (riscv64CrepRuntimeTarget base) (opSizeToCrepLoadOp size) name address =
      (.finalFfi event,
        clearCrepRuntimeLocals (riscv64CrepRuntimeTarget base)) ∧
    stateRel { source with ffi := nextFfi }
      (clearCrepRuntimeLocals (riscv64CrepRuntimeTarget base)) := by
  obtain ⟨hdom, hffi, hcall⟩ :=
    panValueFfiSharedLoad_final_inv (riscv64PanValueFfiContext base.shMemaddrs)
      source.ffi size address nextFfi event hsource
  subst hffi
  have hbaseffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  have hcallBase : callFfi base.ffi (.sharedMem .mappedRead)
      [UInt8.ofNat (panValueFfiWidth size)]
      ((riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false) =
        .final event := by
    rw [hbaseffi]; exact hcall
  have hvalid : crepRuntimeSharedAddressValid (riscv64CrepRuntimeTarget base)
      (opSizeToCrepLoadOp size) address = true := by
    rw [crepRuntimeSharedAddressValid_opSizeToCrepLoadOp]; exact hdom
  constructor
  · cases size <;>
      (simp only [opSizeToCrepLoadOp] at hvalid
       simp only [panValueFfiWidth] at hcallBase
       simp only [opSizeToCrepLoadOp, crepRuntimeMemWidth,
         riscv64CrepRuntimeTarget_ffi, riscv64CrepRuntimeTarget_ffiContext,
         riscv64SharedMemCallFfiHandler_sharedMem, crepSharedMemOperator,
         crepRuntimeSharedMem, clearCrepRuntimeLocals, hvalid, if_true,
         hcallBase])
  · simpa only [stateRel, clearCrepRuntimeLocals] using hstate

/-- The source `sh_mem_store` `FFI_final` outcome drives the target
    shared-memory `store` dispatch to `FinalFFI` with the pre-state relation
    (HOL `(SOME FinalFFI, s)`).  Direct oracle:
    `scripts/hol-probes/crep_runtime_shared_mem_probe.out` (`store_final`). -/
theorem panValueFfiSharedStore_stateRel_final
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (size : OpSize) (name : Nat) (address : RiscV.Word 64)
    (value : RiscV.Word 64)
    (hname : (riscv64CrepRuntimeTarget base).locals name = some (.word value))
    (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (hstate : stateRel source (riscv64CrepRuntimeTarget base))
    (hsource : panValueFfiSharedStore (riscv64PanValueFfiContext base.shMemaddrs)
        source.ffi size address value = some (.final nextFfi event)) :
    crepRuntimeSharedMem riscv64SharedMemCallFfiHandler
        (riscv64CrepRuntimeTarget base) (opSizeToCrepStoreOp size) name address =
      (.finalFfi event, riscv64CrepRuntimeTarget base) ∧
    stateRel { source with ffi := nextFfi }
      (riscv64CrepRuntimeTarget base) := by
  obtain ⟨hdom, hffi, hcall⟩ :=
    panValueFfiSharedStore_final_inv (riscv64PanValueFfiContext base.shMemaddrs)
      source.ffi size address value nextFfi event hsource
  subst hffi
  have hbaseffi : base.ffi = source.ffi :=
    (hstate.2.2.2.2.2.2.2.1.trans (riscv64CrepRuntimeTarget_ffi base)).symm
  have hcallBase : callFfi base.ffi (.sharedMem .mappedWrite)
      [UInt8.ofNat (panValueFfiWidth size)]
      (if panValueFfiWidth size = 0 then
          (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false
        else
          ((riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false).take
              (panValueFfiWidth size) ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false) =
        .final event := by
    rw [hbaseffi]; exact hcall
  have hvalid : crepRuntimeSharedAddressValid (riscv64CrepRuntimeTarget base)
      (opSizeToCrepStoreOp size) address = true := by
    rw [crepRuntimeSharedAddressValid_opSizeToCrepStoreOp]; exact hdom
  have hcallGoal : callFfi base.ffi (.sharedMem .mappedWrite)
      [UInt8.ofNat (crepRuntimeMemWidth (opSizeToCrepStoreOp size))]
      (if crepRuntimeMemWidth (opSizeToCrepStoreOp size) = 0 then
          (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false
        else
          ((riscv64PanValueFfiContext base.shMemaddrs).wordToBytes value false).take
              (crepRuntimeMemWidth (opSizeToCrepStoreOp size)) ++
            (riscv64PanValueFfiContext base.shMemaddrs).wordToBytes address false) =
        .final event := by
    rw [crepRuntimeSharedStorePayload_eq (riscv64PanValueFfiContext base.shMemaddrs)
      value address size]
    rw [crepRuntimeMemWidth_opSizeToCrepStoreOp]
    exact hcallBase
  constructor
  · cases size <;>
      (simp only [opSizeToCrepStoreOp] at hvalid
       simp only [opSizeToCrepStoreOp, riscv64CrepRuntimeTarget_ffi,
         riscv64CrepRuntimeTarget_ffiContext,
         riscv64SharedMemCallFfiHandler_sharedMem, crepSharedMemOperator,
         crepRuntimeSharedMem, hname, Option.map_some, panTheWord, hvalid, if_true]
       erw [hcallGoal])
  · simpa only [stateRel] using hstate

/-- Flapjack-specific analogue of HOL `pan_to_crepProofScript.sml:3051`
`evaluate_replicate_const`.  NOT a port: the production Crep evaluator
`evalCrepRuntimeExp`/`evalCrepRuntimeExps` returns the bare `α` carried by a
`word_lab` cell, and this statement is proved over the separate word_lab core
`evalCrepRuntimeExpsWordLab`, whose recursive children still call the bare
`evalCrepRuntimeExp` and whose arithmetic/`crepOp` cases delegate to the
arbitrary runtime `memoryModel` hooks rather than HOL's fixed `crepSem$eval`.
So it is not yet kernel-checked equal to `crepSem$eval` and must not carry a
`@[hol]` tag.  Establishing a faithful production evaluator/projection and
revisiting the tag is tracked by bead `flapjack-pxn.18.4.3.48.1`. -/
theorem evaluateReplicateConst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (count : Nat) (state : CrepRuntimeState α σ) :
    evalCrepRuntimeExpsWordLab state (List.replicate count (.const (0 : α))) =
      some (List.replicate count (.word (0 : α))) := by
  induction count with
  | zero => simp [evalCrepRuntimeExpsWordLab]
  | succ count ih =>
      simp [List.replicate_succ, evalCrepRuntimeExpsWordLab, evalCrepRuntimeExpWordLab, ih]

/-- Exact port of HOL `pan_to_crepProofScript.sml:3051` `evaluate_replicate_const`:
`∀n s. OPT_MMAP (eval s) (REPLICATE n (Const 0w)) = SOME (REPLICATE n (Word 0w))`.

This is the faithful statement, unlike the untagged word_lab-core analogue
`evaluateReplicateConst` above: it uses the reviewed exact `crepSem$eval_def`
port `evalCrepSemHOLExp` (`Flapjack/Pancake/Semantics/CrepSem/HOLState.lean`,
tagged `@[hol crepSemScript.sml eval_def]`), whose `Const` clause already
returns the `word_lab` cell `.word value`, so the conclusion has HOL's exact
`SOME (REPLICATE n (Word 0w))` shape with no bare-runtime post-map. `OPT_MMAP`
on an option monad is Lean `List.mapM`. Production routing (the executed
compiler calling the reviewed evaluator) remains tracked by
`flapjack-pxn.18.4.3.48.1`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "evaluate_replicate_const"]
theorem evaluateReplicateConstHOL {width : Nat} [NeZero width] {ffiState : Type}
    (n : Nat) (state : CrepSemHOLState width ffiState) :
    (List.replicate n (CrepExpHOL.const (0 : BitVec width))).mapM
        (evalCrepSemHOLExp state) =
      some (List.replicate n (HolWordLab.word (0 : BitVec width))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.mapM_cons, evalCrepSemHOLExp, ih]
      rfl

/-! ## Exact HOL `pan_to_crep` `is_wf_shape_nil_length_flatten`

The match above is the source-shaped port over the production `PanValue`/`String`
carrier. The declaration below is the exact port of the same HOL theorem over
the HOL-shaped `ValueHOL`/`StructContextExact` carriers. -/
open Flapjack.Pancake.PanLang

/-- Exact port of HOL Cake `pan_to_crepProof$is_wf_shape_nil_length_flatten`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2469`). Over the
    HOL-shaped `ValueHOL`/`StructContextExact` carriers, a word list selected
    by the zero-size or positive-size branch has the size prescribed by the
    source value shape. Reuses the exact `flattenHOL_length_eq_sizeOfShapeHOL`
    (HOL `panPropsScript.sml:171`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "is_wf_shape_nil_length_flatten"]
theorem isWfShapeExactHOL_length_flatten {width : Nat} [NeZero width]
    (value : ValueHOL width) (words : List (HolWordLab width))
    (h : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true ∧
      (sizeOfShapeHOL (shapeOfHOLExact value) = 0 → words = []) ∧
      (0 < sizeOfShapeHOL (shapeOfHOLExact value) → words = flattenHOL value)) :
    words.length = sizeOfShapeHOL (shapeOfHOLExact value) := by
  obtain ⟨hwf, hzero, hpositive⟩ := h
  by_cases hz : sizeOfShapeHOL (shapeOfHOLExact value) = 0
  · simp [hzero hz, hz]
  · have hpos : 0 < sizeOfShapeHOL (shapeOfHOLExact value) := Nat.pos_of_ne_zero hz
    rw [hpositive hpos]
    exact flattenHOL_length_eq_sizeOfShapeHOL value hwf

/-- Exact port of HOL `decs_stcnames_lemma` (`pan_to_crepProofScript.sml:4963-4969`):
a declaration list containing only function or exception declarations leaves the
structure context unchanged. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "decs_stcnames_lemma"]
theorem decsStcnamesHOLExact_of_functions_or_exnDecls {width : Nat} [NeZero width]
    (code : List (DeclHOL width)) (context : StructContextExact)
    (h : code.all (fun declaration =>
      isFunctionHOL declaration || isExnDeclHOL declaration) = true) :
    decsStcnamesHOLExact (width := width) context code = some context := by
  induction code generalizing context with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration <;>
        simp_all [decsStcnamesHOLExact, isFunctionHOL, isExnDeclHOL]

/-! ## Disposition of HOL `state_rel_imp_semantics` (bead flapjack-4ac.5.79)

`cakeml/pancake/proofs/pan_to_crepProofScript.sml:5005-5022` proves the
top-level pan-to-crep semantics-preservation theorem

```
!s t pan_code start.
  state_rel s t /\ ALL_DISTINCT (MAP FST (functions pan_code)) /\
  s.code = alist_to_fmap (functions pan_code) /\
  t.code = alist_to_fmap (pan_to_crep$compile_prog pan_code) /\
  s.locals = FEMPTY /\
  EVERY (localised_prog o FST o SND o SND) (functions pan_code) /\
  panLang$size_of_eids pan_code < dimword (:'a) /\
  FDOM s.eshapes = FDOM (get_eids_from_decls pan_code) /\
  semantics s start <> Fail ==>
  semantics t start = semantics s start
```

over `panSem$state`/`crepSem$state` with `mlstring`-keyed code/eshapes and the
HOL `state_rel`. No Lean declaration states it. Flapjack's `stateRel`
(`Flapjack/Pancake/Proofs/PanToCrep.lean`) relates the production
`PanSemState α (FfiState σ)` / `CrepRuntimeState α σ` with `VarName`/
`FunName`/`ExceptionId`/`StructName = String`, `PanValue α` and production
`Shape`, whereas HOL relates `mlstring`-keyed states, `panSem$v`, and `shape`
with `'a word_lab` payloads; it also has no Lean `semantics`/`compile_prog`
counterparts for the two languages. The theorem therefore must not be
`@[hol]`-tagged. Faithful-port dependencies: `flapjack-pxn.18.4.4` (port
`state_rel_imp_semantics_to_crep` and the declarations theorem) plus
`flapjack-pxn.18.3.5.8` (exact MlString carriers) and `flapjack-0lj`
(`word_lab`).

The same disposition applies to the two declaration-level companions.

`state_rel_imp_semantics_decls_to_crep`
(`pan_to_crepProofScript.sml:4973-4990`) drops to `state_rel (s with structs
:= []) t`, `s.code = FEMPTY`, `t.code = alist_to_fmap (compile_to_crep
pan_code)`, `s.eshapes = FEMPTY`, requires `EVERY (λx. is_function x ∨
is_exn_decl x) pan_code`, and concludes `semantics t start = semantics_decls s
start pan_code` from `semantics_decls s start pan_code <> Fail`.
`state_rel_imp_semantics_decls` (`pan_to_crepProofScript.sml:5042-5059`) is the
same statement except that `t.code = alist_to_fmap (compile_prog pan_code)`
rather than `alist_to_fmap (compile_to_crep pan_code)`; both require
`s.eshapes = FEMPTY`. Both quantify over the same `mlstring`-keyed
`panSem$state`/`crepSem$state`, use the HOL `state_rel`, `semantics_decls`,
`compile_to_crep`/`compile_prog` and `is_function`/`is_exn_decl`, none of which
has a Lean counterpart; Flapjack's `stateRel` relates production String-keyed
`PanSemState`/`CrepRuntimeState`. Neither may be `@[hol]`-tagged. Both are
tracked by the same faithful-port dependency `flapjack-pxn.18.4.4` (with
`flapjack-pxn.18.3.5.8` and `flapjack-0lj`). -/

/-! ## Exact HOL `pan_to_crepProof$ctxt_fc`

HOL (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:25-29`) builds the
compiled-function context from the function map `cvs`, the exception map `em`,
variable names `vs`, shapes `shs`, and the `GENLIST`-indexed name blocks `ns`:

    ctxt_fc cvs em vs shs ns =
      <|vars := FEMPTY |++ ZIP (vs, ZIP (shs, with_shape shs ns));
        funcs := cvs; eids := em; vmax := MAX_LIST ns|>

The Lean port matches the argument order `(cvs, em, vs, shs, ns)` and the field
assignment clause for clause. HOL `FEMPTY |++ l` is `FUPDATE_LIST FEMPTY l`
(`HolFiniteMapExact.updateList HolFiniteMapExact.empty l`), HOL `ZIP` is
`List.zip` (which truncates to the shorter list exactly as HOL does),
`with_shape` is the tagged `withShapeHOL`, and `MAX_LIST` is `maxList`. The
record carrier is the reviewed exact `PanToCrepContextExact`; the
`fmap_as_finite_support` qualifier records only the canonical finite-support
representation of its three HOL finite-map fields. Direct HOL-EVAL rows are in
`scripts/hol-probes/ctxt_fc_probe.out` and replayed by
`Flapjack.Test.PanToCrepContextExactParity`.

`updateList` is explicitly instantiated with Lean's generic
`BEqOfDecidableEq`/`LawfulBEq` pair for `MlS`. This keeps the definition's
equality dictionary tied to HOL `=` independently of the named but equivalent
`MlS` instances imported through the production inline-pass dependency. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_def"
  (fmap_as_finite_support := [vars, funcs, eids])]
def ctxtFcExactHOL {width : Nat} [NeZero width]
    (cvs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (em : HolFiniteMapExact MlS (BitVec width))
    (vs : List MlS) (shs : List ShapeHOL) (ns : List Nat) :
    PanToCrepContextExact width where
  vars := @HolFiniteMapExact.updateList MlS (ShapeHOL × List Nat)
    (@instBEqOfDecidableEq MlS
      Flapjack.Basis.Pure.MlString.instDecidableEqMlString)
    (@instLawfulBEq MlS
      Flapjack.Basis.Pure.MlString.instDecidableEqMlString)
    (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ShapeHOL × List Nat))
    (vs.zip (shs.zip (withShapeHOL shs ns)))
  funcs := cvs
  eids := em
  vmax := maxList ns

namespace CtxtFcExact

/-- Canonical finite-map representation witness for the imported exact context
    carrier `PanToCrepContextExact`, required by the `fmap_as_finite_support`
    qualifier on `ctxtFcExactHOL`. Flapjack-only representation infrastructure;
    it is not a port of a HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context := by
  cases context
  rfl

end CtxtFcExact

/-- Exact port of HOL `ctxt_fc_funcs_eq`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2295`):
    `(ctxt_fc cvs em vs shs ns).funcs = cvs`. The constructed context's
    `funcs` field is definitionally the supplied function map. The statement
    keeps HOL's argument order `(cvs, em, vs, shs, ns)` and its unrestricted
    quantifiers; the only representation difference is the reviewed canonical
    `HolFiniteMapExact` translation of HOL's `funname |-> ((varname # shape) #
    shape)` finite map (names are `MlS` = `mlstring`, shapes are
    `ShapeHOL` = `shape`), recorded by the `fmap_as_finite_support` qualifier on
    the `funcs` field of the imported exact `PanToCrepContextExact` carrier
    (same-module witness `CtxtFcExact.holFmapAsFiniteSupportWitness`). The
    signature is width-indexed with `BitVec width` exception codes and
    `[NeZero width]`, so HOL's type-indexed `'a word` translation is recorded by
    the `(words_as_type_indexed_bitvec)` qualifier. Direct HOL-EVAL row
    `functions_projection=T` in `scripts/hol-probes/ctxt_fc_probe.out` is
    replayed by the kernel-checked regression in
    `Flapjack.Test.PanToCrepContextExactParity`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_funcs_eq"
  (fmap_as_finite_support := [funcs])
  (words_as_type_indexed_bitvec)]
theorem ctxtFcFuncsEqHOL {width : Nat} [NeZero width]
    (cvs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (em : HolFiniteMapExact MlS (BitVec width))
    (vs : List MlS) (shs : List ShapeHOL) (ns : List Nat) :
    (ctxtFcExactHOL cvs em vs shs ns : PanToCrepContextExact width).funcs = cvs := rfl

/-- Exact port of HOL `ctxt_fc_eids_eq`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2301`):
    `(ctxt_fc cvs em vs shs ns).eids = em`. The constructed context's
    `eids` field is definitionally the supplied exception-code map. The
    statement keeps HOL's argument order `(cvs, em, vs, shs, ns)` and its
    unrestricted quantifiers; the only representation difference is the
    reviewed canonical `HolFiniteMapExact` translation of HOL's
    `eid |-> 'a word` finite map (names are `MlS` = `mlstring`), recorded by
    the `fmap_as_finite_support` qualifier on the `eids` field of the imported
    exact `PanToCrepContextExact` carrier (same-module witness
    `CtxtFcExact.holFmapAsFiniteSupportWitness`). The signature is width-indexed
    with `BitVec width` exception codes and `[NeZero width]`, so HOL's
    type-indexed `'a word` translation is recorded by the
    `(words_as_type_indexed_bitvec)` qualifier. The direct HOL-EVAL projection
    row is replayed by the kernel-checked regression in
    `Flapjack.Test.PanToCrepContextExactParity`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_eids_eq"
  (fmap_as_finite_support := [eids])
  (words_as_type_indexed_bitvec)]
theorem ctxtFcEidsEqHOL {width : Nat} [NeZero width]
    (cvs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (em : HolFiniteMapExact MlS (BitVec width))
    (vs : List MlS) (shs : List ShapeHOL) (ns : List Nat) :
    (ctxtFcExactHOL cvs em vs shs ns : PanToCrepContextExact width).eids = em := rfl

/-- Exact port of HOL `ctxt_fc_vmax`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2307`):
    `(ctxt_fc ctxt.funcs em vs shs ns).vmax = MAX_LIST ns`. The typed capture
    `ctxt_fc_vmax_typed` (`pan_to_crep_proof_typed_probe.out:4`) types the
    context at `β context` and `em` at `α word`, so the context's word
    dimension is independent of the exception-code width; the statement binds
    `{ctxtWidth}` and `{width}` separately and states HOL's `ctxt` binder with
    its `.funcs` projection (task 152 item 4). The argument order
    `(ctxt, em, vs, shs, ns)` and HOL's unrestricted quantifiers are kept; the
    constructed context's `vmax` field is definitionally `maxList ns`, so the
    statement is a no-premise projection. `.vmax` is a `Nat` that depends only
    on `ns`, so the conclusion does not traverse any finite-map field; the
    `fmap_as_finite_support := [funcs]` qualifier records the canonical
    `HolFiniteMapExact` translation of the traversed `ctxt.funcs` field
    (same-module witness `CtxtFcExact.holFmapAsFiniteSupportWitness`). `em` is
    a standalone canonical map parameter and needs no qualifier. The signature
    is width-indexed with `BitVec width` exception codes and `[NeZero width]`,
    so HOL's type-indexed `'a word` translation is recorded by the
    `(words_as_type_indexed_bitvec)` qualifier. Direct HOL-EVAL rows
    `vmax_nonempty_list=T`/`vmax_empty_list=T` in
    `scripts/hol-probes/ctxt_fc_probe.out` are replayed by the kernel-checked
    regression in `Flapjack.Test.PanToCrepContextExactParity`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_vmax"
  (fmap_as_finite_support := [funcs])
  (words_as_type_indexed_bitvec)]
theorem ctxtFcVmaxHOL {width : Nat} {ctxtWidth : Nat} [NeZero width] [NeZero ctxtWidth]
    (ctxt : PanToCrepContextExact ctxtWidth)
    (em : HolFiniteMapExact MlS (BitVec width))
    (vs : List MlS) (shs : List ShapeHOL) (ns : List Nat) :
    (ctxtFcExactHOL ctxt.funcs em vs shs ns : PanToCrepContextExact width).vmax =
      maxList ns := rfl

/-- Untagged bare-map form of `ctxt_fc_vmax` for callers that only hold the
    `funcs` map; the tagged statement follows HOL's `ctxt` binder. -/
theorem ctxtFcVmaxHOL_bare {width : Nat} [NeZero width]
    (cvs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (em : HolFiniteMapExact MlS (BitVec width))
    (vs : List MlS) (shs : List ShapeHOL) (ns : List Nat) :
    (ctxtFcExactHOL cvs em vs shs ns : PanToCrepContextExact width).vmax =
      maxList ns := rfl

end Flapjack
