import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.ValueHOL
import Flapjack.Pancake.Semantics.PanSem.IsValidValueExact
import Flapjack.Pancake.Semantics.PanSem.DecExact
import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge
import Flapjack.Pancake.Semantics.PanSem.TotalEvalRanged
import Flapjack.Pancake.PanLang.Decl

/-!
Source-state conversion and evaluator support for porting HOL
`pan_structsProofScript.sml` `compile_correct`. The full theorem's premises
and invariant postconditions are not yet proved here.
-/

namespace Flapjack


mutual
  /-- Source-shaped executable counterpart (Flapjack-specific; NOT an exact HOL port) of HOL `convert_v_def`. The HOL datatype
      cases are `Val (Word w)`, `RStruct xs`, and `NStruct nm flds`; these
      correspond respectively to `.word`, `.rStruct`, and `.nStruct` in
      `PanValue`. The first case is unchanged, the second maps recursively in
      order, and the third drops both record and field names while recursively
      mapping field values in order. The direct HOL-EVAL regression is recorded
      in the adjacent probe fixture. -/
  -- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is over the
  -- production PanValue α carrier, whose word payload is the generic α and whose
  -- nStruct record/field names are StructName/FieldName = String, while HOL
  -- pan_structsProofScript.sml is over panSem$v with a word-labelled payload and
  -- stcname/fldname = mlstring. The exact HOL definition is `convertV` over the
  -- exact `ValueHOL` carrier (tagged with this HOL name above); the kernel-checked
  -- This executable counterpart stays
  -- untagged until the executable path itself runs over the exact carriers,
  -- tracked by flapjack-pxn.18.3.5.8 (parent flapjack-pxn.18.3.5.7.2).
  def panStructConvertValue : PanValue α → PanValue α
    | .word value => .word value
    | .rStruct fields => .rStruct (panStructConvertValues fields)
    | .nStruct _ fields => .rStruct (panStructConvertFieldValues fields)
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructConvertValues : List (PanValue α) → List (PanValue α)
    | [] => []
    | value :: values => panStructConvertValue value :: panStructConvertValues values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructConvertFieldValues : List (FieldName × PanValue α) → List (PanValue α)
    | [] => []
    | (_, value) :: fields =>
        panStructConvertValue value :: panStructConvertFieldValues fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Exact port of HOL `convert_v_def`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:31-37`):
    `convert_v (Val x) = Val x`,
    `convert_v (RStruct xs) = RStruct (MAP convert_v xs)`, and
    `convert_v (NStruct nm flds) = RStruct (MAP (\(nm,v). convert_v v) flds)`,
    over the exact `panSem$v` carrier `ValueHOL` (MlString names and an indexed
    word payload). The `NStruct` branch drops the record and field names, so the
    exact `mlstring` name carrier is carried but never inspected. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_v_def"
  (words_as_type_indexed_bitvec)]
def convertV {width : Nat} [NeZero width] : ValueHOL width → ValueHOL width
  | .val value => .val value
  | .rStruct fields => .rStruct (fields.map convertV)
  | .nStruct _ fields => .rStruct (fields.map (fun pair => convertV pair.2))
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
    | (rename_i hmem
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)
    | (rename_i hmem
       have hsnd : sizeOf pair.snd < sizeOf pair := by cases pair; simp +arith
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)

/-- Exact port of HOL `convert_res_def`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:1005-1009`):
    `convert_res (SOME Break) = SOME Break`,
    `convert_res (SOME (Return v)) = SOME (Return (convert_v v))`,
    `convert_res (SOME (Exception eid ev)) = SOME (Exception eid (convert_v ev))`,
    and `convert_res res = res`.

    The parameter is HOL's `panSem$result option`, rendered as
    `Option (PanSemResultExact width)` over the reviewed exact `result` carrier
    (`DecExact.lean:58`, tagged against `panSemScript.sml:68-75`).  The three
    matched clauses recurse through the exact `convertV`; the default clause
    keeps `NONE`, `Error`, `TimeOut`, `Continue`, and `FinalFFI` unchanged,
    exactly as HOL's catch-all.  The only difference from HOL is the
    already-reviewed `result` carrier, so no qualifier applies. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_res_def"]
def convertResHOL {width : Nat} [NeZero width] :
    Option (PanSemResultExact width) → Option (PanSemResultExact width)
  | some .break => some .break
  | some (.returned value) => some (.returned (convertV value))
  | some (.exception exceptionId value) => some (.exception exceptionId (convertV value))
  | res => res

/-- Exact port of HOL `convert_res_eq_case1[local]`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:1012-1019`):
    `convert_res res = (case res of
       SOME Break => convert_res (SOME Break)
     | SOME x => convert_res (SOME x)
     | NONE => NONE)`.

    The parameter is HOL's `panSem$result option`, rendered as
    `Option (PanSemResultExact width)` over the reviewed exact `result` carrier
    (`DecExact.lean:58`, tagged against `panSemScript.sml:68-75`), and
    `convertResHOL` is the already-reviewed exact port of `convert_res` above.
    `SOME Break` is `some .break`, `SOME x` is `some x`, `NONE` is `none`, and
    the HOL `case ... of` is the Lean `match`; the two sides are equal
    constructor by constructor and no payload is inspected.  The only difference
    from HOL is the already-reviewed `result` carrier, so no qualifier applies. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_res_eq_case1"]
theorem convertResHOL_eqCase1 {width : Nat} [NeZero width]
    (res : Option (PanSemResultExact width)) :
    convertResHOL res =
      (match res with
        | some .break => convertResHOL (some .break)
        | some x => convertResHOL (some x)
        | none => none) := by
  cases res with
  | none => rfl
  | some result => cases result <;> rfl

/-- Exact port of HOL `is_cont_res_def`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:992-997`):
    `is_cont_res NONE = T`, `is_cont_res (SOME Break) = T`,
    `is_cont_res (SOME Continue) = T`, and `is_cont_res _ = F`.

    The parameter is HOL's `panSem$result option`, rendered as
    `Option (PanSemResultExact width)` over the reviewed exact `result` carrier
    (`DecExact.lean:58`, tagged against `panSemScript.sml:68-75`).  The three
    matched clauses and the `NONE` clause return `true`, the catch-all returns
    `false`, exactly as HOL's clauses; no payload is inspected.  The only
    difference from HOL is the already-reviewed `result` carrier, so no
    qualifier applies. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "is_cont_res_def"]
def isContResHOL {width : Nat} [NeZero width] :
    Option (PanSemResultExact width) → Bool
  | none => true
  | some .break => true
  | some .continue => true
  | _ => false

/-- Exact port of HOL `is_cont_res_eq_disj[local]`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:999-1003`):
    `is_cont_res res = (res = NONE \/ res = SOME Break \/ res = SOME Continue)`.

    The parameter is HOL's `panSem$result option`, rendered as
    `Option (PanSemResultExact width)` over the reviewed exact `result` carrier
    (`DecExact.lean:58`, tagged against `panSemScript.sml:68-75`); the Bool
    equality against a disjunction is rendered as the iff
    `isContResHOL res = true ↔ res = none ∨ res = some .break ∨
    res = some .continue`.  `isContResHOL` is `true` exactly on `NONE`,
    `SOME Break`, and `SOME Continue`, so the two sides coincide constructor by
    constructor; no payload is inspected.  The only difference from HOL is the
    already-reviewed `result` carrier and the standard Bool-to-Prop rendering of
    the disjunctive equality, so no qualifier applies. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "is_cont_res_eq_disj"]
theorem isContResHOL_eqDisj {width : Nat} [NeZero width]
    (res : Option (PanSemResultExact width)) :
    (isContResHOL res = true) ↔
      res = none ∨ res = some .break ∨ res = some .continue := by
  cases res with
  | none => simp [isContResHOL]
  | some result =>
      cases result <;> simp [isContResHOL]

/-- Exact port of HOL `res_vs_def`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:1028-1031`):
    `res_vs (SOME (Return v)) = [v]`,
    `res_vs (SOME (Exception eid ev)) = [ev]`, and `res_vs _ = []`.

    The parameter is HOL's `panSem$result option`, rendered as
    `Option (PanSemResultExact width)` over the reviewed exact `result` carrier
    (`DecExact.lean:58`, tagged against `panSemScript.sml:68-75`), and the
    result element type is the reviewed exact `panSem$v` carrier `ValueHOL`
    (`panSemScript.sml:22`).  The two matched clauses extract the `Return` and
    `Exception` payloads verbatim; the catch-all returns the empty list exactly
    as HOL's catch-all, so `NONE`, `Error`, `TimeOut`, `Break`, `Continue`, and
    `FinalFFI` all map to `[]`.  The only difference from HOL is the
    already-reviewed `result`/`v` carriers, so no qualifier applies. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "res_vs_def"]
def resVsHOL {width : Nat} [NeZero width] :
    Option (PanSemResultExact width) → List (ValueHOL width)
  | some (.returned value) => [value]
  | some (.exception _ value) => [value]
  | _ => []

/-- Exact port of HOL `every_convert_v_eq[local]`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:268-271`):
    `EVERY (\w. case w of Val _ => T | _ => F) vs ==> MAP convert_v vs = vs`.

    The list element type is the reviewed exact `panSem$v` carrier `ValueHOL`
    (`panSemScript.sml:22`, tagged `reviewed_exact` via `convert_v_def`), the
    `EVERY` premise is rendered as the membership-quantified
    `∀ w ∈ vs, match w with | .val _ => True | _ => False`, and `MAP convert_v`
    as `List.map convertV`. Only the `Val` case can satisfy the premise, and
    `convert_v (Val x) = Val x` leaves the list unchanged; no payload, name, or
    word dimension is inspected, so the only difference from HOL is the
    already-reviewed carrier and no qualifier applies. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "every_convert_v_eq"]
theorem everyConvertVEq {width : Nat} [NeZero width] (vs : List (ValueHOL width))
    (h : ∀ w ∈ vs, match w with | .val _ => True | _ => False) :
    vs.map convertV = vs := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons, List.cons.injEq]
    constructor
    · cases w <;> simp_all [convertV]
    · exact ih (fun x hx => h x (by simp [hx]))

/-! Structural Bool equality for the translated Shape datatype. It performs
    the HOL constructor equality cases recursively and avoids a BEq instance
    for Shape or String. -/
mutual
  def panStructShapeEqBool : Shape → Shape → Bool
    | .one, .one => true
    | .comb left, .comb right => panStructShapeListEqBool left right
    | .named left, .named right => decide (left = right)
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructShapeListEqBool : List Shape → List Shape → Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        panStructShapeEqBool left right && panStructShapeListEqBool lefts rights
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Source-shaped executable port (Flapjack-specific; NOT an exact HOL port) of HOL `pan_structsProof$v_flds_ok`
      (`cakeml/pancake/proofs/pan_structsProofScript.sml:39`). The HOL clauses
      are reproduced literally: a scalar is `T`; `RStruct vs` is
      `EVERY (v_flds_ok ctxt) vs`; `NStruct nm flds` is the conjunction of the
      per-field predicate `EVERY (\(nm,v). v_flds_ok ctxt v) flds` with the
      `ALOOKUP ctxt nm` case, where `NONE` gives `F` and `SOME info` requires
      both `MAP FST flds = MAP FST info.fields` and
      `MAP (shape_of o SND) flds = MAP SND info.fields`.

      `lookupInfo` is the first-match association-list lookup, i.e. the exact
      `alist$ALOOKUP` counterpart, and under `[LawfulBEq String]` its `==`
      reflects HOL's `=`. The context is the HOL-shaped `StructContextHOL`
      (fields and size only). `panSemShapeOf` is the source-shaped (currently untagged) counterpart of HOL
      `shape_of` (`panSemScript.sml:80`), and `panStructShapeListEqBool`
      computes HOL's `=` on `shape` lists constructor-by-constructor, since
      Lean `Shape` intentionally has no `BEq`/`DecidableEq` instance. The
      direct original-HOL rows are pinned in
      `scripts/hol-probes/pan_structs_value_validity_probe.out`. -/
  -- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is over the
  -- production PanValue carrier whose nStruct record/field names are
  -- StructName/FieldName = String and over StructContextHOL (String-keyed), while
  -- HOL pan_structsProofScript.sml is over panSem$v with stcname/fldname = mlstring.
  -- The exact MlString identifier carrier is tracked by flapjack-pxn.18.3.5.8
  -- (parent flapjack-pxn.18.3.5.7.2).
  def panValueFldsOk [LawfulBEq String] (context : StructContextHOL) :
      PanValue α → Bool
    | .word _ => true
    | .rStruct values => panValuesFldsOk context values
    | .nStruct name fields =>
        panFieldsFldsOk context fields &&
          match lookupInfo name context with
          | none => false
          | some info =>
              (fields.map Prod.fst == info.fields.map Prod.fst) &&
                panStructShapeListEqBool
                  (fields.map (panSemShapeOf ∘ Prod.snd))
                  (info.fields.map Prod.snd)
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panValuesFldsOk [LawfulBEq String] (context : StructContextHOL) :
      List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panValueFldsOk context value && panValuesFldsOk context values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panFieldsFldsOk [LawfulBEq String] (context : StructContextHOL) :
      List (FieldName × PanValue α) → Bool
    | [] => true
    | (_, value) :: fields =>
        panValueFldsOk context value && panFieldsFldsOk context fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

private theorem lookupInfo_mem_of_some [BEq κ] [LawfulBEq κ]
    (key : κ) (entries : List (κ × β)) (value : β)
    (hlookup : lookupInfo key entries = some value) :
    key ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [lookupInfo] at hlookup
  | cons entry entries ih =>
      obtain ⟨candidate, candidateValue⟩ := entry
      by_cases hmatch : candidate == key
      · have heq : candidate = key := LawfulBEq.eq_of_beq hmatch
        simp [heq]
      · simp only [lookupInfo, hmatch] at hlookup
        have htail := ih hlookup
        simp [htail]


open Flapjack.Pancake.PanLang (MlS ShapeHOL StructInfoHOLExact StructContextExact)

mutual
  /-- Exact Bool rendering of HOL `v_flds_ok_def` over the faithful HOL value,
      shape, and struct-context carriers. Field-name and shape-list equality
      implement HOL datatype equality. -/
  @[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "v_flds_ok_def"]
  def valueFldsOkHOLExact {width : Nat} [NeZero width]
      (context : StructContextExact) : ValueHOL width → Bool
    | .val _ => true
    | .rStruct values => valuesFldsOkHOLExact context values
    | .nStruct name fields =>
        fieldsFldsOkHOLExact context fields &&
          match Flapjack.Pancake.PanLang.structContextLookupHOL name context with
          | none => false
          | some info =>
              (fields.map Prod.fst == info.fields.map Prod.fst) &&
                shapeEqHOL.shapeEqListHOL
                  (fields.map (fun field => shapeOfHOLExact field.2))
                  (info.fields.map Prod.snd)
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def valuesFldsOkHOLExact {width : Nat} [NeZero width]
      (context : StructContextExact) : List (ValueHOL width) → Bool
    | [] => true
    | value :: values =>
        valueFldsOkHOLExact context value && valuesFldsOkHOLExact context values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def fieldsFldsOkHOLExact {width : Nat} [NeZero width]
      (context : StructContextExact) : List (MlS × ValueHOL width) → Bool
    | [] => true
    | (_, value) :: fields =>
        valueFldsOkHOLExact context value && fieldsFldsOkHOLExact context fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

private theorem structContextLookupHOL_mem_of_some
    (name : MlS) (entries : StructContextExact) (info : StructInfoHOLExact)
    (hlookup : Flapjack.Pancake.PanLang.structContextLookupHOL name entries = some info) :
    name ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [Flapjack.Pancake.PanLang.structContextLookupHOL] at hlookup
  | cons entry entries ih =>
      obtain ⟨candidate, candidateInfo⟩ := entry
      by_cases hmatch : name = candidate
      · subst name
        simp
      · simp only [Flapjack.Pancake.PanLang.structContextLookupHOL, if_neg hmatch] at hlookup
        have htail := ih hlookup
        simp [hmatch, htail]

private theorem structContextLookupHOL_append_eq_of_some
    (pfx context : StructContextExact) (name : MlS) (info : StructInfoHOLExact)
    (hdisjoint : (pfx.map Prod.fst ++ context.map Prod.fst).Nodup)
    (hlookup : Flapjack.Pancake.PanLang.structContextLookupHOL name context = some info) :
    Flapjack.Pancake.PanLang.structContextLookupHOL name (pfx ++ context) = some info := by
  induction pfx with
  | nil => exact hlookup
  | cons entry pfx ih =>
      obtain ⟨candidate, candidateInfo⟩ := entry
      rcases List.nodup_cons.mp hdisjoint with ⟨hnot, htailNodup⟩
      have hnameMem := structContextLookupHOL_mem_of_some name context info hlookup
      have hne : name ≠ candidate := by
        intro heq
        subst name
        exact hnot (List.mem_append_right _ hnameMem)
      have hlookupTail := ih htailNodup
      simp [hne, hlookupTail]

/-- For a distinct-name context, a successful lookup after a prefix drop is
    unchanged by the drop. -/
private theorem structContextLookupHOL_drop_eq_of_some
    (n : Nat) (context : StructContextExact) (name : MlS) (info : StructInfoHOLExact)
    (hlookup : Flapjack.Pancake.PanLang.structContextLookupHOL name (context.drop n) = some info)
    (hnodup : (context.map Prod.fst).Nodup) :
    Flapjack.Pancake.PanLang.structContextLookupHOL name context = some info := by
  induction n generalizing context with
  | zero => simpa using hlookup
  | succ n ih =>
      cases context with
      | nil => simp at hlookup
      | cons entry rest =>
          obtain ⟨candidate, candidateInfo⟩ := entry
          have hnames : (candidate :: rest.map Prod.fst).Nodup := by
            simpa using hnodup
          obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hnames
          have htail : Flapjack.Pancake.PanLang.structContextLookupHOL name
              (rest.drop n) = some info := by
            simpa using hlookup
          have hmemTail := structContextLookupHOL_mem_of_some name (rest.drop n) info htail
          have hmemRest : name ∈ rest.map Prod.fst := by
            rw [List.map_drop] at hmemTail
            exact List.mem_of_mem_drop hmemTail
          have hne : name ≠ candidate := by
            intro heq
            apply hnot
            rw [← heq]
            exact hmemRest
          have hctx := ih rest htail hrest
          simpa [Flapjack.Pancake.PanLang.structContextLookupHOL, hne] using hctx

/-- Exact port of HOL `size_of_sh_with_ctxt_drop`
    (`pan_structsProofScript.sml:99`). This keeps HOL's well-formedness and
    distinct-name premises over `ShapeHOL` and `StructContextExact`. The
    production String-carrier analogue remains untagged in `PanStructs.lean`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "size_of_sh_with_ctxt_drop"]
theorem sizeOfShapeWithContextHOL_drop (context : StructContextExact)
    (shape : ShapeHOL) (n : Nat)
    (hwf : Flapjack.Pancake.PanLang.isWfShapeExactHOL (context.drop n) shape = true)
    (hnodup : (context.map Prod.fst).Nodup) :
    Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL (context.drop n) shape =
      Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context shape := by
  let contextDrop := context.drop n
  have hrec := Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL.induct
    (context := contextDrop)
    (motive_1 := fun sh =>
      Flapjack.Pancake.PanLang.isWfShapeExactHOL contextDrop sh = true →
        Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL contextDrop sh =
          Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context sh)
    (motive_2 := fun shapes =>
      Flapjack.Pancake.PanLang.isWfShapesExactHOL contextDrop shapes = true →
        Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL contextDrop shapes =
          Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL context shapes)
    (case1 := by
      intro _
      rfl)
    (case2 := by
      intro shapes ih hwfShapes
      simpa [Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL_comb] using ih hwfShapes)
    (case3 := by
      intro name info hlookup _
      have hctx := structContextLookupHOL_drop_eq_of_some n context name info hlookup hnodup
      simp [Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL, hlookup, hctx])
    (case4 := by
      intro name hlookup hwfName
      simp [Flapjack.Pancake.PanLang.isWfShapeExactHOL, hlookup] at hwfName)
    (case5 := by
      intro _
      rfl)
    (case6 := by
      intro child rest ihChild ihRest hwfRest
      simp only [Flapjack.Pancake.PanLang.isWfShapesExactHOL, Bool.and_eq_true] at hwfRest
      obtain ⟨hwfChild, hwfTail⟩ := hwfRest
      simp only [Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL]
      rw [ihChild hwfChild, ihRest hwfTail])
    shape
  exact hrec hwf

/-- Exact port of HOL `v_flds_ok_append` (`pan_structsProofScript.sml:522`).
    Its value, context keys, field keys, and shape keys are the faithful HOL
    carriers: `ValueHOL`, `MlString`, `ShapeHOL`, and `StructContextExact`.
    The premises and conclusion match HOL: validity in `ctxt`, distinct keys
    across `pfx ++ ctxt`, then validity in the appended context. The direct
    HOL EVAL fixture is `v_flds_ok_append_nonempty_prefix_named` in
    `pan_structs_value_validity_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "v_flds_ok_append"]
theorem valueFldsOkHOLExact_append {width : Nat} [NeZero width]
    (ctxt pfx : StructContextExact) (value : ValueHOL width)
    (hvalue : valueFldsOkHOLExact ctxt value = true)
    (hkeys : (pfx.map Prod.fst ++ ctxt.map Prod.fst).Nodup) :
    valueFldsOkHOLExact (pfx ++ ctxt) value = true := by
  revert hvalue hkeys pfx
  apply valueFldsOkHOLExact.induct
    (motive1 := fun value =>
      ∀ pfx, valueFldsOkHOLExact ctxt value = true →
        (pfx.map Prod.fst ++ ctxt.map Prod.fst).Nodup →
          valueFldsOkHOLExact (pfx ++ ctxt) value = true)
    (motive2 := fun fields =>
      ∀ pfx, fieldsFldsOkHOLExact ctxt fields = true →
        (pfx.map Prod.fst ++ ctxt.map Prod.fst).Nodup →
          fieldsFldsOkHOLExact (pfx ++ ctxt) fields = true)
    (motive3 := fun values =>
      ∀ pfx, valuesFldsOkHOLExact ctxt values = true →
        (pfx.map Prod.fst ++ ctxt.map Prod.fst).Nodup →
          valuesFldsOkHOLExact (pfx ++ ctxt) values = true)
  · intro word pfx hvalue hkeys
    simp [valueFldsOkHOLExact]
  · intro values ih pfx hvalue hkeys
    simpa [valueFldsOkHOLExact] using ih pfx
      (by simpa [valueFldsOkHOLExact] using hvalue) hkeys
  · intro name fields ih pfx hvalue hkeys
    simp only [valueFldsOkHOLExact, Bool.and_eq_true] at hvalue ⊢
    cases hlookup : Flapjack.Pancake.PanLang.structContextLookupHOL name ctxt with
    | none => simp [hlookup] at hvalue
    | some info =>
        simp only [hlookup, Bool.and_eq_true] at hvalue
        obtain ⟨hfields, hnames, hshapes⟩ := hvalue
        have hlookupExtended := structContextLookupHOL_append_eq_of_some
          pfx ctxt name info hkeys hlookup
        simp only [hlookupExtended, Bool.and_eq_true]
        exact ⟨ih pfx hfields hkeys, hnames, hshapes⟩
  · intro pfx hvalue hkeys
    simp [fieldsFldsOkHOLExact]
  · intro name value fields ihValue ihFields pfx hvalue hkeys
    simp only [fieldsFldsOkHOLExact, Bool.and_eq_true] at hvalue ⊢
    exact ⟨ihValue pfx hvalue.1 hkeys, ihFields pfx hvalue.2 hkeys⟩
  · intro pfx hvalue hkeys
    simp [valuesFldsOkHOLExact]
  · intro value values ihValue ihValues pfx hvalue hkeys
    simp only [valuesFldsOkHOLExact, Bool.and_eq_true] at hvalue ⊢
    exact ⟨ihValue pfx hvalue.1 hkeys, ihValues pfx hvalue.2 hkeys⟩

mutual
  /-- Bool-valued comparison for HOL `v_flds_ok_def`, using production
      `lookupInfo`. This is not currently tagged as an exact port: the HOL
      predicate uses HOL equality in `ALOOKUP`, while this declaration calls
      `lookupInfo` at the canonical String equality instance. An exact
      clause-by-clause comparison of the recursive shape and field checks
      against HOL is still required before claiming the tag. Lean `StructInfo`
      also has an additional `shapedFields` cache absent from HOL.
      This Bool declaration is distinct from the Prop-valued convenience
      predicate below. -/
  def panStructValueFieldsOkBool (structs : StructContext) :
      PanValue α → Bool
    | .word _ => true
    | .rStruct values => panStructValuesFieldsOkBool structs values
    | .nStruct name fields =>
        panStructFieldValuesFieldsOkBool structs fields &&
          match lookupInfo name structs with
          | none => false
          | some info => panValueFieldsHaveShapes structs info.fields fields
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructValuesFieldsOkBool (structs : StructContext) :
      List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panStructValueFieldsOkBool structs value &&
          panStructValuesFieldsOkBool structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructFieldValuesFieldsOkBool (structs : StructContext) :
      List (FieldName × PanValue α) → Bool
    | [] => true
    | (_, value) :: fields =>
        panStructValueFieldsOkBool structs value &&
          panStructFieldValuesFieldsOkBool structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Prop-valued Flapjack convenience predicate mirroring the equations of
      HOL `v_flds_ok_def`. It is not an exact port: HOL returns Bool, while
      this declaration returns Prop and uses `[BEq String]` lookup. -/
  def panStructValueFieldsOk [BEq String] (structs : StructContext) :
      PanValue α → Prop
    | .word _ => True
    | .rStruct values => panStructValuesFieldsOk structs values
    | .nStruct name fields =>
        panStructFieldValuesFieldsOk structs fields ∧
          match lookupInfo name structs with
          | none => False
          | some info =>
              fields.map Prod.fst = info.fields.map Prod.fst ∧
                fields.map (panSemShapeOf ∘ Prod.snd) = info.fields.map Prod.snd
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructValuesFieldsOk [BEq String] (structs : StructContext) :
      List (PanValue α) → Prop
    | [] => True
    | value :: values =>
        panStructValueFieldsOk structs value ∧ panStructValuesFieldsOk structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructFieldValuesFieldsOk [BEq String] (structs : StructContext) :
      List (FieldName × PanValue α) → Prop
    | [] => True
    | (_, value) :: fields =>
        panStructValueFieldsOk structs value ∧ panStructFieldValuesFieldsOk structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Prop-valued Flapjack convenience predicate mirroring the equations of
      HOL `is_wf_shape_v_def`. It is not an exact port: HOL returns Bool, while
      this declaration returns Prop and uses `[BEq String]` lookup. -/
  def panStructValueShapeWf [BEq String] (structs : StructContext) :
      PanValue α → Prop
    | .word _ => True
    | .rStruct values => panStructValuesShapeWf structs values
    | .nStruct name fields =>
        (lookupInfo name structs ≠ none) ∧ panStructFieldValuesShapeWf structs fields
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructValuesShapeWf [BEq String] (structs : StructContext) :
      List (PanValue α) → Prop
    | [] => True
    | value :: values =>
        panStructValueShapeWf structs value ∧ panStructValuesShapeWf structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructFieldValuesShapeWf [BEq String] (structs : StructContext) :
      List (FieldName × PanValue α) → Prop
    | [] => True
    | (_, value) :: fields =>
        panStructValueShapeWf structs value ∧ panStructFieldValuesShapeWf structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- FEVERY adapters for PanSemState's total lookup functions. The shape-map
    premise below supplies finite support, so these universal clauses are the
    function-view translation of the HOL finite-map predicates. -/
def panStructEveryValueFieldsOk [BEq String] (structs : StructContext)
    (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value → panStructValueFieldsOk structs value

def panStructEveryValueShapeWf [BEq String] (structs : StructContext)
    (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value → panStructValueShapeWf structs value


def panStructEveryValueShapeWfBool [BEq String]
    (structs : StructContext) (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value →
    panIsWfShapeValueBool structs value = true



/-- Executable list-map counterpart of HOL `convert_code_def`. It converts
    each source-owned code entry and uses the original parameter shapes while
    compiling the body, as HOL does with `ctxt with locals := params`.
    This is intentionally untagged: HOL maps a finite map with unique keys,
    while `PanSemCodeMap` is an `InfoMap` list which may contain duplicate
    keys; this definition maps every list entry and cannot express HOL's
    finite-map domain invariant. -/
def panStructConvertCode [BEq String] (context : StructPassContext)
    (code : PanSemCodeMap α) : PanSemCodeMap α :=
  code.map fun (name, (parameters, body, returnShape)) =>
    (name,
      (parameters.map fun (parameter, shape) =>
          (parameter, structCompileShape context.structs shape),
        structCompileProg { context with locals := parameters } body,
        structCompileShape context.structs returnShape))

/-- Executable projection of HOL `convert_s_def` over `PanSemState`.
    The `structs` update and value conversion follow HOL; `code` is projected
    through the list-map helper above, and exception shapes through a total
    lookup function. This is intentionally untagged: `locals`, `globals`, and
    exception shapes are total lookup functions rather than finite maps, while
    code is an `InfoMap` list that may have duplicate keys. These interfaces
    cannot express HOL finite-map support or its exact `FMAP_MAP2` equations.
    The faithful finite-map state conversion remains open. -/
def panStructConvertState [BEq String] (context : StructPassContext)
    (state : PanSemState α ffi) : PanSemState α ffi where
  locals := fun name => (state.locals name).map panStructConvertValue
  globals := fun name => (state.globals name).map panStructConvertValue
  structs := []
  code := panStructConvertCode context state.code
  exceptionShapes := fun exception =>
    (state.exceptionShapes exception).map (structCompileShape context.structs)
  memory := state.memory
  memaddrs := state.memaddrs
  sharedMemaddrs := state.sharedMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddress := state.baseAddress
  topAddress := state.topAddress

/-- The `pan_structs` value conversion preserves `PanValueByteRanged`: the word
    case is unchanged, `rStruct` carries the predicate over the converted field
    list, and `nStruct` drops its record and field names and converts only the
    field values, so the name-range obligations disappear. The proof is the
    simultaneous induction over the three mutually recursive convert functions.
    Untagged Flapjack plumbing. -/
theorem panValueByteRanged_panStructConvertValue {width : Nat} [NeZero width]
    (value : PanValue (BitVec width)) :
    PanValueByteRanged (panStructConvertValue value) :=
  panStructConvertValue.induct
    (fun value => PanValueByteRanged (panStructConvertValue value))
    (fun fields => ∀ value ∈ panStructConvertFieldValues fields,
      PanValueByteRanged value)
    (fun values => ∀ value ∈ panStructConvertValues values,
      PanValueByteRanged value)
    (fun v => by simp only [panStructConvertValue, PanValueByteRanged])
    (fun fields ih => by
      simp only [panStructConvertValue, PanValueByteRanged]
      exact ih)
    (fun name fields ih => by
      simp only [panStructConvertValue, PanValueByteRanged]
      exact ih)
    (fun v hv => by simp only [panStructConvertFieldValues] at hv; cases hv)
    (fun fst value fields ihv ihfs v hv => by
      simp only [panStructConvertFieldValues, List.mem_cons] at hv
      rcases hv with h | h
      · rw [h]; exact ihv
      · exact ihfs v h)
    (fun v hv => by simp only [panStructConvertValues] at hv; cases hv)
    (fun value values ihv ihvs v hv => by
      simp only [panStructConvertValues, List.mem_cons] at hv
      rcases hv with h | h
      · rw [h]; exact ihv
      · exact ihvs v h)
    value

/-- Globals of the concrete `pan_structs` state conversion are byte-ranged when
    produced from any source state: the stored value is routed through
    `panStructConvertValue`. Untagged Flapjack plumbing. -/
theorem panValueByteRanged_of_globals_panStructConvertState {σ : Type}
    [BEq String] (context : StructPassContext)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    ∀ name value, (panStructConvertState context state).globals name = some value →
      PanValueByteRanged value := by
  intro name value h
  simp only [panStructConvertState] at h
  cases hg : state.globals name with
  | none => simp [hg] at h
  | some v =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact panValueByteRanged_panStructConvertValue v

/-- Locals of the concrete `pan_structs` state conversion are byte-ranged when
    produced from any source state: the stored value is routed through
    `panStructConvertValue`. Untagged Flapjack plumbing. -/
theorem panValueByteRanged_of_locals_panStructConvertState {σ : Type}
    [BEq String] (context : StructPassContext)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    ∀ name value, (panStructConvertState context state).locals name = some value →
      PanValueByteRanged value := by
  intro name value h
  simp only [panStructConvertState] at h
  cases hg : state.locals name with
  | none => simp [hg] at h
  | some v =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact panValueByteRanged_panStructConvertValue v

/-- The concrete `pan_structs` state conversion lands in the ranged executable
    state relation `PanSemStateRelExecRanged`: converted locals and globals are
    byte-ranged and the converted structure context is `[]`. This discharges the
    initial-state locals and globals byte-range conjuncts for the state produced
    after the pass. Untagged Flapjack plumbing. -/
theorem panSemStateRelExecRanged_panStructConvertState {σ : Type}
    [BEq String] (context : StructPassContext)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanSemStateRelExecRanged (panStructConvertState context state) := by
  refine ⟨?_, ?_, ?_⟩
  · exact panValueByteRanged_of_locals_panStructConvertState context state
  · exact panValueByteRanged_of_globals_panStructConvertState context state
  · simp [panStructConvertState, StructContext.toHOL,
      Pancake.PanLang.StructContextByteRanged]


inductive PanStructAll {α : Type} (predicate : α → Prop) : List α → Prop
  | nil : PanStructAll predicate []
  | cons {head tail} : predicate head → PanStructAll predicate tail →
      PanStructAll predicate (head :: tail)


/-- Flapjack-specific name-forgetful map from the exact `panSem$v` carrier to the
    executable `PanValue`, decoding `mlstring` records/fields by their bytes. It
    states the production bridge for the exact `convert_v` port and has no HOL
    counterpart. -/
def ValueHOL.toPanValue {width : Nat} [NeZero width] :
    ValueHOL width → PanValue (BitVec width)
  | .val (.word bits) => .word bits
  | .rStruct fields => .rStruct (fields.map ValueHOL.toPanValue)
  | .nStruct name fields =>
      .nStruct (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
        (fields.map (fun pair =>
          (Flapjack.Basis.Pure.MlString.toStringOfBytes pair.1,
            ValueHOL.toPanValue pair.2)))
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
    | (rename_i hmem
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)
    | (rename_i hmem
       have hsnd : sizeOf pair.snd < sizeOf pair := by cases pair; simp +arith
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)


/-! One/Comb branch of HOL `mem_load_conversion` at
    `pan_structsProofScript.sml:609`. This support theorem relates the
    production fuel-indexed loader across `structCompileShapeWF`; it is
    intentionally untagged because HOL's `mem_load` uses a finite address
    domain and word-labelled state memory, while this helper is stated over
    the production `readWord` callback. The no-named-shape premise isolates
    precisely the One/Comb induction branches. -/

private theorem panValueFlatFieldsFuel_eq_shapeListFuel
    (fields : List (FieldName × Shape)) :
    panValueFlatFieldsFuel fields =
      panValueFlatShapeFuel.panValueFlatShapeListFuel (fields.map Prod.snd) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      cases field
      simp [panValueFlatFieldsFuel, panValueFlatShapeFuel.panValueFlatShapeListFuel, ih]

/-! General `Named` load conversion used by the HOL `mem_load_conversion`
    step. This theorem is untagged: production loading is `Option`-valued with
    explicit `bytesInWord` and a `readWord` callback, whereas HOL uses a finite
    address domain and word-labelled memory. -/


mutual
  private theorem panValueShape_eq_panSemShapeOf (context : StructContext)
      (value : PanValue α) :
      panValueShape context value = panSemShapeOf value := by
    cases value with
    | word value => rw [panValueShape.eq_1, panSemShapeOf.eq_1]
    | nStruct name fields => rw [panValueShape.eq_3, panSemShapeOf.eq_3]
    | rStruct values =>
        rw [panValueShape.eq_2, panSemShapeOf.eq_2]
        exact congrArg Shape.comb
          (panValueShapeList_eq_panSemShapeOf context values)

  private theorem panValueShapeList_eq_panSemShapeOf (context : StructContext)
      (values : List (PanValue α)) :
      values.map (panValueShape context) = values.map panSemShapeOf := by
    cases values with
    | nil => rfl
    | cons value values =>
        simp only [List.map_cons]
        rw [panValueShape_eq_panSemShapeOf, panValueShapeList_eq_panSemShapeOf]
end


/-- Boolean rearrangement used when comparing the pairwise production field
    check with the whole-list HOL shape/name equalities. -/
theorem boolAndRearr (left shape names shapes : Bool) :
    (left && shape && (names && shapes)) = ((left && names) && (shape && shapes)) := by
  cases left <;> cases shape <;> cases names <;> cases shapes <;> rfl

/-- String `==` is symmetric, used to reorient the pairwise field-name check
    against the HOL whole-list `MAP FST` equality. -/
theorem string_beq_comm (left right : String) :
    (left == right) = (right == left) := by
  by_cases h : left = right
  · rw [beq_iff_eq.mpr h, beq_iff_eq.mpr h.symm]
  · have h' : ¬ right = left := fun hba => h hba.symm
    rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

/- The production `panShapeMatches` agrees with the constructor-recursive
    `panStructShapeEqBool` under lawful String equality. -/
mutual
  theorem panShapeMatches_eq_panStructShapeEqBool [LawfulBEq String]
      (left right : Shape) :
      panShapeMatches left right = panStructShapeEqBool left right := by
    cases left with
    | one => cases right <;> simp [panShapeMatches, panStructShapeEqBool]
    | named leftName =>
        cases right with
        | one => simp [panShapeMatches, panStructShapeEqBool]
        | named rightName =>
            simp only [panShapeMatches, panStructShapeEqBool]
            by_cases h : leftName = rightName
            · rw [beq_iff_eq.mpr h, decide_eq_true h]
            · rw [beq_eq_false_iff_ne.mpr h, decide_eq_false h]
        | comb _ => simp [panShapeMatches, panStructShapeEqBool]
    | comb leftFields =>
        cases right with
        | one => simp [panShapeMatches, panStructShapeEqBool]
        | named _ => simp [panShapeMatches, panStructShapeEqBool]
        | comb rightFields =>
            simp only [panShapeMatches, panStructShapeEqBool]
            exact panShapeListMatches_eq_panStructShapeListEqBool leftFields rightFields

  theorem panShapeListMatches_eq_panStructShapeListEqBool [LawfulBEq String]
      (left right : List Shape) :
      panShapeMatches.panShapeListMatches left right = panStructShapeListEqBool left right := by
    cases left with
    | nil => cases right <;> simp [panShapeMatches.panShapeListMatches, panStructShapeListEqBool]
    | cons head tail =>
        cases right with
        | nil => simp [panShapeMatches.panShapeListMatches, panStructShapeListEqBool]
        | cons head' tail' =>
            simp only [panShapeMatches.panShapeListMatches, panStructShapeListEqBool]
            rw [panShapeMatches_eq_panStructShapeEqBool head head']
            exact congrArg (fun rest => panStructShapeEqBool head head' && rest)
              (panShapeListMatches_eq_panStructShapeListEqBool tail tail')
end

/-- The production pairwise `panValueFieldsHaveShapes` check is exactly HOL's
    whole-list `MAP FST flds = MAP FST info.fields /\
    MAP (shape_of o SND) flds = MAP SND info.fields` conjunction. -/
theorem panValueFieldsHaveShapes_eq [LawfulBEq String] (context : StructContext)
    (expected : List (FieldName × Shape)) (actual : List (FieldName × PanValue α)) :
    panValueFieldsHaveShapes context expected actual =
      ((actual.map Prod.fst == expected.map Prod.fst) &&
        panStructShapeListEqBool
          (actual.map (panSemShapeOf ∘ Prod.snd))
          (expected.map Prod.snd)) := by
  induction expected generalizing actual with
  | nil =>
      cases actual with
      | nil => simp [panValueFieldsHaveShapes, panStructShapeListEqBool]
      | cons head tail => simp [panValueFieldsHaveShapes]
  | cons expectedHead expectedTail ih =>
      obtain ⟨expectedName, expectedShape⟩ := expectedHead
      cases actual with
      | nil => simp [panValueFieldsHaveShapes]
      | cons actualHead actualTail =>
          obtain ⟨actualName, actualValue⟩ := actualHead
          simp only [panValueFieldsHaveShapes, List.map_cons,
            panStructShapeListEqBool, Function.comp_apply]
          rw [ih actualTail, panShapeMatches_eq_panStructShapeEqBool,
            panValueShape_eq_panSemShapeOf, string_beq_comm expectedName actualName]
          exact boolAndRearr (actualName == expectedName)
            (panStructShapeEqBool (panSemShapeOf actualValue) expectedShape)
            (actualTail.map Prod.fst == expectedTail.map Prod.fst)
            (panStructShapeListEqBool (actualTail.map (panSemShapeOf ∘ Prod.snd))
              (expectedTail.map Prod.snd))

/- Full clause-by-clause adapter for HOL `v_flds_ok_def`: the exact
    HOL-shaped `panValueFldsOk` over the projected context equals the
    production `panStructValueFieldsOkBool` over the cache-augmented context. -/
mutual
  theorem panValueFldsOk_toHOL [LawfulBEq String] (context : StructContext)
      (value : PanValue α) :
      panValueFldsOk context.toHOL value = panStructValueFieldsOkBool context value := by
    cases value with
    | word word => simp [panValueFldsOk, panStructValueFieldsOkBool]
    | rStruct values =>
        simp only [panValueFldsOk, panStructValueFieldsOkBool]
        exact panValuesFldsOk_toHOL context values
    | nStruct name fields =>
        simp only [panValueFldsOk, panStructValueFieldsOkBool, lookupInfo_toHOL]
        rw [panFieldsFldsOk_toHOL context fields]
        cases hlookup : lookupInfo name context with
        | none => simp
        | some info =>
            simp only [Option.map_some]
            rw [panValueFieldsHaveShapes_eq]

  theorem panValuesFldsOk_toHOL [LawfulBEq String] (context : StructContext)
      (values : List (PanValue α)) :
      panValuesFldsOk context.toHOL values = panStructValuesFieldsOkBool context values := by
    cases values with
    | nil => simp [panValuesFldsOk, panStructValuesFieldsOkBool]
    | cons value values =>
        simp only [panValuesFldsOk, panStructValuesFieldsOkBool]
        rw [panValueFldsOk_toHOL context value, panValuesFldsOk_toHOL context values]

  theorem panFieldsFldsOk_toHOL [LawfulBEq String] (context : StructContext)
      (fields : List (FieldName × PanValue α)) :
      panFieldsFldsOk context.toHOL fields = panStructFieldValuesFieldsOkBool context fields := by
    cases fields with
    | nil => simp [panFieldsFldsOk, panStructFieldValuesFieldsOkBool]
    | cons field fields =>
        obtain ⟨fieldName, value⟩ := field
        simp only [panFieldsFldsOk, panStructFieldValuesFieldsOkBool]
        rw [panValueFldsOk_toHOL context value, panFieldsFldsOk_toHOL context fields]
end

private theorem panStructRStructListShapeFields
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Sub α]
    [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α))
    (hinduction : PanStructAll (fun expression => ∀ subvalue,
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        expression = some subvalue →
      structOldExpShape context expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool structs subvalue = true) expressions)
    (values : List (PanValue α))
    (hvalues : evalPanValueExps structs locals globals memory baseAddress topAddress
      bytesInWord expressions = some values) :
    structOldExpShape.structOldExpShapes context expressions = values.map panSemShapeOf ∧
    panStructValuesFieldsOkBool structs values = true := by
  revert hinduction values hvalues
  induction expressions with
  | nil =>
      intro hinduction values hvalues
      cases hinduction
      simp [evalPanValueExps, evalPanValueExp.evalPanValueExps] at hvalues
      subst values
      exact ⟨by simp [structOldExpShape.structOldExpShapes],
        by simp [panStructValuesFieldsOkBool]⟩
  | cons expression expressions ih =>
      intro hinduction values hvalues
      cases hinduction with
      | cons ihHead ihTail =>
          simp only [evalPanValueExps, evalPanValueExp.evalPanValueExps] at hvalues
          cases hhead : evalPanValueExp structs locals globals memory
              baseAddress topAddress bytesInWord expression with
          | none => simp [hhead] at hvalues
          | some head =>
              cases htail : evalPanValueExp.evalPanValueExps structs locals globals memory
                  baseAddress topAddress bytesInWord expressions with
              | none => simp [hhead, htail] at hvalues
              | some tail =>
                  have hvaluesEq : head :: tail = values := by
                    simpa [hhead, htail] using hvalues
                  subst values
                  have hheadFacts := ihHead head hhead
                  have htailFacts := ih ihTail tail
                    (by simpa [evalPanValueExps] using htail)
                  exact ⟨by simp [structOldExpShape.structOldExpShapes,
                    hheadFacts.1, htailFacts.1], by
                    simp [panStructValuesFieldsOkBool, hheadFacts.2, htailFacts.2]⟩


theorem panStruct_mapKeys_preserved (entries : InfoMap α)
    (transform : String × α → String × β)
    (htransform : ∀ entry, (transform entry).1 = entry.1) :
    (entries.map transform).map Prod.fst = entries.map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      simp [ih, htransform]

/-- A finite-map representation of the map-valued fields in HOL's
    `panSem$state`, together with its exact lookup view in the production
    `PanSemState` evaluator. `entries` are authoritative; the agreement fields
    make locals, globals, and exception-shape lookup use HOL equality directly.
    The `LawfulBEq String` parameter ensures production code-map lookup agrees
    with equality-based HOL `FLOOKUP`. `Nodup` records the key uniqueness
    inherent in HOL finite maps. -/
structure PanStructFiniteState [BEq String] [LawfulBEq String]
    (α : Type u) (ffi : Type v) where
  runtime : PanSemState α ffi
  locals : InfoMap (PanValue α)
  globals : InfoMap (PanValue α)
  exceptionShapes : InfoMap Shape
  locals_nodup : (locals.map Prod.fst).Nodup
  globals_nodup : (globals.map Prod.fst).Nodup
  exceptionShapes_nodup : (exceptionShapes.map Prod.fst).Nodup
  code_nodup : (runtime.code.map Prod.fst).Nodup
  locals_lookup : ∀ name, runtime.locals name = panPropsALookupEq name locals
  globals_lookup : ∀ name, runtime.globals name = panPropsALookupEq name globals
  exceptionShapes_lookup :
    ∀ name, runtime.exceptionShapes name = panPropsALookupEq name exceptionShapes

/-- Build the production evaluator view from explicit HOL-shaped finite maps.
    The only side conditions are the key uniqueness conditions that are part
    of the finite-map representation itself; lookup agreement is constructed
    definitionally instead of being added as a theorem premise. -/
def panStructFiniteStateFromMaps [BEq String] [LawfulBEq String]
    (runtime : PanSemState α ffi)
    (locals globals : InfoMap (PanValue α)) (exceptionShapes : InfoMap Shape)
    (code : PanSemCodeMap α)
    (locals_nodup : (locals.map Prod.fst).Nodup)
    (globals_nodup : (globals.map Prod.fst).Nodup)
    (exceptionShapes_nodup : (exceptionShapes.map Prod.fst).Nodup)
    (code_nodup : (code.map Prod.fst).Nodup) : PanStructFiniteState α ffi where
  runtime := { runtime with
    locals := fun name => panPropsALookupEq name locals
    globals := fun name => panPropsALookupEq name globals
    exceptionShapes := fun name => panPropsALookupEq name exceptionShapes
    code := code }
  locals := locals
  globals := globals
  exceptionShapes := exceptionShapes
  locals_nodup := locals_nodup
  globals_nodup := globals_nodup
  exceptionShapes_nodup := exceptionShapes_nodup
  code_nodup := code_nodup
  locals_lookup := by
    cases runtime
    intro name
    simp
  globals_lookup := by
    cases runtime
    intro name
    simp
  exceptionShapes_lookup := by
    cases runtime
    intro name
    simp

/-- Map all HOL finite-map fields while keeping the same finite key support.
    The result is again related to the production evaluator state by exact
    lookup equations. -/
def panStructConvertFiniteState [BEq String] [LawfulBEq String]
    (context : StructPassContext) (state : PanStructFiniteState α ffi) :
    PanStructFiniteState α ffi where
  runtime := panStructConvertState context state.runtime
  locals := state.locals.map fun (name, value) =>
    (name, panStructConvertValue value)
  globals := state.globals.map fun (name, value) =>
    (name, panStructConvertValue value)
  exceptionShapes := state.exceptionShapes.map fun (name, shape) =>
    (name, structCompileShape context.structs shape)
  locals_nodup := by
    rw [panStruct_mapKeys_preserved state.locals
      (fun (name, value) => (name, panStructConvertValue value))]
    · exact state.locals_nodup
    · intro entry
      rfl
  globals_nodup := by
    rw [panStruct_mapKeys_preserved state.globals
      (fun (name, value) => (name, panStructConvertValue value))]
    · exact state.globals_nodup
    · intro entry
      rfl
  exceptionShapes_nodup := by
    rw [panStruct_mapKeys_preserved state.exceptionShapes
      (fun (name, shape) => (name, structCompileShape context.structs shape))]
    · exact state.exceptionShapes_nodup
    · intro entry
      rfl
  code_nodup := by
    change ((panStructConvertCode context state.runtime.code).map Prod.fst).Nodup
    rw [show (panStructConvertCode context state.runtime.code).map Prod.fst =
        state.runtime.code.map Prod.fst by
          apply panStruct_mapKeys_preserved
          intro entry
          cases entry with
          | mk name value => rfl]
    exact state.code_nodup
  locals_lookup := by
    intro name
    simp [panStructConvertState, panPropsALookupEq_mapValues, state.locals_lookup]
  globals_lookup := by
    intro name
    simp [panStructConvertState, panPropsALookupEq_mapValues, state.globals_lookup]
  exceptionShapes_lookup := by
    intro name
    simp [panStructConvertState, panPropsALookupEq_mapValues,
      state.exceptionShapes_lookup]

@[simp] theorem panStructConvertFiniteState_locals_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).locals.map Prod.fst =
      state.locals.map Prod.fst := by
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

@[simp] theorem panStructConvertFiniteState_globals_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).globals.map Prod.fst =
      state.globals.map Prod.fst := by
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

@[simp] theorem panStructConvertFiniteState_exceptionShapes_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).exceptionShapes.map Prod.fst =
      state.exceptionShapes.map Prod.fst := by
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

@[simp] theorem panStructConvertFiniteState_code_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).runtime.code.map Prod.fst =
      state.runtime.code.map Prod.fst := by
  change (panStructConvertCode context state.runtime.code).map Prod.fst =
    state.runtime.code.map Prod.fst
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

def panStructConvertLocalMap (locals : VarName → Option (PanValue α)) :=
  fun name => (locals name).map panStructConvertValue

def panStructConvertControlResult : PanValueFfiControlResult α σ →
    PanValueFfiControlResult α σ
  | .normal locals globals memory ffi =>
      .normal (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .error locals globals memory ffi =>
      .error (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .returned locals globals memory ffi values =>
      .returned (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi (panStructConvertValues values)
  | .raised locals globals memory ffi exception value =>
      .raised (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi exception (panStructConvertValue value)
  | .broke locals globals memory ffi =>
      .broke (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .continued locals globals memory ffi =>
      .continued (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .finalFfi locals globals memory ffi event =>
      .finalFfi (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi event

def panStructConvertClockOutcome : PanValueFfiClockOutcome α σ →
    PanValueFfiClockOutcome α σ
  | .control result => .control (panStructConvertControlResult result)
  | .timeout locals globals memory ffi =>
      .timeout (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi

def panStructConvertClockResult (result : PanValueFfiClockResult α σ) :
    PanValueFfiClockResult α σ :=
  (panStructConvertClockOutcome result.1, result.2)

@[simp] theorem panStructConvertState_code [BEq String]
    (context : StructPassContext) (state : PanSemState α ffi) :
    (panStructConvertState context state).code =
      panStructConvertCode context state.code := rfl

@[simp] theorem panStructCompileSkip_eq_skip [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.skip : Prog α) = .skip := by
  simp [structCompileProg]

@[simp] theorem panStructCompileBreak_eq_break [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.break : Prog α) = .break := by
  simp [structCompileProg]




end Flapjack
