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

/-- Flapjack-specific name-forgetful map from the exact `panSem$v` carrier to the
    executable `PanValue`, decoding `mlstring` records/fields by their bytes.
    This conversion has no independent HOL counterpart. -/
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



end Flapjack
