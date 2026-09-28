import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge

/-!
# Production/exact `lookup_code` correspondence for the total panSem bridge

The production total evaluator `panSemTotalEvaluate` looks a callee up with
`panSemTotalCodeLookup` (through `lookupPanSemCodeCall`, `PanBst.lean:106`),
while the exact evaluator `evaluateHOLFiniteState` uses `lookupCodeHOLFinite`,
the finite-support rendering of HOL `lookup_code_def`
(`cakeml/pancake/semantics/panSemScript.sml:458-467`).  This module proves the
two lookups agree under `PanSemStateRelExec`: both fail, or both succeed with
the exact body `progToHOL` of the production body, the encoded return shape, and
callee locals related on every `NameRanged` name.

The correspondence needs the looked-up production code entry to be byte-ranged
(`PanLangEntryByteRanged`, `StateBridge.lean:224`): the formal names must be `NameRanged` so that
`ofString` preserves distinctness, and the formal shapes must be
`ShapeByteRanged` so that production `panShapeMatches` coincides with HOL
`shape_eq`.  `PanSemStateRelExecRanged` constrains only locals, globals and the
structure context, so code-entry rangedness is an explicit premise here; it is
part of the rangedness boundary tracked by `flapjack-pxn.18.4.3.77.2.15`.

Everything here is untagged Flapjack-specific bridge infrastructure.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

/-- `ofString` preserves and reflects distinctness of a list of ranged names. -/
theorem nodup_map_ofString_iff (names : List String)
    (hnames : ∀ name ∈ names, NameRanged name) :
    (names.map ofString).Nodup ↔ names.Nodup := by
  induction names with
  | nil => simp
  | cons name names ih =>
      have htail : ∀ n ∈ names, NameRanged n := fun n hn => hnames n (by simp [hn])
      have hhead : NameRanged name := hnames name (by simp)
      simp only [List.map_cons, List.nodup_cons, ih htail]
      constructor
      · rintro ⟨hnot, hnd⟩
        refine ⟨fun hmem => hnot (List.mem_map.mpr ⟨name, hmem, rfl⟩), hnd⟩
      · rintro ⟨hnot, hnd⟩
        refine ⟨fun hmem => ?_, hnd⟩
        obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
        have := ofString_injective_of_ranged (htail other hother) hhead heq
        exact hnot (this ▸ hother)

/-- The production argument-shape check agrees with HOL `lookup_code`'s length
    and pointwise `shape_eq (shape_of arg) formal` test on the encoded lists,
    for byte-ranged formal shapes and argument values. -/
theorem panSemCodeArgumentsMatch_iff_HOL (structs : StructContext)
    (parameters : List (VarName × Shape)) (values : List (PanValue (RiscV.Word 64)))
    (hparameters : ∀ parameter ∈ parameters, ShapeByteRanged parameter.2)
    (hvalues : ∀ value ∈ values, PanValueByteRanged value) :
    panSemCodeArgumentsMatch structs parameters values = true ↔
      ((parameters.map paramToHOL).length = (values.map panValueToHOL).length ∧
        ((parameters.map paramToHOL).zip (values.map panValueToHOL)).all
          (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true) := by
  induction parameters generalizing values with
  | nil => cases values <;> simp [panSemCodeArgumentsMatch]
  | cons parameter parameters ih =>
      cases values with
      | nil => simp [panSemCodeArgumentsMatch]
      | cons value values =>
          have hps : ∀ p ∈ parameters, ShapeByteRanged p.2 :=
            fun p hp => hparameters p (by simp [hp])
          have hvs : ∀ v ∈ values, PanValueByteRanged v :=
            fun v hv => hvalues v (by simp [hv])
          have hhead : panShapeMatches (panValueShape structs value) parameter.2 =
              shapeEqHOL (paramToHOL parameter).2 (shapeOfHOLExact (panValueToHOL value)) := by
            rw [panShapeMatches_comm, shapeOfHOLExact_panValueToHOL structs value,
              panShapeMatches_eq_shapeEqHOL _ _ (hparameters parameter (by simp))
                (panValueShape_byteRanged structs value (hvalues value (by simp)))]
            rfl
          simp only [panSemCodeArgumentsMatch, List.map_cons, List.length_cons,
            List.zip_cons_cons, List.all_cons, Bool.and_eq_true, hhead, ih values hps hvs,
            Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
          · rintro ⟨h2, h1, h3⟩; exact ⟨h1, h2, h3⟩

/-- The production parameter-binding fold and HOL's `FEMPTY |++ ZIP` fold (as
    the function-update fold of `lookupCodeHOLExact`) agree on every
    `NameRanged` name, and the production result holds only listed values. -/
theorem bindFold_agree (entries : List (VarName × PanValue (RiscV.Word 64)))
    (hnames : ∀ entry ∈ entries, NameRanged entry.1)
    (production : VarName → Option (PanValue (RiscV.Word 64)))
    (exact : MlS → Option (ValueHOL 64))
    (hrel : ∀ name, NameRanged name →
      Option.map panValueToHOL (production name) = exact (ofString name)) :
    ∀ name, NameRanged name →
      Option.map panValueToHOL
          (entries.foldl (fun locals (entry : VarName × PanValue (RiscV.Word 64)) =>
            updatePanValueMap locals entry.1 entry.2) production name) =
        (entries.map (fun entry => (ofString entry.1, panValueToHOL entry.2))).foldl
          (fun (map : MlS → Option (ValueHOL 64)) (entry : MlS × ValueHOL 64) =>
            fun current => if current = entry.1 then some entry.2 else map current)
          exact (ofString name) := by
  induction entries generalizing production exact with
  | nil => simpa using hrel
  | cons entry entries ih =>
      simp only [List.foldl_cons, List.map_cons]
      apply ih (fun e he => hnames e (by simp [he]))
      intro name hname
      have hentry : NameRanged entry.1 := hnames entry (by simp)
      simp only [updatePanValueMap]
      by_cases heq : name = entry.1
      · subst heq
        simp
      · have hne : ofString name ≠ ofString entry.1 :=
          fun h => heq (ofString_injective_of_ranged hname hentry h)
        simp [heq, hne, hrel name hname]

/-- Every value held by the production binding fold is either an initial value
    or one of the listed values. -/
theorem bindFold_values (entries : List (VarName × PanValue (RiscV.Word 64)))
    (production : VarName → Option (PanValue (RiscV.Word 64)))
    (P : PanValue (RiscV.Word 64) → Prop)
    (hentries : ∀ entry ∈ entries, P entry.2)
    (hinit : ∀ name value, production name = some value → P value) :
    ∀ name value,
      entries.foldl (fun locals (entry : VarName × PanValue (RiscV.Word 64)) =>
        updatePanValueMap locals entry.1 entry.2) production name = some value →
      P value := by
  induction entries generalizing production with
  | nil => simpa using hinit
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      apply ih _ (fun e he => hentries e (by simp [he]))
      intro name value h
      simp only [updatePanValueMap] at h
      split at h
      · cases h; exact hentries entry (by simp)
      · exact hinit name value h

/-- Production/exact `lookup_code` correspondence.  Under `PanSemStateRelExec`,
    for byte-ranged argument values and a byte-ranged looked-up code entry, the
    production `panSemTotalCodeLookup` and the exact `lookupCodeHOLFinite` both
    fail or both succeed; on success the exact body is `progToHOL` of the
    production body, the return shapes correspond, the production body and
    return shape are byte-ranged, the callee locals are related on every
    `NameRanged` name, and every production callee local is byte-ranged. -/
theorem panSemTotalCodeLookup_agree {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (function : MlS) (values : List (PanValue (RiscV.Word 64)))
    (hvalues : ∀ value ∈ values, PanValueByteRanged value)
    (hcode : ∀ entry, panSemCodeLookup production.code (toStringOfBytes function) =
      some entry → PanLangEntryByteRanged entry) :
    match panSemTotalCodeLookup production (toStringOfBytes function) values,
      lookupCodeHOLFinite exact.code.lookup function (values.map panValueToHOL) with
    | none, none => True
    | some (callee, calleeLocals, returnShape), some (body, exactLocals, exactShape) =>
        body = progToHOL callee ∧ exactShape = shapeToHOL returnShape ∧
        ProgByteRanged callee ∧ ShapeByteRanged returnShape ∧
        (∀ name, NameRanged name →
          Option.map panValueToHOL (calleeLocals name) = exactLocals.lookup (ofString name)) ∧
        (∀ name value, calleeLocals name = some value → PanValueByteRanged value)
    | _, _ => False := by
  have hfn : NameRanged (toStringOfBytes function) := by
    intro character hmem
    simp only [toStringOfBytes, String.toList_ofList, List.mem_map] at hmem
    obtain ⟨byte, _hbyte, rfl⟩ := hmem
    have hb : byte.toNat < 256 := by simpa using byte.isLt
    rw [ofNat_toNat_char byte]
    exact hb
  have hcodeRel := hrel.2.2.2.1 (toStringOfBytes function) hfn
  rw [ofString_toStringOfBytes] at hcodeRel
  have hexactNone : ∀ v, lookupCodeHOLExact exact.code.lookup function v = none →
      lookupCodeHOLFinite exact.code.lookup function v = none :=
    fun v h => (lookupCodeHOLFinite_eq_none_iff _ _ _).mpr h
  cases hlk : panSemCodeLookup production.code (toStringOfBytes function) with
  | none =>
      rw [hlk] at hcodeRel
      have h := hexactNone (values.map panValueToHOL)
        (lookupCodeHOLExact_of_code_none _ _ _ hcodeRel.symm)
      have hprod : panSemTotalCodeLookup production (toStringOfBytes function) values = none := by
        simp [panSemTotalCodeLookup, lookupPanSemCodeCall, hlk]
      rw [hprod, h]
      trivial
  | some entry =>
      obtain ⟨parameters, callee, returnShape⟩ := entry
      obtain ⟨hparams, hbody, hret⟩ := hcode _ hlk
      rw [hlk] at hcodeRel
      simp only [Option.map_some, panLangEntryToHOL] at hcodeRel
      have hnames : ∀ name ∈ parameters.map Prod.fst, NameRanged name := by
        intro name hmem
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
        exact (hparams p hp).1
      have hfst : (parameters.map paramToHOL).map Prod.fst =
          (parameters.map Prod.fst).map ofString := by
        simp [paramToHOL, Function.comp_def]
      have hnodup : ((parameters.map paramToHOL).map Prod.fst).Nodup ↔
          (parameters.map Prod.fst).Nodup := by
        rw [hfst]; exact nodup_map_ofString_iff _ hnames
      have hargs := panSemCodeArgumentsMatch_iff_HOL production.structs parameters values
        (fun p hp => (hparams p hp).2) hvalues
      have hexactCode : lookupCodeHOLExact exact.code.lookup function
          (values.map panValueToHOL) =
          if ((parameters.map paramToHOL).map Prod.fst).Nodup ∧
              (parameters.map paramToHOL).length = (values.map panValueToHOL).length ∧
              ((parameters.map paramToHOL).zip (values.map panValueToHOL)).all
                (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true then
            some (progToHOL callee,
              List.foldl
                (fun (map : MlS → Option (ValueHOL 64)) (entry : MlS × ValueHOL 64) =>
                  fun current => if current = entry.1 then some entry.2 else map current)
                (fun _ => none)
                (((parameters.map paramToHOL).map Prod.fst).zip (values.map panValueToHOL)),
              shapeToHOL returnShape)
          else none := by
        unfold lookupCodeHOLExact
        rw [← hcodeRel]
      by_cases hok : (parameters.map Prod.fst).Nodup ∧
          panSemCodeArgumentsMatch production.structs parameters values = true
      · obtain ⟨hlen, hall⟩ := hargs.mp hok.2
        have hcond : ((parameters.map paramToHOL).map Prod.fst).Nodup ∧
            (parameters.map paramToHOL).length = (values.map panValueToHOL).length ∧
            ((parameters.map paramToHOL).zip (values.map panValueToHOL)).all
              (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true :=
          ⟨hnodup.mpr hok.1, hlen, hall⟩
        rw [if_pos hcond] at hexactCode
        have hlen' : parameters.length = values.length := by
          simpa using hlen
        have hprod : panSemTotalCodeLookup production (toStringOfBytes function) values =
            some (callee,
              ((parameters.map Prod.fst).zip values).foldl
                (fun locals (entry : VarName × PanValue (RiscV.Word 64)) =>
                  updatePanValueMap locals entry.1 entry.2) (fun _ => none),
              returnShape) := by
          simp [panSemTotalCodeLookup, lookupPanSemCodeCall, hlk, hok.1, hok.2,
            bindPanValueParameters, hlen']
        rw [hprod]
        cases hfin : lookupCodeHOLFinite exact.code.lookup function
            (values.map panValueToHOL) with
        | none =>
            rw [(lookupCodeHOLFinite_eq_none_iff _ _ _).mp hfin] at hexactCode
            exact absurd hexactCode (by simp)
        | some result =>
            obtain ⟨body, exactLocals, exactShape⟩ := result
            have hsome := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hfin
            rw [hexactCode] at hsome
            simp only [Option.some.injEq, Prod.mk.injEq] at hsome
            obtain ⟨hb, hl, hs⟩ := hsome
            refine ⟨hb.symm, hs.symm, hbody, hret, ?_, ?_⟩
            · intro name hname
              rw [← hl, hfst]
              have hzip : ((parameters.map Prod.fst).map ofString).zip
                  (values.map panValueToHOL) =
                  ((parameters.map Prod.fst).zip values).map
                    (fun entry => (ofString entry.1, panValueToHOL entry.2)) := by
                rw [List.zip_map]
                rfl
              rw [hzip]
              exact bindFold_agree _ (fun e he => hnames e.1 (List.of_mem_zip he).1)
                (fun _ => none) (fun _ => none) (fun _ _ => rfl) name hname
            · exact bindFold_values _ (fun _ => none) PanValueByteRanged
                (fun e he => hvalues e.2 (List.of_mem_zip he).2) (fun _ _ h => by cases h)
      · have hbad : ¬ (((parameters.map paramToHOL).map Prod.fst).Nodup ∧
            (parameters.map paramToHOL).length = (values.map panValueToHOL).length ∧
            ((parameters.map paramToHOL).zip (values.map panValueToHOL)).all
              (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true) := by
          rintro ⟨h1, h2, h3⟩
          exact hok ⟨hnodup.mp h1, hargs.mpr ⟨h2, h3⟩⟩
        rw [if_neg hbad] at hexactCode
        have hprod : panSemTotalCodeLookup production (toStringOfBytes function) values =
            none := by
          by_cases hnd : (parameters.map Prod.fst).Nodup
          · have hm : panSemCodeArgumentsMatch production.structs parameters values = false := by
              cases h : panSemCodeArgumentsMatch production.structs parameters values
              · rfl
              · exact absurd ⟨hnd, h⟩ hok
            simp [panSemTotalCodeLookup, lookupPanSemCodeCall, hlk, hnd, hm]
          · simp [panSemTotalCodeLookup, lookupPanSemCodeCall, hlk, hnd]
        rw [hprod, hexactNone _ hexactCode]
        trivial

end Flapjack
