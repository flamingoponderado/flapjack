import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

/-!
# Production/exact `lookup_code` correspondence for the total panSem bridge

The production total evaluator `panSemTotalEvaluate` looks a callee up with
`panSemTotalCodeLookup` (through `lookupPanSemCodeCall`, `PanBst.lean:106`),
while the exact evaluator `evaluateHOLFiniteState` uses `lookupCodeHOLFinite`,
the finite-support rendering of HOL `lookup_code_def`
(`cakeml/pancake/semantics/panSemScript.sml:458-467`).  This module proves the
two lookups agree under `PanSemStateRelExec`: both fail, or both succeed with
the exact body `progToHOL` of the production body, the encoded return shape, and
callee locals related on every `NameRanged` name.  On top of it,
`panSemTotalEvaluate_call_agree` proves the `Call` constructor agreement.

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

/-- `PanSemStateRelExec` carries over to the production call-entry state (clock
    decremented, fresh callee locals) and the exact `callEntryStateHOLFinite`
    whenever the callee locals are related on `NameRanged` names. -/
theorem PanSemStateRelExec.callEntry {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateFiniteExact 64 σ}
    (h : PanSemStateRelExec production exact.toExact)
    (newLocals : VarName → Option (PanValue (RiscV.Word 64)))
    (calleeLocals : HolFiniteMapExact MlS (ValueHOL 64))
    (hlocals : ∀ name, NameRanged name →
      Option.map panValueToHOL (newLocals name) = calleeLocals.lookup (ofString name)) :
    PanSemStateRelExec { production with clock := production.clock - 1, locals := newLocals }
      (callEntryStateHOLFinite exact calleeLocals).toExact := by
  obtain ⟨_, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  exact ⟨hlocals, hg, hs, hc, he, hm, hmd, hsm, by
    show exact.clock - 1 = production.clock - 1
    exact congrArg (· - 1) hck, hbe, hffi, hb, ht⟩

/-- Restoring the caller's locals on both sides preserves `PanSemStateRelExec`. -/
theorem PanSemStateRelExec.restoreLocals {σ : Type}
    {production caller : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact exactCaller : PanSemStateFiniteExact 64 σ}
    (h : PanSemStateRelExec production exact.toExact)
    (hcaller : PanSemStateRelExec caller exactCaller.toExact) :
    PanSemStateRelExec { production with locals := caller.locals }
      ({ exact with locals := exactCaller.locals } : PanSemStateFiniteExact 64 σ).toExact := by
  obtain ⟨_, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  exact ⟨hcaller.1, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩

/-- Restoring the caller's locals preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.restoreLocals {σ : Type}
    {production caller : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged production) (hcaller : PanSemStateRelExecRanged caller) :
    PanSemStateRelExecRanged { production with locals := caller.locals } :=
  ⟨hcaller.1, h.2.1, h.2.2⟩

/-- Byte-rangedness of the identifier/value payload of a production result. -/
def PanSemHOLResultRanged : Option (PanSemHOLResult (RiscV.Word 64)) → Prop
  | some (.returned value) => PanValueByteRanged value
  | some (.exception identifier value) => NameRanged identifier ∧ PanValueByteRanged value
  | _ => True


/-- A byte-ranged argument list evaluated under a ranged state yields
    byte-ranged values (via the `rStruct` expression over the same list). -/
theorem evalPanSemStateExps_byteRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hranged : PanSemStateRelExecRanged state)
    (expressions : List (Exp (RiscV.Word 64)))
    (hexpressions : ∀ e ∈ expressions, ExpByteRanged e)
    (values : List (PanValue (RiscV.Word 64)))
    (hvalues : evalPanSemStateExps state expressions = some values) :
    ∀ value ∈ values, PanValueByteRanged value := by
  rw [evalPanSemStateExps_64_eq_previous] at hvalues
  unfold evalPanValueExps at hvalues
  have hstruct : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord (.rStruct expressions)
      (memoryAccess := some (panSemBitVec64MemoryAccess state)) = some (.rStruct values) := by
    simp [evalPanValueExp, hvalues]
  have hr := evalPanValueExp_byteRanged state hranged _ (.rStruct expressions)
    (by
      simp only [ExpByteRanged]
      clear hvalues hstruct
      induction expressions with
      | nil => trivial
      | cons e es ih =>
          exact ⟨hexpressions e (by simp), ih (fun x hx => hexpressions x (by simp [hx]))⟩)
    _ hstruct
  simpa [PanValueByteRanged] using hr

/-- The production `Call` info decoded by `progOfHOL`. -/
def callInfoOfHOL :
    Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)) →
      Option (Option (VarKind × VarName) × Option (VarName × VarName × Prog (RiscV.Word 64)))
  | none => none
  | some (kind, none) => some (kind.map (fun kv => (kv.1, toStringOfBytes kv.2)), none)
  | some (kind, some (eid, var, handler)) =>
      some (kind.map (fun kv => (kv.1, toStringOfBytes kv.2)),
        some (toStringOfBytes eid, toStringOfBytes var, progOfHOL handler))

/-- `progOfHOL` on a `Call` node, with its info decoded by `callInfoOfHOL`. -/
theorem progOfHOL_call
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64)) :
    progOfHOL (.call info function arguments : ProgHOL 64) =
      .call (callInfoOfHOL info) (toStringOfBytes function) (arguments.map expOfHOL) := by
  rcases info with _ | ⟨kind, _ | ⟨eid, var, handler⟩⟩ <;> simp [progOfHOL, callInfoOfHOL]

/-- Agreement of one production/exact program pair at a related state pair. -/
abbrev PanSemTotalAgreeAt {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (program : Prog (RiscV.Word 64)) (exactProgram : ProgHOL 64)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) : Prop :=
  PanSemHOLResultOptionRel (panSemTotalEvaluate primitive program production).1
      (evaluateHOLFiniteState exact exactProgram).1 ∧
    PanSemStateRelExec (panSemTotalEvaluate primitive program production).2
      (evaluateHOLFiniteState exact exactProgram).2.toExact

/-- Production/exact agreement for the `Call` constructor.  Both evaluators
    evaluate the arguments (`evalPanValueExps_eq_evalListHOLExact_of`), look the
    callee up (`panSemTotalCodeLookup_agree`), time out at clock 0, and run the
    callee from the call-entry state; `ihCallee` is the well-founded hypothesis at
    a strictly smaller clock and `ihHandler` the structural hypothesis for the
    handler.  Production `fix_clock` on the callee state is the identity up to the
    relation (`evaluateHOLFiniteState_clock_le`).  Every result is covered:
    `None`/`Break`/`Continue` errors, `Return` with a tail call, a discarded
    value, or a local/global assignment (validity parity
    `panValueAssignmentValid_eq_isValidValueHOLFinite`), return-shape mismatch,
    exception propagation and handling (id match, missing shape, shape/validity
    failure), and pass-through results with `empty_locals`.

    The explicit premises `hcode`, `hexceptionShapes` and `hcallee` are the
    rangedness boundary of `flapjack-pxn.18.4.3.77.2.15`: code entries and
    exception shapes are not covered by `PanSemStateRelExecRanged`, and
    rangedness of the callee post-state and result payload is not preserved by
    every production step. -/
theorem panSemTotalEvaluate_call_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64))
    (hcode : ∀ entry, panSemCodeLookup production.code (toStringOfBytes function) =
      some entry → PanLangEntryByteRanged entry)
    (hexceptionShapes : ∀ identifier shape,
      production.exceptionShapes identifier = some shape → ShapeByteRanged shape)
    (hcallee : ∀ values callee newLocals returnShape,
      panSemTotalCodeLookup production (toStringOfBytes function) values =
        some (callee, newLocals, returnShape) →
      PanSemStateRelExecRanged (panSemTotalEvaluate primitive callee
          { production with clock := production.clock - 1, locals := newLocals }).2 ∧
        PanSemHOLResultRanged (panSemTotalEvaluate primitive callee
          { production with clock := production.clock - 1, locals := newLocals }).1)
    (ihCallee : ∀ (program : ProgHOL 64)
        (production' : PanSemState (RiscV.Word 64) (FfiState σ))
        (exact' : PanSemStateFiniteExact 64 σ),
        PanSemStateRelExec production' exact'.toExact →
        PanSemStateRelExecRanged production' →
        production'.clock < production.clock →
        PanSemTotalAgreeAt primitive (progOfHOL program) program production' exact')
    (ihHandler : ∀ kind eid var handler,
        info = some (kind, some (eid, var, handler)) →
        ∀ (production' : PanSemState (RiscV.Word 64) (FfiState σ))
          (exact' : PanSemStateFiniteExact 64 σ),
          PanSemStateRelExec production' exact'.toExact →
          PanSemStateRelExecRanged production' →
          PanSemTotalAgreeAt primitive (progOfHOL handler) handler production' exact') :
    PanSemTotalAgreeAt primitive (progOfHOL (.call info function arguments))
      (.call info function arguments) production exact := by
  letI : DecidablePred exact.memaddrs := fun a => Classical.propDecidable _
  have hargs : Option.map (List.map panValueToHOL)
      (evalPanSemStateExps production (arguments.map expOfHOL)) =
      exact.evalListHOLFinite arguments := by
    rw [evalPanSemStateExps_64_eq_previous]
    unfold evalPanValueExps
    have h := evalPanValueExps_eq_evalListHOLExact_of production.structs production.locals
      production.globals production.memory production.baseAddress production.topAddress
      panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess production)) exact
      (arguments.map expOfHOL) (fun e he => by
        obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
        exact evalPanValueExp_agree production exact hrel hranged _
          (expOfHOL_byteRanged_bridge e'))
    simpa [List.map_map, Function.comp_def, expToHOL_expOfHOL] using h
  have hck : exact.clock = production.clock := hrel.2.2.2.2.2.2.2.2.1
  have hfnRanged := nameRanged_toStringOfBytes_bridge function
  simp only [PanSemTotalAgreeAt]
  rw [progOfHOL_call, panSemTotalEvaluate, evaluateHOLFiniteState_call]
  cases hev : evalPanSemStateExps production (arguments.map expOfHOL) with
  | none =>
      rw [hev] at hargs
      simp only [Option.map_none] at hargs
      rw [← hargs]
      exact ⟨trivial, hrel⟩
  | some values =>
      rw [hev] at hargs
      simp only [Option.map_some] at hargs
      rw [← hargs]
      dsimp only
      have hvals := evalPanSemStateExps_byteRanged production hranged _
        (fun e he => by
          obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
          exact expOfHOL_byteRanged_bridge e') values hev
      have hlk := panSemTotalCodeLookup_agree production exact hrel function values hvals hcode
      have hcal := hcallee values
      revert hlk hcal
      cases hp : panSemTotalCodeLookup production (toStringOfBytes function) values <;>
        cases he : lookupCodeHOLFinite exact.code.lookup function (values.map panValueToHOL) <;>
        intro hlk hcal
      · exact ⟨trivial, hrel⟩
      · exact hlk.elim
      · exact hlk.elim
      · rename_i pentry eentry
        obtain ⟨callee, newLocals, returnShape⟩ := pentry
        obtain ⟨body, calleeLocals, exactShape⟩ := eentry
        obtain ⟨rfl, rfl, hbodyR, hrsR, hlocals, hlocalsR⟩ := hlk
        obtain ⟨hpostR, hresR⟩ := hcal callee newLocals returnShape rfl
        simp only [hck]
        by_cases hz : production.clock = 0
        · simp only [hz, if_true]
          exact ⟨trivial, by
            simpa only [panEmptyLocals, toExact_emptyLocalsHOLFinite] using
              PanSemStateRelExec.emptyLocals hrel⟩
        simp only [hz, if_false]
        have hentryRel := PanSemStateRelExec.callEntry hrel newLocals calleeLocals hlocals
        have hentryR : PanSemStateRelExecRanged
            { production with clock := production.clock - 1, locals := newLocals } :=
          ⟨hlocalsR, hranged.2.1, hranged.2.2⟩
        have hih := ihCallee (progToHOL callee) _ _ hentryRel hentryR (by simp; omega)
        rw [progOfHOL_progToHOL callee hbodyR] at hih
        obtain ⟨hres, hst⟩ := hih
        have hle := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite exact calleeLocals)
          (progToHOL callee)
        have hfix : PanSemStateRelExec
            (panSemFixClock (production.clock - 1) (panSemTotalEvaluate primitive callee
              { production with clock := production.clock - 1, locals := newLocals }).2)
            (evaluateHOLFiniteState (callEntryStateHOLFinite exact calleeLocals)
              (progToHOL callee)).2.toExact := by
          have h := PanSemStateRelExec.fixClock (production.clock - 1) hst
          have hc : min (production.clock - 1) (evaluateHOLFiniteState
              (callEntryStateHOLFinite exact calleeLocals) (progToHOL callee)).2.clock =
              (evaluateHOLFiniteState (callEntryStateHOLFinite exact calleeLocals)
                (progToHOL callee)).2.clock := by
            have hce : (callEntryStateHOLFinite exact calleeLocals).clock =
                production.clock - 1 := by
              simp [callEntryStateHOLFinite, hck]
            rw [hce] at hle
            omega
          simpa only [toExact, hc] using h
        have hfixR := hpostR.setClock (min (production.clock - 1) (panSemTotalEvaluate primitive
          callee { production with clock := production.clock - 1, locals := newLocals }).2.clock)
        generalize panSemTotalEvaluate primitive callee
          { production with clock := production.clock - 1, locals := newLocals } = P
          at hres hfix hfixR hresR ⊢
        generalize evaluateHOLFiniteState (callEntryStateHOLFinite exact calleeLocals)
          (progToHOL callee) = E at hres hfix ⊢
        have hempty : PanSemStateRelExec (panEmptyLocals (panSemFixClock (production.clock - 1) P.2))
            (emptyLocalsHOLFinite E.2).toExact := by
          simpa only [panEmptyLocals, toExact_emptyLocalsHOLFinite] using
            PanSemStateRelExec.emptyLocals hfix
        rcases P with ⟨_ | r, p⟩ <;> rcases E with ⟨_ | e, q⟩
        · exact ⟨trivial, hfix⟩
        · exact hres.elim
        · exact hres.elim
        · cases r <;> cases e <;> simp only [PanSemHOLResultOptionRel, PanSemHOLResultRel] at hres <;>
            dsimp only
          all_goals first
            | exact ⟨trivial, hfix⟩
            | exact ⟨trivial, hempty⟩
            | exact ⟨hres, hempty⟩
            | skip
          · -- `Return`
            rename_i v v'
            subst hres
            have hvR : PanValueByteRanged v := hresR
            have hshapeExact : shapeOfHOLExact (panValueToHOL v) =
                shapeToHOL (panSemShapeOf v) := by
              rw [shapeOfHOLExact_panValueToHOL production.structs v,
                panValueShape_eq_panSemShapeOf_tagged production.structs v]
            have hshR : ShapeByteRanged (panSemShapeOf v) := by
              have h := panValueShape_byteRanged production.structs v hvR
              rwa [panValueShape_eq_panSemShapeOf_tagged production.structs v] at h
            have hmatch : panShapeMatches (panSemShapeOf v) returnShape =
                shapeEqHOL (shapeOfHOLExact (panValueToHOL v)) (shapeToHOL returnShape) := by
              rw [hshapeExact]
              exact panShapeMatches_eq_shapeEqHOL _ _ hshR hrsR
            rw [← hmatch]
            by_cases hm : panShapeMatches (panSemShapeOf v) returnShape = true
            · simp only [hm, if_true]
              rcases info with _ | ⟨_ | ⟨k, n⟩, hopt⟩
              · exact ⟨rfl, hempty⟩
              · rcases hopt with _ | ⟨eid, var, h⟩ <;>
                  exact ⟨trivial, PanSemStateRelExec.restoreLocals hfix hrel⟩
              · have hn := nameRanged_toStringOfBytes_bridge n
                have hparity := panValueAssignmentValid_eq_isValidValueHOLFinite production exact
                  hrel hranged k (toStringOfBytes n) hn v hvR
                rw [ofString_toStringOfBytes, isValidValueHOLFinite_eq] at hparity
                have hrestore := PanSemStateRelExec.restoreLocals hfix hrel
                rcases hopt with _ | ⟨eid, var, h⟩ <;>
                · simp only [callInfoOfHOL, Option.map, ← hparity]
                  by_cases hv : panValueAssignmentValid production.structs production.locals
                      production.globals k (toStringOfBytes n) v = true
                  · simp only [hv, if_true]
                    refine ⟨trivial, ?_⟩
                    cases k with
                    | «local» =>
                        have h := PanSemStateRelExec.updateLocals hrestore (toStringOfBytes n) hn v
                        rw [ofString_toStringOfBytes] at h
                        exact h
                    | global =>
                        have h := PanSemStateRelExec.updateGlobals hrestore (toStringOfBytes n) hn v
                        rw [ofString_toStringOfBytes] at h
                        exact h
                  · simp only [hv]
                    exact ⟨trivial, hfix⟩
            · simp only [hm]
              exact ⟨trivial, hfix⟩
          · -- `Exception`
            rename_i eid0 v eid' v'
            obtain ⟨rfl, rfl⟩ := hres
            obtain ⟨hidR, hvR⟩ : NameRanged eid0 ∧ PanValueByteRanged v := hresR
            rcases info with _ | ⟨kopt, _ | ⟨hid, hvar, handler⟩⟩
            · exact ⟨⟨rfl, rfl⟩, hempty⟩
            · exact ⟨⟨rfl, rfl⟩, hempty⟩
            · simp only [callInfoOfHOL]
              by_cases heq : ofString eid0 = hid
              · have hstr : eid0 = toStringOfBytes hid :=
                  ofString_injective_of_ranged hidR (nameRanged_toStringOfBytes_bridge hid)
                    (by rw [ofString_toStringOfBytes]; exact heq)
                have hb : (eid0 == toStringOfBytes hid) = true := beq_iff_eq.mpr hstr
                simp only [hb, heq, if_true]
                subst heq
                have hes : Option.map shapeToHOL (production.exceptionShapes eid0) =
                    exact.eshapes.lookup (ofString eid0) := hrel.2.2.2.2.1 eid0 hidR
                cases hsh : production.exceptionShapes eid0 with
                | none =>
                    rw [hsh] at hes
                    rw [← hes]
                    exact ⟨trivial, hfix⟩
                | some shape =>
                    rw [hsh] at hes
                    rw [← hes]
                    dsimp only [Option.map_some]
                    have hshapeR := hexceptionShapes eid0 shape hsh
                    have hshapeExact : shapeOfHOLExact (panValueToHOL v) =
                        shapeToHOL (panSemShapeOf v) := by
                      rw [shapeOfHOLExact_panValueToHOL production.structs v,
                        panValueShape_eq_panSemShapeOf_tagged production.structs v]
                    have hshR : ShapeByteRanged (panSemShapeOf v) := by
                      have h := panValueShape_byteRanged production.structs v hvR
                      rwa [panValueShape_eq_panSemShapeOf_tagged production.structs v] at h
                    have hmatch : panShapeMatches (panSemShapeOf v) shape =
                        shapeEqHOL (shapeOfHOLExact (panValueToHOL v)) (shapeToHOL shape) := by
                      rw [hshapeExact]
                      exact panShapeMatches_eq_shapeEqHOL _ _ hshR hshapeR
                    have hvn := nameRanged_toStringOfBytes_bridge hvar
                    have hparity := panValueAssignmentValid_eq_isValidValueHOLFinite production
                      exact hrel hranged .local (toStringOfBytes hvar) hvn v hvR
                    rw [ofString_toStringOfBytes, isValidValueHOLFinite_eq] at hparity
                    rw [← hmatch, ← hparity]
                    by_cases hok : (panShapeMatches (panSemShapeOf v) shape &&
                        panValueAssignmentValid production.structs production.locals
                          production.globals .local (toStringOfBytes hvar) v) = true
                    · simp only [hok, if_true]
                      have hstate := PanSemStateRelExec.updateLocals
                        (PanSemStateRelExec.restoreLocals hfix hrel) (toStringOfBytes hvar) hvn v
                      rw [ofString_toStringOfBytes] at hstate
                      have hstateR := PanSemStateRelExecRanged.updateLocals
                        (PanSemStateRelExecRanged.restoreLocals hfixR hranged)
                        (toStringOfBytes hvar) v hvR
                      exact ihHandler kopt (ofString eid0) hvar handler rfl _ _ hstate hstateR
                    · simp only [hok]
                      exact ⟨trivial, hfix⟩
              · have hb : (eid0 == toStringOfBytes hid) = false := by
                  cases h : eid0 == toStringOfBytes hid
                  · rfl
                  · exfalso
                    apply heq
                    rw [beq_iff_eq.mp h, ofString_toStringOfBytes]
                simp only [hb, heq]
                exact ⟨⟨rfl, rfl⟩, hempty⟩

end Flapjack
