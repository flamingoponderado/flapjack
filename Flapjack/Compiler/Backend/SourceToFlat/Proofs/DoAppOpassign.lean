module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MemoryOps
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveData

@[expose] public section

/-! Assignment, reference, byte-array, and string-copy cases of the primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppOpassignPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppOpassignPort

/-- The Opassign case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Opassign {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .opassign vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.opassign ≠ .aallocEmpty ∧ Op.opassign ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .opassign) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons value rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases first <;> simp [doApp, doAppNumericCore, doAppBasic] at run
        case loc flag address =>
          cases assigned : storeAssign address (.refv value) s1.1 with
          | none => simp [assigned] at run
          | some sourceRefs =>
            simp [assigned] at run
            obtain ⟨rfl, rfl⟩ := run
            cases values with
            | cons locationRel tail =>
              cases tail with
              | cons valueRel tail =>
                cases tail
                cases locationRel
                rename_i flatValue
                let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
                have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
                obtain ⟨flatRefs, _, flatApply, relatedUnit, afterRel, reserved⟩ :=
                  opassign_related genv source flat states flag address value flatValue valueRel sourceRefs assigned
                obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                  (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp afterRel
                refine ⟨.val FlatSem.unitValue, { flat with refs := flatRefs }, afterStores,
                  afterNonempty, afterFfi, rfl, reserved.symm, .value relatedUnit, ?_⟩
                simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatApply]

/-- The Opref case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Opref {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .opref vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.opref ≠ .aallocEmpty ∧ Op.opref ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .opref) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons value rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases values with
      | cons valueRel tail =>
        cases tail
        rename_i flatValue
        let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
        have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
        have sim := opref_related genv source flat states value flatValue valueRel
        cases sourceAlloc : storeAlloc (.refv value) s1.1 with
        | mk sourceRefs sourceAddress =>
          simp [doApp, doAppNumericCore, doAppBasic, sourceAlloc] at run
          obtain ⟨rfl, rfl⟩ := run
          cases flatAlloc : storeAlloc (.refv flatValue) flat.refs with
          | mk flatRefs flatAddress =>
            simp only [source, sourceAlloc, flatAlloc] at sim
            obtain ⟨_, flatApply, related, afterRel, reserved⟩ := sim
            obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
              (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp afterRel
            refine ⟨.val (.loc true flatAddress), { flat with refs := flatRefs }, afterStores,
              afterNonempty, afterFfi, rfl, reserved.symm, .value related, ?_⟩
            simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatApply]

/-- The Opderef case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Opderef {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .opderef vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.opderef ≠ .aallocEmpty ∧ Op.opderef ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .opderef) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases first <;> simp [doApp, doAppNumericCore, doAppBasic] at run
      case loc flag address =>
        cases lookup : storeLookup address s1.1 with
        | none => simp [lookup] at run
        | some stored =>
          cases stored <;> simp [lookup] at run
          case refv value =>
            obtain ⟨rfl, rfl⟩ := run
            cases values with
            | cons locationRel tail =>
              cases tail
              cases locationRel
              let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
              have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
              obtain ⟨flatValue, flatLookup, related⟩ :=
                stateRel_ref_lookup genv source flat states address value lookup
              refine ⟨.val flatValue, flat, stores, nonempty, ffi, rfl, rfl, .value related, ?_⟩
              simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppFlat, flatLookup]

/-- The Aw8alloc case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Aw8alloc {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aw8alloc vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aw8alloc ≠ .aallocEmpty ∧ Op.aw8alloc ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aw8alloc) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases first <;> cases second <;> simp [doApp, doAppNumericCore, doAppBasic] at run
        case litv.litv sizeLit byteLit =>
          cases sizeLit <;> cases byteLit <;> simp at run
          case intLit.word8 size byte =>
            cases values with
            | cons sizeRel tail =>
              cases tail with
              | cons byteRel tail =>
                cases tail
                cases sizeRel
                cases byteRel
                by_cases negative : size < 0
                · simp [negative, boundsFailure] at run
                  obtain ⟨rfl, rfl⟩ := run
                  refine ⟨.err (.raise FlatSem.subscriptExnV), flat, stores, nonempty, ffi, rfl, rfl, ?_, ?_⟩
                  · exact .raise (valueRel_lemmas genv ok).2.2.2.2
                  · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                      FlatSem.boundsFailure, negative]
                · let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
                  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
                  have sim := aw8alloc_related genv source flat states size (Int.le_of_not_gt negative) byte
                  cases sourceAlloc : storeAlloc (.w8array (List.replicate size.toNat byte)) s1.1 with
                  | mk sourceRefs sourceAddress =>
                    simp [negative, sourceAlloc] at run
                    obtain ⟨rfl, rfl⟩ := run
                    cases flatAlloc : storeAlloc (.w8array (List.replicate size.toNat byte)) flat.refs with
                    | mk flatRefs flatAddress =>
                      simp only [source, sourceAlloc, flatAlloc] at sim
                      obtain ⟨_, flatApply, related, afterRel, reserved⟩ := sim
                      obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                        (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp afterRel
                      refine ⟨.val (.loc true flatAddress), { flat with refs := flatRefs }, afterStores,
                        afterNonempty, afterFfi, rfl, reserved.symm, .value related, ?_⟩
                      simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatApply]

/-- The Aw8sub case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Aw8sub {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aw8sub vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aw8sub ≠ .aallocEmpty ∧ Op.aw8sub ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aw8sub) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        have successful : doApp (source.refs, source.ffi) .aw8sub [first, second] ≠ none := by
          simp [source, run]
        obtain ⟨flag, address, index, sourceValues, rfl, rfl, lookup⟩ :=
          aw8sub_operands source first second false successful
        cases values with
        | cons locationRel tail =>
          cases tail with
          | cons indexRel tail =>
            cases tail
            cases locationRel
            cases indexRel
            have sim := aw8sub_complete_related genv source flat states ok flag address sourceValues lookup index false
            simp only [Bool.false_eq_true, if_false, source, run] at sim
            cases flatRun : FlatSem.doAppMemory flat .aw8sub [.loc flag (address + 1), .litv (.intLit index)] with
            | none => simp [flatRun] at sim
            | some result =>
              cases result with
              | none => simp [flatRun] at sim
              | some pair =>
                cases pair with
                | mk next result =>
                  simp only [flatRun] at sim
                  obtain ⟨refsEq, ffiEq, nextEq, resultRel⟩ := sim
                  subst next
                  refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, resultRel, ?_⟩
                  · simpa [source, refsEq] using stores
                  · simpa [source, ffiEq] using ffi
                  · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatRun]

/-- The Aw8length case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Aw8length {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aw8length vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aw8length ≠ .aallocEmpty ∧ Op.aw8length ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aw8length) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases first <;> simp [doApp, doAppNumericCore, doAppBasic] at run
      case loc flag address =>
        cases lookup : storeLookup address s1.1 with
        | none => simp [lookup] at run
        | some stored =>
          cases stored <;> simp [lookup] at run
          case w8array bytes =>
            obtain ⟨rfl, rfl⟩ := run
            cases values with
            | cons locationRel tail =>
              cases tail
              cases locationRel
              let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
              have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
              have flatLookup := stateRel_byteArray_lookup genv source flat states address bytes lookup
              refine ⟨.val (.litv (.intLit bytes.length)), flat, stores, nonempty, ffi, rfl, rfl,
                .value (.literal genv _), ?_⟩
              simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatLookup]

/-- The Aw8update case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Aw8update {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aw8update vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aw8update ≠ .aallocEmpty ∧ Op.aw8update ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aw8update) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | cons value rest =>
        cases rest with
        | cons fourth rest => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          have successful : doApp (source.refs, source.ffi) .aw8update [first, second, value] ≠ none := by
            simp [source, run]
          obtain ⟨flag, address, index, byte, sourceValues, rfl, rfl, rfl, lookup⟩ :=
            aw8update_operands source first second value false successful
          cases values with
          | cons locationRel tail =>
            cases tail with
            | cons indexRel tail =>
              cases tail with
              | cons valueRel tail =>
                cases tail
                cases locationRel
                cases indexRel
                cases valueRel
                have sim := aw8update_complete_related genv source flat states ok flag address sourceValues lookup
                  index byte false
                simp only [Bool.false_eq_true, if_false, source, run] at sim
                cases flatRun : FlatSem.doAppMemory flat .aw8update
                    [.loc flag (address + 1), .litv (.intLit index), .litv (.word8 byte)] with
                | none => simp [flatRun] at sim
                | some result =>
                  cases result with
                  | none => simp [flatRun] at sim
                  | some pair =>
                    cases pair with
                    | mk next result =>
                      simp only [flatRun] at sim
                      obtain ⟨ffiEq, nextEq, nextRel, reserved, resultRel⟩ := sim
                      obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                        (stateRel_iff genv { source with refs := s2.1 } next).mp nextRel
                      refine ⟨result, next, afterStores, afterNonempty, ?_, ?_, reserved.symm, resultRel, ?_⟩
                      · simpa [source, ffiEq] using afterFfi
                      · rw [nextEq]
                      · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatRun]

/-- The CopyStrStr case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_CopyStrStr {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .copyStrStr vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.copyStrStr ≠ .aallocEmpty ∧ Op.copyStrStr ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .copyStrStr) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | cons third rest =>
        cases rest with
        | cons fourth rest => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases first <;> cases second <;> cases third <;>
            simp [doApp, doAppNumericCore, doAppBasic] at run
          case litv.litv.litv textLit offsetLit lengthLit =>
            cases textLit <;> cases offsetLit <;> cases lengthLit <;> simp at run
            case strLit.intLit.intLit text offset length =>
              cases values with
              | cons textRel tail =>
                cases tail with
                | cons offsetRel tail =>
                  cases tail with
                  | cons lengthRel tail =>
                    cases tail
                    cases textRel
                    cases offsetRel
                    cases lengthRel
                    cases copied : copyArray (text.explode, offset) length none with
                    | none =>
                      simp [copied, boundsFailure] at run
                      obtain ⟨rfl, rfl⟩ := run
                      refine ⟨.err (.raise FlatSem.subscriptExnV), flat, stores, nonempty, ffi, rfl, rfl,
                        .raise (valueRel_lemmas genv ok).2.2.2.2, ?_⟩
                      simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                        FlatSem.doAppData, FlatSem.doAppCopy,
                        FlatSem.boundsFailure, copied]
                    | some chars =>
                      simp [copied] at run
                      obtain ⟨rfl, rfl⟩ := run
                      refine ⟨.val (.litv (.strLit (.implode chars))), flat, stores, nonempty, ffi, rfl, rfl,
                        .value (.literal genv _), ?_⟩
                      simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                        FlatSem.doAppData, FlatSem.doAppCopy, copied]

/-- The CopyStrAw8 case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_CopyStrAw8 {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .copyStrAw8 vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.copyStrAw8 ≠ .aallocEmpty ∧ Op.copyStrAw8 ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .copyStrAw8) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | cons third rest =>
        cases rest with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | cons fourth rest =>
          cases rest with
          | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
          | cons fifth rest =>
            cases rest with
            | cons sixth rest => simp [doApp, doAppNumericCore, doAppBasic] at run
            | nil =>
              have successful : doApp (source.refs, source.ffi) .copyStrAw8 [first, second, third, fourth, fifth] ≠ none := by
                simp [source, run]
              obtain ⟨text, offset, length, flag, address, dstOffset, bytes, rfl, rfl, rfl, rfl, rfl, lookup⟩ :=
                copyStrAw8_operands source first second third fourth fifth successful
              cases values with
              | cons textRel tail =>
                cases tail with
                | cons offsetRel tail =>
                  cases tail with
                  | cons lengthRel tail =>
                    cases tail with
                    | cons locationRel tail =>
                      cases tail with
                      | cons dstRel tail =>
                        cases tail
                        cases textRel
                        cases offsetRel
                        cases lengthRel
                        cases locationRel
                        cases dstRel
                        have sim := copyStrAw8_related genv source flat states ok text offset length flag address bytes dstOffset lookup
                        simp only [source, run] at sim
                        cases flatRun : FlatSem.doAppCopy flat .copyStrAw8
                            [.litv (.strLit text), .litv (.intLit offset), .litv (.intLit length),
                             .loc flag (address + 1), .litv (.intLit dstOffset)] with
                        | none => simp [flatRun] at sim
                        | some result =>
                          cases result with
                          | none => simp [flatRun] at sim
                          | some pair =>
                            cases pair with
                            | mk next result =>
                              simp only [flatRun] at sim
                              obtain ⟨ffiEq, nextEq, nextRel, reserved, resultRel⟩ := sim
                              obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                                (stateRel_iff genv { source with refs := s2.1 } next).mp nextRel
                              refine ⟨result, next, afterStores, afterNonempty, ?_, ?_,
                                reserved.symm, resultRel, ?_⟩
                              · simpa [source, ffiEq] using afterFfi
                              · rw [nextEq]
                              · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                                  FlatSem.doAppData, flatRun]

/-- The CopyAw8Str case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_CopyAw8Str {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .copyAw8Str vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.copyAw8Str ≠ .aallocEmpty ∧ Op.copyAw8Str ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .copyAw8Str) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | cons third rest =>
        cases rest with
        | cons fourth rest => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          have successful : doApp (source.refs, source.ffi) .copyAw8Str [first, second, third] ≠ none := by
            simp [source, run]
          obtain ⟨flag, address, offset, length, bytes, rfl, rfl, rfl, lookup⟩ :=
            copyAw8Str_operands source first second third successful
          cases values with
          | cons locationRel tail =>
            cases tail with
            | cons offsetRel tail =>
              cases tail with
              | cons lengthRel tail =>
                cases tail
                cases locationRel
                cases offsetRel
                cases lengthRel
                have sim := copyAw8Str_complete_related genv source flat states ok flag address bytes lookup offset length
                simp only [source, run] at sim
                cases flatRun : FlatSem.doAppCopy flat .copyAw8Str
                    [.loc flag (address + 1), .litv (.intLit offset), .litv (.intLit length)] with
                | none => simp [flatRun] at sim
                | some result =>
                  cases result with
                  | none => simp [flatRun] at sim
                  | some pair =>
                    cases pair with
                    | mk next result =>
                      simp only [flatRun] at sim
                      obtain ⟨refsEq, ffiEq, nextEq, resultRel⟩ := sim
                      subst next
                      refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, resultRel, ?_⟩
                      · simpa [source, refsEq] using stores
                      · simpa [source, ffiEq] using ffi
                      · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          FlatSem.doAppData, flatRun]

/-- The CopyAw8Aw8 case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_CopyAw8Aw8 {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .copyAw8Aw8 vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.copyAw8Aw8 ≠ .aallocEmpty ∧ Op.copyAw8Aw8 ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .copyAw8Aw8) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | cons third rest =>
        cases rest with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | cons fourth rest =>
          cases rest with
          | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
          | cons fifth rest =>
            cases rest with
            | cons sixth rest => simp [doApp, doAppNumericCore, doAppBasic] at run
            | nil =>
              have successful : doApp (source.refs, source.ffi) .copyAw8Aw8 [first, second, third, fourth, fifth] ≠ none := by
                simp [source, run]
              obtain ⟨srcFlag, srcAddress, offset, length, dstFlag, dstAddress, dstOffset, srcBytes, dstBytes,
                rfl, rfl, rfl, rfl, rfl, srcLookup, dstLookup⟩ :=
                copyAw8Aw8_operands source first second third fourth fifth successful
              cases values with
              | cons srcRel tail =>
                cases tail with
                | cons offsetRel tail =>
                  cases tail with
                  | cons lengthRel tail =>
                    cases tail with
                    | cons dstRel tail =>
                      cases tail with
                      | cons dstOffsetRel tail =>
                        cases tail
                        cases srcRel
                        cases offsetRel
                        cases lengthRel
                        cases dstRel
                        cases dstOffsetRel
                        have sim := copyAw8Aw8_related genv source flat states ok srcFlag srcAddress srcBytes offset length
                          dstFlag dstAddress dstBytes dstOffset srcLookup dstLookup
                        simp only [source, run] at sim
                        cases flatRun : FlatSem.doAppCopy flat .copyAw8Aw8
                            [.loc srcFlag (srcAddress + 1), .litv (.intLit offset), .litv (.intLit length),
                             .loc dstFlag (dstAddress + 1), .litv (.intLit dstOffset)] with
                        | none => simp [flatRun] at sim
                        | some result =>
                          cases result with
                          | none => simp [flatRun] at sim
                          | some pair =>
                            cases pair with
                            | mk next result =>
                              simp only [flatRun] at sim
                              obtain ⟨ffiEq, nextEq, nextRel, reserved, resultRel⟩ := sim
                              obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                                (stateRel_iff genv { source with refs := s2.1 } next).mp nextRel
                              refine ⟨result, next, afterStores, afterNonempty, ?_, ?_,
                                reserved.symm, resultRel, ?_⟩
                              · simpa [source, ffiEq] using afterFfi
                              · rw [nextEq]
                              · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                                  FlatSem.doAppData, flatRun]

/-- The XorAw8Str_unsafe case of `do_app`. The dispatcher inherits
`reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_XorAw8StrUnsafe {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .xorAw8StrUnsafe vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.xorAw8StrUnsafe ≠ .aallocEmpty ∧ Op.xorAw8StrUnsafe ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .xorAw8StrUnsafe) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        have successful : doApp (source.refs, source.ffi) .xorAw8StrUnsafe [first, second] ≠ none := by
          simp [source, run]
        obtain ⟨flag, address, text, bytes, result, rfl, rfl, lookup, xor⟩ :=
          xorAw8Str_operands source first second successful
        cases values with
        | cons locationRel tail =>
          cases tail with
          | cons textRel tail =>
            cases tail
            cases locationRel
            cases textRel
            obtain ⟨sourceRefs, flatRefs, src, dst, nextRel, reserved⟩ :=
              xorAw8Str_related genv source flat states flag address text bytes result lookup xor
            simp only [source, run, Option.some.injEq, Prod.mk.injEq] at src
            obtain ⟨rfl, rfl, rfl⟩ := src.symm
            obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
              (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp nextRel
            refine ⟨.val FlatSem.unitValue, { flat with refs := flatRefs }, afterStores, afterNonempty,
              afterFfi, rfl, reserved.symm, .value (.tuple genv [] [] (.nil genv)), ?_⟩
            simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
              FlatSem.doAppData, dst]

/-- The Implode case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Implode {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .implode vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.implode ≠ .aallocEmpty ∧ Op.implode ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .implode) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons value rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases decoded : valueToCharList value with
      | none => simp [doApp, doAppNumericCore, doAppBasic, decoded] at run
      | some chars =>
        simp [doApp, doAppNumericCore, doAppBasic, decoded] at run
        obtain ⟨rfl, rfl⟩ := run
        cases values with
        | cons valueRel tail =>
          cases tail
          rename_i flatValue
          have flatDecoded := valueToCharList_related genv ok value flatValue chars ⟨valueRel, decoded⟩
          refine ⟨.val (.litv (.strLit (.implode chars))), flat, stores, nonempty, ffi, rfl, rfl,
            .value (.literal genv _), ?_⟩
          simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
            FlatSem.doAppData, flatDecoded]

/-- The Explode case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Explode {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .explode vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.explode ≠ .aallocEmpty ∧ Op.explode ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .explode) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons value rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases value <;> simp [doApp, doAppNumericCore, doAppBasic] at run
      case litv lit =>
        cases lit <;> simp at run
        case strLit text =>
          obtain ⟨rfl, rfl⟩ := run
          cases values with
          | cons valueRel tail =>
            cases tail
            cases valueRel
            have itemsRel : List.Forall₂ (ValueRel genv)
                (text.explode.map (SemanticPrimitivesHOL.Value.litv ∘ Lit.char))
                (text.explode.map (FlatSem.Value.litv ∘ Lit.char)) := by
              induction text.explode with
              | nil => exact .nil
              | cons char rest ih => exact .cons (.literal genv (.char char)) ih
            have resultRel := listToValue_related genv _ _ ⟨ok.2.2.1, itemsRel⟩
            refine ⟨.val (FlatSem.listToValue (text.explode.map (FlatSem.Value.litv ∘ Lit.char))),
              flat, stores, nonempty, ffi, rfl, rfl, .value resultRel, ?_⟩
            simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- The Strsub case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Strsub {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .strsub vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.strsub ≠ .aallocEmpty ∧ Op.strsub ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .strsub) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        have successful : doApp (source.refs, source.ffi) .strsub [first, second] ≠ none := by
          simp [source, run]
        obtain ⟨str, index, rfl, rfl⟩ := strsub_operands source first second successful
        cases values with
        | cons stringRel tail =>
          cases tail with
          | cons indexRel tail =>
            cases tail
            cases stringRel
            cases indexRel
            have sim := strsub_complete_related genv source flat ok str index
            simp only [source, run] at sim
            cases flatRun : FlatSem.doAppData flat .strsub [.litv (.strLit str), .litv (.intLit index)] with
            | none => simp [flatRun] at sim
            | some result =>
              cases result with
              | none => simp [flatRun] at sim
              | some pair =>
                cases pair with
                | mk next result =>
                  simp only [flatRun] at sim
                  obtain ⟨refsEq, ffiEq, nextEq, resultRel⟩ := sim
                  subst next
                  refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, resultRel, ?_⟩
                  · simpa [source, refsEq] using stores
                  · simpa [source, ffiEq] using ffi
                  · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatRun]

/-- The Strlen case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Strlen {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .strlen vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.strlen ≠ .aallocEmpty ∧ Op.strlen ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .strlen) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons value rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases value <;> simp [doApp, doAppNumericCore, doAppBasic] at run
      case litv lit =>
        cases lit <;> simp at run
        case strLit text =>
          obtain ⟨rfl, rfl⟩ := run
          cases values with
          | cons valueRel tail =>
            cases tail
            cases valueRel
            refine ⟨.val (.litv (.intLit text.explode.length)), flat, stores, nonempty, ffi, rfl, rfl,
              .value (.literal genv _), ?_⟩
            simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- The Strcat case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Strcat {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .strcat vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.strcat ≠ .aallocEmpty ∧ Op.strcat ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .strcat) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons value rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases decoded : valueToList value with
      | none => simp [doApp, doAppNumericCore, doAppBasic, decoded] at run
      | some sourceValues =>
        cases stringDecoded : valuesToString sourceValues with
        | none => simp [doApp, doAppNumericCore, doAppBasic, decoded, stringDecoded] at run
        | some str =>
          simp [doApp, doAppNumericCore, doAppBasic, decoded, stringDecoded] at run
          obtain ⟨rfl, rfl⟩ := run
          cases values with
          | cons valueRel tail =>
            cases tail
            rename_i flatValue
            obtain ⟨flatValues, flatDecoded, relatedValues⟩ :=
              valueToList_related genv ok value flatValue sourceValues ⟨valueRel, decoded⟩
            have flatString := valuesToString_related genv sourceValues flatValues str relatedValues stringDecoded
            refine ⟨.val (.litv (.strLit str)), flat, stores, nonempty, ffi, rfl, rfl,
              .value (.literal genv _), ?_⟩
            simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
              FlatSem.doAppData, flatDecoded, flatString]

/-- The VfromList case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_VfromList {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .vfromList vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.vfromList ≠ .aallocEmpty ∧ Op.vfromList ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .vfromList) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons value rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases decoded : valueToList value with
      | none => simp [doApp, doAppNumericCore, doAppBasic, decoded] at run
      | some sourceValues =>
        simp [doApp, doAppNumericCore, doAppBasic, decoded] at run
        obtain ⟨rfl, rfl⟩ := run
        cases values with
        | cons valueRel tail =>
          cases tail
          rename_i flatValue
          obtain ⟨flatValues, flatDecoded, relatedValues⟩ :=
            valueToList_related genv ok value flatValue sourceValues ⟨valueRel, decoded⟩
          refine ⟨.val (.vectorv flatValues), flat, stores, nonempty, ffi, rfl, rfl,
            .value (valueRel_vector genv sourceValues flatValues relatedValues), ?_⟩
          simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
            FlatSem.doAppData, flatDecoded]

/-- The Vsub case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Vsub {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .vsub vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.vsub ≠ .aallocEmpty ∧ Op.vsub ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .vsub) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        have successful : doApp (source.refs, source.ffi) .vsub [first, second] ≠ none := by
          simp [source, run]
        obtain ⟨sourceValues, index, rfl, rfl⟩ := vsub_operands source first second false successful
        cases values with
        | cons vectorRel tail =>
          cases tail with
          | cons indexRel tail =>
            cases tail
            obtain ⟨flatValues, rfl, related⟩ := ((valueRel_eqns_nonGlobal).2.2.2.1 sourceValues _ genv).mp vectorRel
            cases indexRel
            have sim := vsub_complete_related genv source flat ok sourceValues flatValues related index false
            simp only [Bool.false_eq_true, if_false, source, run] at sim
            cases flatRun : FlatSem.doAppData flat .vsub [.vectorv flatValues, .litv (.intLit index)] with
            | none => simp [flatRun] at sim
            | some result =>
              cases result with
              | none => simp [flatRun] at sim
              | some pair =>
                cases pair with
                | mk next result =>
                  simp only [flatRun] at sim
                  obtain ⟨refsEq, ffiEq, nextEq, resultRel⟩ := sim
                  subst next
                  refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, resultRel, ?_⟩
                  · simpa [source, refsEq] using stores
                  · simpa [source, ffiEq] using ffi
                  · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatRun]

/-- The Vsub_unsafe case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_VsubUnsafe {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .vsubUnsafe vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.vsubUnsafe ≠ .aallocEmpty ∧ Op.vsubUnsafe ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .vsubUnsafe) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        have successful : doApp (source.refs, source.ffi) .vsubUnsafe [first, second] ≠ none := by
          simp [source, run]
        obtain ⟨sourceValues, index, rfl, rfl⟩ := vsub_operands source first second true successful
        cases values with
        | cons vectorRel tail =>
          cases tail with
          | cons indexRel tail =>
            cases tail
            obtain ⟨flatValues, rfl, related⟩ := ((valueRel_eqns_nonGlobal).2.2.2.1 sourceValues _ genv).mp vectorRel
            cases indexRel
            have sim := vsub_complete_related genv source flat ok sourceValues flatValues related index true
            simp only [if_true, source, run] at sim
            cases flatRun : FlatSem.doAppData flat .vsubUnsafe [.vectorv flatValues, .litv (.intLit index)] with
            | none => simp [flatRun] at sim
            | some result =>
              cases result with
              | none => simp [flatRun] at sim
              | some pair =>
                cases pair with
                | mk next result =>
                  simp only [flatRun] at sim
                  obtain ⟨refsEq, ffiEq, nextEq, resultRel⟩ := sim
                  subst next
                  refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, resultRel, ?_⟩
                  · simpa [source, refsEq] using stores
                  · simpa [source, ffiEq] using ffi
                  · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatRun]

/-- The Vlength case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Vlength {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .vlength vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.vlength ≠ .aallocEmpty ∧ Op.vlength ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .vlength) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons value rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases value <;> simp [doApp, doAppNumericCore, doAppBasic] at run
      case vectorv sourceValues =>
        obtain ⟨rfl, rfl⟩ := run
        cases values with
        | cons valueRel tail =>
          cases tail
          obtain ⟨flatValues, rfl, related⟩ := ((valueRel_eqns_nonGlobal).2.2.2.1 sourceValues _ genv).mp valueRel
          have lengths := List.Forall₂.length_eq related
          refine ⟨.val (.litv (.intLit sourceValues.length)), flat, stores, nonempty, ffi, rfl, rfl,
            .value (.literal genv _), ?_⟩
          simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
            FlatSem.doAppData, ← lengths]

/-- The Aalloc case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Aalloc {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aalloc vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aalloc ≠ .aallocEmpty ∧ Op.aalloc ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aalloc) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons value rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases first <;> simp [doApp, doAppNumericCore, doAppBasic] at run
        case litv sizeLit =>
          cases sizeLit <;> simp at run
          case intLit size =>
            cases values with
            | cons sizeRel tail =>
              cases tail with
              | cons valueRel tail =>
                cases tail
                cases sizeRel
                rename_i flatValue
                by_cases negative : size < 0
                · simp [negative, boundsFailure] at run
                  obtain ⟨rfl, rfl⟩ := run
                  refine ⟨.err (.raise FlatSem.subscriptExnV), flat, stores, nonempty, ffi, rfl, rfl, ?_, ?_⟩
                  · exact .raise (valueRel_lemmas genv ok).2.2.2.2
                  · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                      FlatSem.boundsFailure, negative]
                · let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
                  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
                  have sim := aalloc_related genv source flat states size (Int.le_of_not_gt negative) value flatValue valueRel
                  cases sourceAlloc : storeAlloc (.varray (List.replicate size.toNat value)) s1.1 with
                  | mk sourceRefs sourceAddress =>
                    simp [negative, sourceAlloc] at run
                    obtain ⟨rfl, rfl⟩ := run
                    cases flatAlloc : storeAlloc (.varray (List.replicate size.toNat flatValue)) flat.refs with
                    | mk flatRefs flatAddress =>
                      simp only [source, sourceAlloc, flatAlloc] at sim
                      obtain ⟨_, flatApply, related, afterRel, reserved⟩ := sim
                      obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                        (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp afterRel
                      refine ⟨.val (.loc true flatAddress), { flat with refs := flatRefs }, afterStores,
                        afterNonempty, afterFfi, rfl, reserved.symm, .value related, ?_⟩
                      simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatApply]

/-- The AallocFixed case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_AallocFixed {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aallocFixed vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aallocFixed ≠ .aallocEmpty ∧ Op.aallocFixed ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aallocFixed) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  have sim := aallocFixed_related genv source flat states vs flatVs values
  cases sourceAlloc : storeAlloc (.varray vs) s1.1 with
  | mk sourceRefs sourceAddress =>
    simp [doApp, doAppNumericCore, doAppBasic, sourceAlloc] at run
    obtain ⟨rfl, rfl⟩ := run
    cases flatAlloc : storeAlloc (.varray flatVs) flat.refs with
    | mk flatRefs flatAddress =>
      simp only [source, sourceAlloc, flatAlloc] at sim
      obtain ⟨_, flatApply, related, afterRel, reserved⟩ := sim
      obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
        (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp afterRel
      refine ⟨.val (.loc true flatAddress), { flat with refs := flatRefs }, afterStores,
        afterNonempty, afterFfi, rfl, reserved.symm, .value related, ?_⟩
      simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatApply]

/-- The Asub case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Asub {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .asub vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.asub ≠ .aallocEmpty ∧ Op.asub ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .asub) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        have successful : doApp (source.refs, source.ffi) .asub [first, second] ≠ none := by
          simp [source, run]
        obtain ⟨flag, address, index, sourceValues, rfl, rfl, lookup⟩ :=
          asub_operands source first second false successful
        cases values with
        | cons locationRel tail =>
          cases tail with
          | cons indexRel tail =>
            cases tail
            cases locationRel
            cases indexRel
            have sim := asub_complete_related genv source flat states ok flag address sourceValues lookup index false
            simp only [Bool.false_eq_true, if_false, source, run] at sim
            cases flatRun : FlatSem.doAppMemory flat .asub [.loc flag (address + 1), .litv (.intLit index)] with
            | none => simp [flatRun] at sim
            | some result =>
              cases result with
              | none => simp [flatRun] at sim
              | some pair =>
                cases pair with
                | mk next result =>
                  simp only [flatRun] at sim
                  obtain ⟨refsEq, ffiEq, nextEq, resultRel⟩ := sim
                  subst next
                  refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, resultRel, ?_⟩
                  · simpa [source, refsEq] using stores
                  · simpa [source, ffiEq] using ffi
                  · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatRun]

/-- The Alength case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Alength {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .alength vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.alength ≠ .aallocEmpty ∧ Op.alength ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .alength) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic] at run
    | nil =>
      cases first <;> simp [doApp, doAppNumericCore, doAppBasic] at run
      case loc flag address =>
        cases lookup : storeLookup address s1.1 with
        | none => simp [lookup] at run
        | some stored =>
          cases stored <;> simp [lookup] at run
          case varray items =>
            obtain ⟨rfl, rfl⟩ := run
            cases values with
            | cons locationRel tail =>
              cases tail
              cases locationRel
              let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
              have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
              obtain ⟨flatItems, flatLookup, itemsRel⟩ := stateRel_array_lookup genv source flat states address items lookup
              have length := List.Forall₂.length_eq itemsRel
              refine ⟨.val (.litv (.intLit items.length)), flat, stores, nonempty, ffi, rfl, rfl,
                .value (.literal genv _), ?_⟩
              simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatLookup, ← length]

/-- The Aupdate case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Aupdate {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aupdate vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aupdate ≠ .aallocEmpty ∧ Op.aupdate ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aupdate) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | cons value rest =>
        cases rest with
        | cons fourth rest => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          have successful : doApp (source.refs, source.ffi) .aupdate [first, second, value] ≠ none := by
            simp [source, run]
          obtain ⟨flag, address, index, sourceValues, rfl, rfl, lookup⟩ :=
            aupdate_operands source first second value false successful
          cases values with
          | cons locationRel tail =>
            cases tail with
            | cons indexRel tail =>
              cases tail with
              | cons valueRel tail =>
                cases tail
                cases locationRel
                cases indexRel
                rename_i flatValue
                have sim := aupdate_complete_related genv source flat states ok flag address sourceValues lookup
                  index value flatValue valueRel false
                simp only [Bool.false_eq_true, if_false, source, run] at sim
                cases flatRun : FlatSem.doAppMemory flat .aupdate
                    [.loc flag (address + 1), .litv (.intLit index), flatValue] with
                | none => simp [flatRun] at sim
                | some result =>
                  cases result with
                  | none => simp [flatRun] at sim
                  | some pair =>
                    cases pair with
                    | mk next result =>
                      simp only [flatRun] at sim
                      obtain ⟨ffiEq, nextEq, nextRel, reserved, resultRel⟩ := sim
                      obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                        (stateRel_iff genv { source with refs := s2.1 } next).mp nextRel
                      refine ⟨result, next, afterStores, afterNonempty, ?_, ?_, reserved.symm, resultRel, ?_⟩
                      · simpa [source, ffiEq] using afterFfi
                      · rw [nextEq]
                      · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatRun]

/-- The Asub_unsafe case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_AsubUnsafe {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .asubUnsafe vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.asubUnsafe ≠ .aallocEmpty ∧ Op.asubUnsafe ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .asubUnsafe) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        have successful : doApp (source.refs, source.ffi) .asubUnsafe [first, second] ≠ none := by
          simp [source, run]
        obtain ⟨flag, address, index, sourceValues, rfl, rfl, lookup⟩ :=
          asub_operands source first second true successful
        cases values with
        | cons locationRel tail =>
          cases tail with
          | cons indexRel tail =>
            cases tail
            cases locationRel
            cases indexRel
            have sim := asub_complete_related genv source flat states ok flag address sourceValues lookup index true
            simp only [if_true, source, run] at sim
            cases flatRun : FlatSem.doAppMemory flat .asubUnsafe [.loc flag (address + 1), .litv (.intLit index)] with
            | none => simp [flatRun] at sim
            | some result =>
              cases result with
              | none => simp [flatRun] at sim
              | some pair =>
                cases pair with
                | mk next result =>
                  simp only [flatRun] at sim
                  obtain ⟨refsEq, ffiEq, nextEq, resultRel⟩ := sim
                  subst next
                  refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, resultRel, ?_⟩
                  · simpa [source, refsEq] using stores
                  · simpa [source, ffiEq] using ffi
                  · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatRun]

/-- The Aupdate_unsafe case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_AupdateUnsafe {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aupdateUnsafe vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aupdateUnsafe ≠ .aallocEmpty ∧ Op.aupdateUnsafe ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aupdateUnsafe) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | cons value rest =>
        cases rest with
        | cons fourth rest => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          have successful : doApp (source.refs, source.ffi) .aupdateUnsafe [first, second, value] ≠ none := by
            simp [source, run]
          obtain ⟨flag, address, index, sourceValues, rfl, rfl, lookup⟩ :=
            aupdate_operands source first second value true successful
          cases values with
          | cons locationRel tail =>
            cases tail with
            | cons indexRel tail =>
              cases tail with
              | cons valueRel tail =>
                cases tail
                cases locationRel
                cases indexRel
                rename_i flatValue
                have sim := aupdate_complete_related genv source flat states ok flag address sourceValues lookup
                  index value flatValue valueRel true
                simp only [if_true, source, run] at sim
                cases flatRun : FlatSem.doAppMemory flat .aupdateUnsafe
                    [.loc flag (address + 1), .litv (.intLit index), flatValue] with
                | none => simp [flatRun] at sim
                | some result =>
                  cases result with
                  | none => simp [flatRun] at sim
                  | some pair =>
                    cases pair with
                    | mk next result =>
                      simp only [flatRun] at sim
                      obtain ⟨ffiEq, nextEq, nextRel, reserved, resultRel⟩ := sim
                      obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                        (stateRel_iff genv { source with refs := s2.1 } next).mp nextRel
                      refine ⟨result, next, afterStores, afterNonempty, ?_, ?_, reserved.symm, resultRel, ?_⟩
                      · simpa [source, ffiEq] using afterFfi
                      · rw [nextEq]
                      · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatRun]

/-- The Aw8sub_unsafe case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Aw8subUnsafe {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aw8subUnsafe vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aw8subUnsafe ≠ .aallocEmpty ∧ Op.aw8subUnsafe ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aw8subUnsafe) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        have successful : doApp (source.refs, source.ffi) .aw8subUnsafe [first, second] ≠ none := by
          simp [source, run]
        obtain ⟨flag, address, index, sourceValues, rfl, rfl, lookup⟩ :=
          aw8sub_operands source first second true successful
        cases values with
        | cons locationRel tail =>
          cases tail with
          | cons indexRel tail =>
            cases tail
            cases locationRel
            cases indexRel
            have sim := aw8sub_complete_related genv source flat states ok flag address sourceValues lookup index true
            simp only [if_true, source, run] at sim
            cases flatRun : FlatSem.doAppMemory flat .aw8subUnsafe [.loc flag (address + 1), .litv (.intLit index)] with
            | none => simp [flatRun] at sim
            | some result =>
              cases result with
              | none => simp [flatRun] at sim
              | some pair =>
                cases pair with
                | mk next result =>
                  simp only [flatRun] at sim
                  obtain ⟨refsEq, ffiEq, nextEq, resultRel⟩ := sim
                  subst next
                  refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, resultRel, ?_⟩
                  · simpa [source, refsEq] using stores
                  · simpa [source, ffiEq] using ffi
                  · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatRun]

/-- The Aw8update_unsafe case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Aw8updateUnsafe {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .aw8updateUnsafe vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.aw8updateUnsafe ≠ .aallocEmpty ∧ Op.aw8updateUnsafe ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .aw8updateUnsafe) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | cons value rest =>
        cases rest with
        | cons fourth rest => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          have successful : doApp (source.refs, source.ffi) .aw8updateUnsafe [first, second, value] ≠ none := by
            simp [source, run]
          obtain ⟨flag, address, index, byte, sourceValues, rfl, rfl, rfl, lookup⟩ :=
            aw8update_operands source first second value true successful
          cases values with
          | cons locationRel tail =>
            cases tail with
            | cons indexRel tail =>
              cases tail with
              | cons valueRel tail =>
                cases tail
                cases locationRel
                cases indexRel
                cases valueRel
                have sim := aw8update_complete_related genv source flat states ok flag address sourceValues lookup
                  index byte true
                simp only [if_true, source, run] at sim
                cases flatRun : FlatSem.doAppMemory flat .aw8updateUnsafe
                    [.loc flag (address + 1), .litv (.intLit index), .litv (.word8 byte)] with
                | none => simp [flatRun] at sim
                | some result =>
                  cases result with
                  | none => simp [flatRun] at sim
                  | some pair =>
                    cases pair with
                    | mk next result =>
                      simp only [flatRun] at sim
                      obtain ⟨ffiEq, nextEq, nextRel, reserved, resultRel⟩ := sim
                      obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                        (stateRel_iff genv { source with refs := s2.1 } next).mp nextRel
                      refine ⟨result, next, afterStores, afterNonempty, ?_, ?_, reserved.symm, resultRel, ?_⟩
                      · simpa [source, ffiEq] using afterFfi
                      · rw [nextEq]
                      · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatRun]

/-- The ThunkOp case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_ThunkOp {C F : Type} (genv : GlobalEnv) (op : ThunkOp)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 (.thunkOp op) vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.thunkOp op ≠ .aallocEmpty ∧ Op.thunkOp op ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp (.thunkOp op)) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases op with
  | forceThunk => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
  | allocThunk mode =>
    cases vs with
    | nil => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
    | cons value rest =>
      cases rest with
      | cons second rest => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
      | nil =>
        cases values with
        | cons valueRel tail =>
          cases tail
          rename_i flatValue
          have successful : doApp (source.refs, source.ffi) (.thunkOp (.allocThunk mode)) [value] ≠ none := by
            simp [source, run]
          have sim := allocThunk_related genv source flat states mode value flatValue valueRel successful
          cases sourceAlloc : storeAlloc (.thunk mode value) s1.1 with
          | mk sourceRefs sourceAddress =>
            cases flatAlloc : storeAlloc (.thunk mode flatValue) flat.refs with
            | mk flatRefs flatAddress =>
              simp only [source, sourceAlloc, flatAlloc, run, Option.some.injEq, Prod.mk.injEq] at sim
              obtain ⟨⟨rfl, rfl⟩, flatApply, related, afterRel, reserved⟩ := sim
              obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp afterRel
              refine ⟨.val (.loc false flatAddress), { flat with refs := flatRefs }, afterStores,
                afterNonempty, afterFfi, rfl, reserved.symm, .value related, ?_⟩
              simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApply]
  | updateThunk mode =>
    cases vs with
    | nil => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
    | cons pointer rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
      | cons value rest =>
        cases rest with
        | cons third rest => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
        | nil =>
          have successful : doApp (source.refs, source.ffi) (.thunkOp (.updateThunk mode)) [pointer, value] ≠ none := by
            simp [source, run]
          obtain ⟨address, sourceRefs, rfl, guard, assigned⟩ := updateThunkOp_operands source mode pointer value successful
          cases values with
          | cons pointerRel tail =>
            cases tail with
            | cons valueRel tail =>
              cases tail
              cases pointerRel
              rename_i flatValue
              obtain ⟨flatRefs, src, dst, afterRel, reserved⟩ :=
                updateThunkOp_related genv source flat states mode address value flatValue valueRel sourceRefs guard assigned
              simp only [source, run, Option.some.injEq, Prod.mk.injEq] at src
              obtain ⟨rfl, rfl, rfl⟩ := src.symm
              obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                (stateRel_iff genv { source with refs := sourceRefs } { flat with refs := flatRefs }).mp afterRel
              refine ⟨.val FlatSem.unitValue, { flat with refs := flatRefs }, afterStores, afterNonempty,
                afterFfi, rfl, reserved.symm, .value (.tuple genv [] [] (.nil genv)), ?_⟩
              simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, dst]

/-- The ListAppend case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_ListAppend {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 .listAppend vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.listAppend ≠ .aallocEmpty ∧ Op.listAppend ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp .listAppend) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases leftDecoded : valueToList first with
        | none => simp [doApp, doAppNumericCore, doAppBasic, leftDecoded] at run
        | some left =>
          cases rightDecoded : valueToList second with
          | none => simp [doApp, doAppNumericCore, doAppBasic, leftDecoded, rightDecoded] at run
          | some right =>
            simp [doApp, doAppNumericCore, doAppBasic, leftDecoded, rightDecoded] at run
            obtain ⟨rfl, rfl⟩ := run
            cases values with
            | cons firstRel tail =>
              cases tail with
              | cons secondRel tail =>
                cases tail
                rename_i flatFirst flatSecond
                obtain ⟨flatLeft, flatLeftDecoded, leftRel⟩ :=
                  valueToList_related genv ok first flatFirst left ⟨firstRel, leftDecoded⟩
                obtain ⟨flatRight, flatRightDecoded, rightRel⟩ :=
                  valueToList_related genv ok second flatSecond right ⟨secondRel, rightDecoded⟩
                have appended : List.Forall₂ (ValueRel genv) (left ++ right) (flatLeft ++ flatRight) := by
                  clear leftDecoded flatLeftDecoded
                  induction leftRel with
                  | nil => exact rightRel
                  | cons head _ ih => exact .cons head ih
                have related := listToValue_related genv _ _ ⟨ok.2.2.1, appended⟩
                refine ⟨.val (FlatSem.listToValue (flatLeft ++ flatRight)), flat, stores, nonempty, ffi,
                  rfl, rfl, .value related, ?_⟩
                simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                  FlatSem.doAppData, flatLeftDecoded, flatRightDecoded]

/-- The FFI case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_FFI {C F : Type} (genv : GlobalEnv) (name : Basis.Pure.MlString.MlString)
    (s1 s2 : Store Value × HolFfiState F) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 (.ffi name) vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.ffi name ≠ .aallocEmpty ∧ Op.ffi name ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp (.ffi name)) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, _, _, _⟩ := premises
  let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
  have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
  cases vs with
  | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        have successful : doApp (source.refs, source.ffi) (.ffi name) [first, second] ≠ none := by
          simp [source, run]
        obtain ⟨text, flag, address, bytes, rfl, rfl, lookup⟩ :=
          ffi_operands source name first second successful
        cases values with
        | cons textRel tail =>
          cases tail with
          | cons locationRel tail =>
            cases tail
            cases textRel
            cases locationRel
            cases call : callFFIHOL source.ffi (.extCall name) text.explode bytes with
            | ret nextFfi output =>
              obtain ⟨sourceRefs, flatRefs, sourceRun, flatRun, nextRel, reserved⟩ :=
                ffi_return_related genv source flat states name text flag address bytes output nextFfi lookup call
              simp only [source, doApp, doAppNumericCore, sourceRun] at run
              obtain ⟨rfl, rfl, rfl⟩ := run
              obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                (stateRel_iff genv { source with refs := sourceRefs, ffi := nextFfi }
                  { flat with refs := flatRefs, ffi := nextFfi }).mp nextRel
              refine ⟨.val FlatSem.unitValue, { flat with refs := flatRefs, ffi := nextFfi },
                afterStores, afterNonempty, afterFfi, rfl, reserved.symm,
                .value (.tuple genv [] [] (.nil genv)), ?_⟩
              simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatRun]
            | final event =>
              have flatLookup := stateRel_byteArray_lookup genv source flat states address bytes lookup
              have sourceRun : doAppBasic (source.refs, source.ffi) (.ffi name)
                  [.litv (.strLit text), .loc flag address] =
                  some (some ((source.refs, source.ffi), .err (.abort (.ffiError event)))) := by
                simp [doAppBasic, lookup, call]
              simp only [source, doApp, doAppNumericCore, sourceRun] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨.err (.abort (.ffiError event)), flat, stores, nonempty, ffi,
                rfl, rfl, ?_, ?_⟩
              · exact .abort (.ffiError event)
              · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                  FlatSem.doAppData, flatLookup, ← ffi, call, source]

end Flapjack.Compiler.Backend.SourceToFlat
