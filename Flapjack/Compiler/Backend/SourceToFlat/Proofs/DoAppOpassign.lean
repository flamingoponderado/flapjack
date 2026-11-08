import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MemoryOps
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedData

/-! Assignment, reference, byte-array, and string-copy cases of the primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppOpassignPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppOpassignPort

/-- The Opassign case of `do_app`; the full theorem is not yet assembled. The
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

/-- The Opref case of `do_app`; the full theorem is not yet assembled. The
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

/-- The Opderef case of `do_app`; the full theorem is not yet assembled. The
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

/-- The Aw8alloc case of `do_app`; the full theorem is not yet assembled. The
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
                  · exact .raise (exceptionValues_related genv ok).2.2.2
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

/-- The Aw8sub case of `do_app`; the full theorem is not yet assembled. The
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
        case loc.litv flag address lit =>
          cases lit <;> simp at run
          case intLit index =>
            cases lookup : storeLookup address s1.1 with
            | none => simp [lookup] at run
            | some stored =>
              cases stored <;> simp [lookup] at run
              case w8array bytes =>
                cases values with
                | cons locationRel tail =>
                  cases tail with
                  | cons indexRel tail =>
                    cases tail
                    cases locationRel
                    cases indexRel
                    let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
                    have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
                    have flatLookup := stateRel_byteArray_lookup genv source flat states address bytes lookup
                    by_cases negative : index < 0
                    · simp [readIndexed, boundsFailure, negative] at run
                      obtain ⟨rfl, rfl⟩ := run
                      refine ⟨.err (.raise FlatSem.subscriptExnV), flat, stores, nonempty, ffi, rfl, rfl, ?_, ?_⟩
                      · exact .raise (exceptionValues_related genv ok).2.2.2
                      · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          FlatSem.readIndexed, FlatSem.boundsFailure, flatLookup, negative]
                    · cases element : bytes[index.toNat]? with
                      | none =>
                        simp [readIndexed, boundsFailure, negative, element] at run
                        obtain ⟨rfl, rfl⟩ := run
                        refine ⟨.err (.raise FlatSem.subscriptExnV), flat, stores, nonempty, ffi, rfl, rfl, ?_, ?_⟩
                        · exact .raise (exceptionValues_related genv ok).2.2.2
                        · simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                            FlatSem.readIndexed, FlatSem.boundsFailure, flatLookup, negative, element]
                      | some byte =>
                        simp [readIndexed, negative, element] at run
                        obtain ⟨rfl, rfl⟩ := run
                        refine ⟨.val (.litv (.word8 byte)), flat, stores, nonempty, ffi, rfl, rfl,
                          .value (.literal genv _), ?_⟩
                        simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          FlatSem.readIndexed, flatLookup, negative, element]

/-- The Aw8length case of `do_app`; the full theorem is not yet assembled. The
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
              have ⟨_, flatApply, related⟩ := aw8length_related genv source flat states flag address bytes lookup
              refine ⟨.val (.litv (.intLit bytes.length)), flat, stores, nonempty, ffi, rfl, rfl,
                .value related, ?_⟩
              simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, flatApply]

/-- The Aw8update case of `do_app`; the full theorem is not yet assembled. The
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
  have original := run
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
          case loc.litv.litv flag address indexLit byteLit =>
            cases indexLit <;> cases byteLit <;> simp at run
            case intLit.word8 index byte =>
              cases lookup : storeLookup address s1.1 with
              | none => simp [lookup] at run
              | some stored =>
                cases stored <;> simp [lookup] at run
                case w8array bytes =>
                  cases values with
                  | cons locationRel tail =>
                    cases tail with
                    | cons indexRel tail =>
                      cases tail with
                      | cons byteRel tail =>
                        cases tail
                        cases locationRel
                        cases indexRel
                        cases byteRel
                        let source : SemanticPrimitivesHOL.State F := ⟨flat.clock, s1.1, s1.2, 0, 0, none⟩
                        have states : StateRel genv source flat := .intro source flat nonempty stores rfl ffi
                        by_cases bad : index < 0 ∨ bytes.length ≤ index.toNat
                        · have ⟨src, dst, exceptionRel⟩ :=
                            aw8update_outOfBounds genv source flat states ok flag address bytes lookup index bad byte false
                          simp only [Bool.false_eq_true, if_false] at src dst
                          simp [doApp, doAppNumericCore, src, source] at original
                          obtain ⟨rfl, rfl⟩ := original
                          refine ⟨.err (.raise FlatSem.subscriptExnV), flat, stores, nonempty, ffi, rfl, rfl,
                            .raise exceptionRel, ?_⟩
                          simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, dst]
                        · have nonnegative : 0 ≤ index := Int.le_of_not_gt (fun h => bad (.inl h))
                          have inBounds : index.toNat < bytes.length := Nat.lt_of_not_ge (fun h => bad (.inr h))
                          obtain ⟨flatRefs, src, dst, unitRel, nextRel, reserved⟩ :=
                            aw8update_related genv source flat states flag address bytes lookup index nonnegative inBounds byte false
                          simp only [Bool.false_eq_true, if_false] at src dst
                          simp [doApp, doAppNumericCore, src, source] at original
                          obtain ⟨rfl, rfl⟩ := original
                          obtain ⟨afterNonempty, afterStores, _, afterFfi⟩ :=
                            (stateRel_iff genv { source with refs := s1.1.set address (.w8array (bytes.set index.toNat byte)) }
                              { flat with refs := flatRefs }).mp nextRel
                          refine ⟨.val FlatSem.unitValue, { flat with refs := flatRefs }, afterStores,
                            afterNonempty, afterFfi, rfl, reserved.symm, .value unitRel, ?_⟩
                          simp [astOpToFlatOp, FlatSem.doApp, FlatSem.doAppNumeric, dst]

/-- The CopyStrStr case of `do_app`; the full theorem is not yet assembled. The
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
                        .raise (exceptionValues_related genv ok).2.2.2, ?_⟩
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

/-- The CopyStrAw8 case of `do_app`; the full theorem is not yet assembled. The
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

end Flapjack.Compiler.Backend.SourceToFlat
