module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveArith

@[expose] public section

/-! Arithmetic case of the source-to-flat primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppArithPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppArithPort

/-- The Arith case of `do_app`; the full theorem is `doApp_correct`. The
dispatcher inherits `reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_Arith {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (action : Arith) (typ : PrimType)
    (vs : List Value) (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 (.arith action typ) vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      Op.arith action typ ≠ .aallocEmpty ∧ Op.arith action typ ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp (.arith action typ)) flatVs = some (flatState, flatResult) := by
  obtain ⟨run, stores, nonempty, values, ffi, ok, _, _⟩ := premises
  cases typ with
  | charT => simp [doApp_arith_core, doAppNumericCore] at run
  | strT => simp [doApp_arith_core, doAppNumericCore] at run
  | intT =>
    let source : SemanticPrimitivesHOL.State F := ⟨0, s1.1, s1.2, 0, 0, none⟩
    have successful : doApp (source.refs, source.ffi) (.arith action .intT) vs ≠ none := by
      simp [source, run]
    obtain ⟨left, right, rfl⟩ := integerArith_operands source action vs successful
    cases values with
    | cons leftRel tail =>
      cases tail with
      | cons rightRel tail =>
        cases tail
        cases leftRel
        cases rightRel
        have sim := integerArith_related genv ok source flat action left right
        simp only [source, run] at sim
        cases targetEq : FlatSem.doAppNumeric flat (.arith action .intT)
          [.litv (.intLit left), .litv (.intLit right)] with
        | none => simp [targetEq] at sim
        | some out =>
          cases out with
          | none => simp [targetEq] at sim
          | some pair =>
            obtain ⟨next, result⟩ := pair
            simp only [targetEq] at sim
            obtain ⟨refs, nextFfi, nextState, rel⟩ := sim
            subst next
            refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, rel, ?_⟩
            · simpa [refs] using stores
            · exact nextFfi.trans ffi
            · simp [astOpToFlatOp, FlatSem.doApp, targetEq]
  | wordT width =>
    let source : SemanticPrimitivesHOL.State F := ⟨0, s1.1, s1.2, 0, 0, none⟩
    have successful : doApp (source.refs, source.ffi) (.arith action (.wordT width)) vs ≠ none := by
      simp [source, run]
    cases width with
    | w8 =>
      obtain ⟨left, right, rfl⟩ := word8Arith_operands source action vs successful
      cases values with
      | cons leftRel tail =>
        cases tail with
        | cons rightRel tail =>
          cases tail
          cases leftRel
          cases rightRel
          have sim := word8Arith_related genv source flat action left right
          simp only [source, run] at sim
          cases targetEq : FlatSem.doAppNumeric flat (.arith action (.wordT .w8))
            [.litv (.word8 left), .litv (.word8 right)] with
          | none => simp [targetEq] at sim
          | some out =>
            cases out with
            | none => simp [targetEq] at sim
            | some pair =>
              obtain ⟨next, result⟩ := pair
              simp only [targetEq] at sim
              obtain ⟨refs, nextFfi, nextState, rel⟩ := sim
              subst next
              refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, rel, ?_⟩
              · simpa [refs] using stores
              · exact nextFfi.trans ffi
              · simp [astOpToFlatOp, FlatSem.doApp, targetEq]
    | w64 =>
      obtain ⟨left, right, rfl⟩ := word64Arith_operands source action vs successful
      cases values with
      | cons leftRel tail =>
        cases tail with
        | cons rightRel tail =>
          cases tail
          cases leftRel
          cases rightRel
          have sim := word64Arith_related genv source flat action left right
          simp only [source, run] at sim
          cases targetEq : FlatSem.doAppNumeric flat (.arith action (.wordT .w64))
            [.litv (.word64 left), .litv (.word64 right)] with
          | none => simp [targetEq] at sim
          | some out =>
            cases out with
            | none => simp [targetEq] at sim
            | some pair =>
              obtain ⟨next, result⟩ := pair
              simp only [targetEq] at sim
              obtain ⟨refs, nextFfi, nextState, rel⟩ := sim
              subst next
              refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, rel, ?_⟩
              · simpa [refs] using stores
              · exact nextFfi.trans ffi
              · simp [astOpToFlatOp, FlatSem.doApp, targetEq]
  | boolT =>
    cases action with
    | not =>
      cases vs with
      | nil => simp [doApp_arith_core, doAppNumericCore] at run
      | cons operand rest =>
        cases rest with
        | cons second rest => simp [doApp_arith_core, doAppNumericCore] at run
        | nil =>
          let source : SemanticPrimitivesHOL.State F := ⟨0, s1.1, s1.2, 0, 0, none⟩
          have successful : doApp (source.refs, source.ffi) (.arith .not .boolT) [operand] ≠ none := by
            simp [source, run]
          obtain ⟨b, rfl⟩ := booleanNot_operand source operand successful
          cases values with
          | cons operandRel tail =>
            cases tail
            rename_i flatOperand
            have eqFlat := (boolValueRel_iff genv b flatOperand ok).mp operandRel
            subst flatOperand
            obtain ⟨sourceRun, flatRun, related⟩ := booleanNot_related genv ok source flat b
            simp only [source, run, Option.some.injEq, Prod.mk.injEq] at sourceRun
            obtain ⟨refs, nextFfi, rfl⟩ := sourceRun
            refine ⟨.val (FlatSem.boolValue (!b)), flat, ?_, nonempty, ?_, rfl, rfl, .value related, ?_⟩
            · simpa [refs] using stores
            · simpa [refs] using ffi
            · simp [astOpToFlatOp, FlatSem.doApp, flatRun]
    | _ => simp [doApp_arith_core, doAppNumericCore] at run
  | float64T =>
    let source : SemanticPrimitivesHOL.State F := ⟨0, s1.1, s1.2, 0, 0, none⟩
    have successful : doApp (source.refs, source.ffi) (.arith action .float64T) vs ≠ none := by
      simp [source, run]
    cases vs with
    | nil => cases action <;> simp [doApp_arith_core, doArith] at run
    | cons first rest =>
      cases rest with
      | nil =>
        obtain ⟨bits, rfl⟩ := floatUnary_operand source action first successful
        cases values with
        | cons related tail =>
          cases tail
          cases related
          have sim := floatUnary_related genv source flat action bits
          simp only [source, run] at sim
          cases targetEq : FlatSem.doAppNumeric flat (.arith action .float64T) [.litv (.float64 bits)] with
          | none => simp [targetEq] at sim
          | some out =>
            cases out with
            | none => simp [targetEq] at sim
            | some pair =>
              obtain ⟨next, result⟩ := pair
              simp only [targetEq] at sim
              obtain ⟨refs, nextFfi, nextState, rel⟩ := sim
              subst next
              refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, rel, ?_⟩
              · simpa [refs] using stores
              · exact nextFfi.trans ffi
              · simp [astOpToFlatOp, FlatSem.doApp, targetEq]
      | cons second rest =>
        cases rest with
        | nil =>
          obtain ⟨left, right, eq⟩ := floatBinary_operands source action first second successful
          simp only [List.cons.injEq] at eq
          obtain ⟨rfl, rfl, _⟩ := eq
          cases values with
          | cons leftRel tail =>
            cases tail with
            | cons rightRel tail =>
              cases tail
              cases leftRel
              cases rightRel
              have sim := floatBinary_related genv source flat action left right
              simp only [source, run] at sim
              cases targetEq : FlatSem.doAppNumeric flat (.arith action .float64T)
                [.litv (.float64 left), .litv (.float64 right)] with
              | none => simp [targetEq] at sim
              | some out =>
                cases out with
                | none => simp [targetEq] at sim
                | some pair =>
                  obtain ⟨next, result⟩ := pair
                  simp only [targetEq] at sim
                  obtain ⟨refs, nextFfi, nextState, rel⟩ := sim
                  subst next
                  refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, rel, ?_⟩
                  · simpa [refs] using stores
                  · exact nextFfi.trans ffi
                  · simp [astOpToFlatOp, FlatSem.doApp, targetEq]
        | cons third rest =>
          cases rest with
          | nil =>
            cases action with
            | fma =>
              obtain ⟨a, b, c, rfl, rfl, rfl⟩ := floatFma_operands source first second third successful
              cases values with
              | cons firstRel tail =>
                cases tail with
                | cons secondRel tail =>
                  cases tail with
                  | cons thirdRel tail =>
                    cases tail
                    cases firstRel
                    cases secondRel
                    cases thirdRel
                    have sim := floatFma_related genv source flat a b c
                    simp only [source, run] at sim
                    cases targetEq : FlatSem.doAppNumeric flat (.arith .fma .float64T)
                      [.litv (.float64 a), .litv (.float64 b), .litv (.float64 c)] with
                    | none => simp [targetEq] at sim
                    | some out =>
                      cases out with
                      | none => simp [targetEq] at sim
                      | some pair =>
                        obtain ⟨next, result⟩ := pair
                        simp only [targetEq] at sim
                        obtain ⟨refs, nextFfi, nextState, rel⟩ := sim
                        subst next
                        refine ⟨result, flat, ?_, nonempty, ?_, rfl, rfl, rel, ?_⟩
                        · simpa [refs] using stores
                        · exact nextFfi.trans ffi
                        · simp [astOpToFlatOp, FlatSem.doApp, targetEq]
            | _ => simp [doApp_arith_core, doArith, theLitvFloat64, checkType] at run
          | cons fourth rest => cases action <;> simp [doApp_arith_core, doArith, theLitvFloat64, checkType] at run

end Flapjack.Compiler.Backend.SourceToFlat
