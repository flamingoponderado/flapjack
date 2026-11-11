module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppConfigGC
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ArithmeticResults
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyArithmeticSource

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
  simp only [SemanticPrimitivesHOL.doApp] at run
  split at run
  next checked =>
    cases arithRun : doArith action typ vs with
    | none => simp [arithRun] at run
    | some result =>
      cases result with
      | inl error =>
        simp only [arithRun, Option.map_some, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨errorEq, flatChecked, flatError, flatArith⟩ :=
          doArith_inl typ vs genv flatVs action error ⟨checked, ok, values, arithRun⟩
        subst error
        refine ⟨.err (.raise FlatSem.divExnV), flat, stores, nonempty, ffi, rfl, rfl, ?_, ?_⟩
        · exact .raise (valueRel_lemmas genv ok).2.1
        · simp [astOpToFlatOp, FlatSem.doApp_arith_source, flatChecked, flatArith]
      | inr value =>
        simp only [arithRun, Option.map_some, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨flatChecked, flatValue, flatArith, related⟩ :=
          doArith_inr typ vs genv flatVs action value ⟨checked, ok, values, arithRun⟩
        refine ⟨.val (FlatSem.valueToFlat flatValue), flat, stores, nonempty, ffi, rfl, rfl, .value related, ?_⟩
        simp [astOpToFlatOp, FlatSem.doApp_arith_source, flatChecked, flatArith]
  next => simp at run

end Flapjack.Compiler.Backend.SourceToFlat
