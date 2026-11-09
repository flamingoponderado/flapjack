module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppOpassign
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppArith
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppFromTo
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppShift
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppEquality
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoAppTest

@[expose] public section

/-! The complete primitive application simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace DoAppPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppPort

/-- Primitive application simulation. The dispatcher inherits
`reals_as_rational_cuts` (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_correct {C F : Type} (genv : GlobalEnv)
    (s1 s2 : Store Value × HolFfiState F) (op : Op) (vs : List Value)
    (r : Result Value Value) (flat : FlatSem.State C F) (flatVs : List FlatSem.Value)
    (premises : doApp s1 op vs = some (s2, r) ∧
      List.Forall₂ (StoreValueRel genv) s1.1 flat.refs.tail ∧ flat.refs ≠ [] ∧
      List.Forall₂ (ValueRel genv) vs flatVs ∧ s1.2 = flat.ffi ∧ genvCOk genv.c ∧
      op ≠ .aallocEmpty ∧ op ≠ .envId) :
    ∃ flatResult flatState,
      List.Forall₂ (StoreValueRel genv) s2.1 flatState.refs.tail ∧ flatState.refs ≠ [] ∧
      s2.2 = flatState.ffi ∧ flat.globals = flatState.globals ∧
      flat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv r flatResult ∧
      FlatSem.doApp flat (astOpToFlatOp op) flatVs = some (flatState, flatResult) := by
  cases op <;> first
    | exact doApp_Equality genv s1 s2 vs r flat flatVs premises
    | exact doApp_Opapp genv s1 s2 vs r flat flatVs premises
    | exact doApp_Opassign genv s1 s2 vs r flat flatVs premises
    | exact doApp_Opref genv s1 s2 vs r flat flatVs premises
    | exact doApp_Opderef genv s1 s2 vs r flat flatVs premises
    | exact doApp_Aw8alloc genv s1 s2 vs r flat flatVs premises
    | exact doApp_Aw8sub genv s1 s2 vs r flat flatVs premises
    | exact doApp_Aw8length genv s1 s2 vs r flat flatVs premises
    | exact doApp_Aw8update genv s1 s2 vs r flat flatVs premises
    | exact doApp_CopyStrStr genv s1 s2 vs r flat flatVs premises
    | exact doApp_CopyStrAw8 genv s1 s2 vs r flat flatVs premises
    | exact doApp_CopyAw8Str genv s1 s2 vs r flat flatVs premises
    | exact doApp_CopyAw8Aw8 genv s1 s2 vs r flat flatVs premises
    | exact doApp_XorAw8StrUnsafe genv s1 s2 vs r flat flatVs premises
    | exact doApp_Implode genv s1 s2 vs r flat flatVs premises
    | exact doApp_Explode genv s1 s2 vs r flat flatVs premises
    | exact doApp_Strsub genv s1 s2 vs r flat flatVs premises
    | exact doApp_Strlen genv s1 s2 vs r flat flatVs premises
    | exact doApp_Strcat genv s1 s2 vs r flat flatVs premises
    | exact doApp_VfromList genv s1 s2 vs r flat flatVs premises
    | exact doApp_Vsub genv s1 s2 vs r flat flatVs premises
    | exact doApp_Vlength genv s1 s2 vs r flat flatVs premises
    | exact doApp_Aalloc genv s1 s2 vs r flat flatVs premises
    | exact doApp_AallocFixed genv s1 s2 vs r flat flatVs premises
    | exact doApp_Asub genv s1 s2 vs r flat flatVs premises
    | exact doApp_Alength genv s1 s2 vs r flat flatVs premises
    | exact doApp_Aupdate genv s1 s2 vs r flat flatVs premises
    | exact doApp_VsubUnsafe genv s1 s2 vs r flat flatVs premises
    | exact doApp_AsubUnsafe genv s1 s2 vs r flat flatVs premises
    | exact doApp_AupdateUnsafe genv s1 s2 vs r flat flatVs premises
    | exact doApp_Aw8subUnsafe genv s1 s2 vs r flat flatVs premises
    | exact doApp_Aw8updateUnsafe genv s1 s2 vs r flat flatVs premises
    | exact doApp_ListAppend genv s1 s2 vs r flat flatVs premises
    | exact doApp_ConfigGC genv s1 s2 vs r flat flatVs premises
    | exact doApp_Arith genv s1 s2 _ _ vs r flat flatVs premises
    | exact doApp_FromTo genv s1 s2 _ _ vs r flat flatVs premises
    | exact doApp_Shift genv s1 s2 _ _ _ vs r flat flatVs premises
    | exact doApp_Test genv s1 s2 _ _ vs r flat flatVs premises
    | exact doApp_ThunkOp genv _ s1 s2 vs r flat flatVs premises
    | exact doApp_FFI genv _ s1 s2 vs r flat flatVs premises
    | exact False.elim (premises.2.2.2.2.2.2.1 rfl)
    | exact False.elim (premises.2.2.2.2.2.2.2 rfl)
    | simp [doApp, doAppNumericCore, doAppBasic] at premises

end Flapjack.Compiler.Backend.SourceToFlat
