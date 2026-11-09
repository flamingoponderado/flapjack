module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxOp
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxInstall
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxForce

@[expose] public section


/-! Complete primitive-operation case of approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.OpTotal
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Complete operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOp {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace op xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace op xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace op xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace op xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace op xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  cases op with
  | label n => exact Op.knownCorrectApproxOpLabel c trace n xs aenv g0 argsIH eas g env extra s0 res s h
  | ffi n => exact Op.knownCorrectApproxOpFfi c trace n xs aenv g0 argsIH eas g env extra s0 res s h
  | intOp v => exact Op.knownCorrectApproxOpInt c trace v xs aenv g0 argsIH eas g env extra s0 res s h
  | wordOp v => exact Op.knownCorrectApproxOpWord c trace v xs aenv g0 argsIH eas g env extra s0 res s h
  | blockOp v => exact Op.knownCorrectApproxOpBlock c trace v xs aenv g0 argsIH eas g env extra s0 res s h
  | globOp v => exact Op.knownCorrectApproxOpGlobal c trace v xs aenv g0 argsIH eas g env extra s0 res s h
  | memOp v => exact Op.knownCorrectApproxOpMemory c trace v xs aenv g0 argsIH eas g env extra s0 res s h
  | install => exact Install.knownCorrectApproxOpInstall c trace xs aenv g0 argsIH eas g env extra s0 res s h
  | thunkOp v =>
    cases v with
    | allocThunk mode => exact Op.knownCorrectApproxOpAllocThunk c trace mode xs aenv g0 argsIH eas g env extra s0 res s h
    | updateThunk mode => exact Op.knownCorrectApproxOpUpdateThunk c trace mode xs aenv g0 argsIH eas g env extra s0 res s h
    | forceThunk => exact Force.knownCorrectApproxOpForce c trace xs aenv g0 argsIH eas g env extra s0 res s h

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.OpTotal
