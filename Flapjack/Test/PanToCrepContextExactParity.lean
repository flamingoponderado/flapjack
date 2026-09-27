import Flapjack.Pancake.PanToCrep.ContextBridge
import Flapjack.Pancake.PanToCrep.ContextProductionEvidence
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Proofs.PanToCrep

/-!
Kernel checks for the exact Pan-to-Crep context's finite-map fields and the
canonical finite-support roundtrip. Field payloads match the direct HOL
`mk_ctxt_fields` record row in `scripts/hol-probes/compile_to_crep_probe.out`.
-/

namespace Flapjack.Test.PanToCrepContextExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL NameRanged ShapeByteRanged shapeOfHOL
  withShapeHOL sizeOfShapeHOL)
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang (DeclByteRanged FunDeclByteRanged ParamByteRanged
  ListParamByteRanged ProgByteRanged ExpByteRanged)

private def p : MlS := Flapjack.Basis.Pure.MlString.ofString "p"
private def f : MlS := Flapjack.Basis.Pure.MlString.ofString "f"
private def e : MlS := Flapjack.Basis.Pure.MlString.ofString "E"

private def sample : PanToCrepContextExact 8 where
  vars := (HolFiniteMapExact.empty).update (p, (.one, [0]))
  funcs := (HolFiniteMapExact.empty).update (f, ([(p, .one)], .one))
  eids := (HolFiniteMapExact.empty).update (e, (2 : BitVec 8))
  vmax := 3

private def productionVars : FiniteMap String (Shape × List Nat) :=
  FUPDATE FEMPTY ("p", (.one, [0]))

private def productionFuncs : FiniteMap String (List (String × Shape) × Shape) :=
  FUPDATE FEMPTY ("f", ([("p", .one)], .one))

private def productionEids : FiniteMap String (BitVec 8) :=
  FUPDATE FEMPTY ("E", (2 : BitVec 8))

private def productionSample : PanToCrepHOLContext (BitVec 8) where
  vars := productionVars
  funcs := productionFuncs
  eids := productionEids
  vmax := 3

private theorem productionEvidence : PanToCrepContextProductionEvidence productionSample := {
  varsSupport := by
    refine ⟨["p"], ?_⟩
    intro key h
    by_cases hk : "p" == key
    · have heq : "p" = key := beq_iff_eq.mp hk
      simp [heq]
    · simp [productionSample, productionVars, FUPDATE, FEMPTY, hk] at h
  funcsSupport := by
    refine ⟨["f"], ?_⟩
    intro key h
    by_cases hk : "f" == key
    · have heq : "f" = key := beq_iff_eq.mp hk
      simp [heq]
    · simp [productionSample, productionFuncs, FUPDATE, FEMPTY, hk] at h
  eidsSupport := by
    refine ⟨["E"], ?_⟩
    intro key h
    by_cases hk : "E" == key
    · have heq : "E" = key := beq_iff_eq.mp hk
      simp [heq]
    · simp [productionSample, productionEids, FUPDATE, FEMPTY, hk] at h
  varsRanged := by
    intro key value h
    by_cases hk : "p" == key
    · have heq : "p" = key := beq_iff_eq.mp hk
      subst key
      simp [productionSample, productionVars, FUPDATE] at h
      subst value
      simp [NameRanged, ShapeByteRanged]
    · simp [productionSample, productionVars, FUPDATE, FEMPTY, hk] at h
  funcsRanged := by
    intro key value h
    by_cases hk : "f" == key
    · have heq : "f" = key := beq_iff_eq.mp hk
      subst key
      simp [productionSample, productionFuncs, FUPDATE] at h
      subst value
      simp [NameRanged, ShapeByteRanged]
    · simp [productionSample, productionFuncs, FUPDATE, FEMPTY, hk] at h
  eidsRanged := by
    intro key value h
    by_cases hk : "E" == key
    · have heq : "E" = key := beq_iff_eq.mp hk
      subst key
      simp [productionSample, productionEids, FUPDATE] at h
      simp [NameRanged]
    · simp [productionSample, productionEids, FUPDATE, FEMPTY, hk] at h
}

example : sample.vars.lookup p = some (.one, [0]) := by
  simp [sample, p, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : sample.funcs.lookup f = some ([(p, .one)], .one) := by
  simp [sample, f, p, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : sample.eids.lookup e = some (2 : BitVec 8) := by
  simp [sample, e, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : sample.vmax = 3 := rfl

/-! Exact HOL `mk_ctxt_def` construction: the reviewed `mkCtxtExactHOL` packs
its four arguments into the exact record with HOL's argument order and field
assignment, so it returns the same record as the direct field fixture above. -/
example :
    (mkCtxtExactHOL sample.vars sample.funcs sample.vmax sample.eids) = sample := rfl

example : (mkCtxtExactHOL sample.vars sample.funcs sample.vmax sample.eids).vmax = 3 := rfl

example :
    (mkCtxtExactHOL sample.vars sample.funcs sample.vmax sample.eids).eids.lookup e =
      some (2 : BitVec 8) := by
  change sample.eids.lookup e = some (2 : BitVec 8)
  simp [sample, e, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]


/-! The production bridge exposes exact context lookups to the String/Shape
compiler boundary using decoded byte names and shapes. -/
example : sample.toProduction.vars (toStringOfBytes p) = some (.one, [0]) := by
  rw [PanToCrepContextExact.toProduction_vars_lookup]
  simp [sample, p, Flapjack.Pancake.PanLang.shapeOfHOL,
    HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : sample.toProduction.funcs (toStringOfBytes f) =
    some ([(toStringOfBytes p, .one)], .one) := by
  rw [PanToCrepContextExact.toProduction_funcs_lookup]
  simp [sample, f, p, Flapjack.Pancake.PanLang.shapeOfHOL,
    HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : sample.toProduction.eids (toStringOfBytes e) = some (2 : BitVec 8) := by
  rw [PanToCrepContextExact.toProduction_eids_lookup]
  simp [sample, e, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : Flapjack.Pancake.PanLang.NameRanged (toStringOfBytes p) :=
  PanToCrepContextExact.toProduction_key_nameRanged p

example : sample.toProduction.vmax = sample.vmax := rfl

example : PanToCrepContextExact.ofBroad
    (PanToCrepContextExact.toBroad sample) = sample :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness sample

private def bridgedProductionSample :=
  panToCrepContextExactOfProduction productionSample productionEvidence

example : bridgedProductionSample.vars.lookup p = some (.one, [0]) := by
  simp [bridgedProductionSample, productionSample, productionVars, FUPDATE, p,
    panToCrepContextExactOfProduction_vars_lookup,
    Flapjack.Basis.Pure.MlString.toStringOfBytes, Flapjack.Basis.Pure.MlString.ofString,
    Flapjack.Pancake.PanLang.shapeToHOL]

example : bridgedProductionSample.vars.lookup (Flapjack.Basis.Pure.MlString.ofString "missing") = none := by
  simp [bridgedProductionSample, productionSample, productionVars, FUPDATE,
    panToCrepContextExactOfProduction_vars_lookup,
    Flapjack.Basis.Pure.MlString.toStringOfBytes, Flapjack.Basis.Pure.MlString.ofString,
    FEMPTY]

example : ((panToCrepContextExactOfProduction productionSample productionEvidence).vars.lookup
    (Flapjack.Basis.Pure.MlString.ofString "p")).map
      (fun value => (shapeOfHOL value.1, value.2)) = productionSample.vars "p" :=
  panToCrepContextExactOfProduction_vars_lookup_roundtrip productionSample productionEvidence
    "p" (by simp [NameRanged])

example : ((panToCrepContextExactOfProduction productionSample productionEvidence).funcs.lookup
    (Flapjack.Basis.Pure.MlString.ofString "f")).map
      (fun value => (value.1.map (fun parameter =>
        (Flapjack.Basis.Pure.MlString.toStringOfBytes parameter.1, shapeOfHOL parameter.2)),
        shapeOfHOL value.2)) = productionSample.funcs "f" :=
  panToCrepContextExactOfProduction_funcs_lookup_roundtrip productionSample productionEvidence
    "f" (by simp [NameRanged])

example : (panToCrepContextExactOfProduction productionSample productionEvidence).eids.lookup
    (Flapjack.Basis.Pure.MlString.ofString "E") = productionSample.eids "E" :=
  panToCrepContextExactOfProduction_eids_lookup_roundtrip productionSample productionEvidence
    "E" (by simp [NameRanged])

/-! Production-constructor path: the same `FUPDATE_LIST` maps created by
`make_vmap`, `make_funcs`, and `get_eids_from_decls` admit the restricted
bridge when the source declaration byte-range invariant holds. -/

private def compilerParams : List (VarName × Shape) := [("p", .one)]

private def compilerFunction : Flapjack.FunDecl (BitVec 8) :=
  ⟨"f", false, false, compilerParams, .skip, .one⟩

private def compilerDeclarations : List (Decl (BitVec 8)) :=
  [Decl.function compilerFunction, Decl.exnDecl "E" .one]

private theorem compilerDeclarationsByteRanged :
    ∀ d ∈ compilerDeclarations, DeclByteRanged d := by
  intro d hd
  have hmem : d = Decl.function compilerFunction ∨
      d = Decl.exnDecl "E" Shape.one := by
    simpa [compilerDeclarations] using hd
  rcases hmem with hfun | hexn
  · rw [hfun]
    simp [DeclByteRanged, FunDeclByteRanged, ListParamByteRanged,
      ParamByteRanged, ProgByteRanged, NameRanged,
      ShapeByteRanged, compilerFunction, compilerParams]
  · rw [hexn]
    simp [DeclByteRanged, NameRanged, ShapeByteRanged]

private def compilerEntry :
    FunName × List (VarName × Shape) × Prog (BitVec 8) × Shape :=
  ("f", compilerParams, (Prog.skip : Prog (BitVec 8)), .one)

private theorem compilerEntryMem : compilerEntry ∈ functionEntries compilerDeclarations := by
  simp [compilerEntry, compilerDeclarations, compilerFunction, compilerParams,
    functionEntries]

private def compilerContext : PanToCrepHOLContext (BitVec 8) :=
  panToCrepMkCtxtHOL (panToCrepMakeVmapHOL compilerParams)
    (functionInfosHOL compilerDeclarations) 0
    (panToCrepGetEidsFromDeclsHOL compilerDeclarations)

private theorem compilerContextEvidence :
    PanToCrepContextProductionEvidence compilerContext := by
  simpa [compilerContext, compilerEntry, compilerParams, Shape.shapeSize,
    compilerDeclarations, compilerFunction, functionEntries] using
      panToCrepFunctionContextProductionEvidence compilerDeclarations compilerEntry
        compilerDeclarationsByteRanged compilerEntryMem

private def compilerContextExact : PanToCrepContextExact 8 :=
  panToCrepContextExactOfProduction compilerContext compilerContextEvidence

example : compilerContextExact.vmax = 0 := rfl

/-! Exact HOL `ctxt_fc_def` rows: replay the direct HOL-EVAL probe
`scripts/hol-probes/ctxt_fc_probe.out`. The rows `shaped_slots`,
`zip_truncates_and_empty_slots`, `empty_maximum`, `functions_projection`,
`vmax_nonempty_list`, and `vmax_empty_list` are checked field by field on the
exact `ctxtFcExactHOL` construction. -/

private def probeX : MlS := Flapjack.Basis.Pure.MlString.ofString "x"
private def probePair : MlS := Flapjack.Basis.Pure.MlString.ofString "pair"
private def probeIgnored : MlS := Flapjack.Basis.Pure.MlString.ofString "ignored"

private def probeCvs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL) :=
  (HolFiniteMapExact.empty).update (f, ([], .one))

private def probeEm : HolFiniteMapExact MlS (BitVec 8) :=
  (HolFiniteMapExact.empty).update (e, (3 : BitVec 8))

private def probeCtxt : PanToCrepContextExact 8 :=
  ctxtFcExactHOL probeCvs probeEm [probeX, probePair]
    [.one, .comb [.one, .one]] [0, 1, 2]

example : probeCtxt.vars.lookup probeX = some (.one, [0]) := by
  simp [probeCtxt, ctxtFcExactHOL, probeX, probePair, withShapeHOL, sizeOfShapeHOL,
    HolFiniteMapExact.updateList, HolFiniteMapExact.empty, FUPDATE_LIST, FUPDATE]
  decide

example : probeCtxt.vars.lookup probePair =
    some (.comb [.one, .one], [1, 2]) := by
  simp [probeCtxt, ctxtFcExactHOL, probePair, probeX, withShapeHOL, sizeOfShapeHOL,
    HolFiniteMapExact.updateList, HolFiniteMapExact.empty, FUPDATE_LIST, FUPDATE]

example : probeCtxt.funcs.lookup f = some ([], .one) := by
  simp [probeCtxt, ctxtFcExactHOL, probeCvs, f,
    HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : probeCtxt.eids.lookup e = some (3 : BitVec 8) := by
  simp [probeCtxt, ctxtFcExactHOL, probeEm, e,
    HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]

example : probeCtxt.vmax = 2 := rfl

private def truncatedCtxt : PanToCrepContextExact 8 :=
  ctxtFcExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty
    [probeX, probeIgnored] [.one] []

example : truncatedCtxt.vars.lookup probeX = some (.one, []) := by
  simp [truncatedCtxt, ctxtFcExactHOL, probeX, withShapeHOL, sizeOfShapeHOL,
    HolFiniteMapExact.updateList, HolFiniteMapExact.empty, FUPDATE_LIST, FUPDATE]

example : truncatedCtxt.vars.lookup probeIgnored = none := by
  simp [truncatedCtxt, ctxtFcExactHOL, probeIgnored, probeX, withShapeHOL,
    sizeOfShapeHOL, HolFiniteMapExact.updateList, HolFiniteMapExact.empty,
    FUPDATE_LIST, FUPDATE]
  decide

example : truncatedCtxt.vmax = 0 := rfl

private def emptyCtxt : PanToCrepContextExact 8 :=
  ctxtFcExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty [] [] []

example : emptyCtxt.vars.lookup probeX = none := by
  simp [emptyCtxt, ctxtFcExactHOL, HolFiniteMapExact.updateList,
    HolFiniteMapExact.empty, probeX, FUPDATE_LIST]

example : emptyCtxt.funcs.lookup f = none := by
  simp [emptyCtxt, ctxtFcExactHOL, HolFiniteMapExact.empty, f]

example : emptyCtxt.eids.lookup e = none := by
  simp [emptyCtxt, ctxtFcExactHOL, HolFiniteMapExact.empty, e]

example : emptyCtxt.vmax = 0 := rfl

example : (ctxtFcExactHOL (width := 8) probeCvs HolFiniteMapExact.empty [] [] []).funcs =
    probeCvs :=
  rfl

/-- Direct replay of the HOL-EVAL `functions_projection=T` row
    (`scripts/hol-probes/ctxt_fc_probe.out`) through the exact
    `ctxt_fc_funcs_eq` port: the constructed context's `funcs` field is the
    supplied function map. -/
example : (ctxtFcExactHOL (width := 8) probeCvs probeEm [probeX, probePair]
    [.one, .comb [.one, .one]] [0, 1, 2]).funcs = probeCvs :=
  ctxtFcFuncsEqHOL probeCvs probeEm [probeX, probePair] [.one, .comb [.one, .one]] [0, 1, 2]

/-- Direct replay of the HOL-EVAL `shaped_slots` row's `eids` field
    (`scripts/hol-probes/ctxt_fc_probe.out`) through the exact
    `ctxt_fc_eids_eq` port: the constructed context's `eids` field is the
    supplied exception-code map. -/
example : (ctxtFcExactHOL (width := 8) probeCvs probeEm [probeX, probePair]
    [.one, .comb [.one, .one]] [0, 1, 2]).eids = probeEm :=
  ctxtFcEidsEqHOL probeCvs probeEm [probeX, probePair] [.one, .comb [.one, .one]] [0, 1, 2]

example : (ctxtFcExactHOL (width := 8) HolFiniteMapExact.empty probeEm
    [probeX] [.one] [0]).eids = probeEm :=
  ctxtFcEidsEqHOL HolFiniteMapExact.empty probeEm [probeX] [.one] [0]

example : (ctxtFcExactHOL (width := 8) HolFiniteMapExact.empty HolFiniteMapExact.empty
    [] [] [4, 1, 7, 3]).vmax = 7 := rfl

example : (ctxtFcExactHOL (width := 8) HolFiniteMapExact.empty HolFiniteMapExact.empty
    [] [] []).vmax = 0 := rfl

end Flapjack.Test.PanToCrepContextExactParity
