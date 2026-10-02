import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVars
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalStateUpdates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAGetSetVars

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof factoring of the native Seq clause after the original
fix_clock_evaluate theorem discharges clock normalization. This has no
independent HOL declaration; the full semantic Seq case uses this equation
without assuming a target execution or successful first result. -/
private theorem evaluateSeqNative {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq first second) state =
      match WordSemStateFiniteExact.evaluate first state with
      | (none, after) => WordSemStateFiniteExact.evaluate second after
      | (some result, after) => (some result, after) := by
  simp only [WordSemStateFiniteExact.evaluate,
    WordSemStateFiniteExact.fix_clock_evaluate]
  cases WordSemStateFiniteExact.evaluate first state with
  | mk result after => cases result <;> rfl

namespace SemanticReturnWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticReturnWitnesses

/-- Full original native Return semantic case with the six original premises
and complete Error-exempt source-permutation/result/frame/result-sensitive locals
conclusion. Source label/list-read errors retain the original exemption. Target
argument moves, generated physical return-register distinctness/lengths, and
preserved renamed-label lookup after the moves are derived from original native
helpers. Both executions return the same location/value list and flush their
locals exactly. No target run, success, or post-state relation is assumed.
The total evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectReturn {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name : Nat) (names : List Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.return name names : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.return name names : WordLangProgHOL (BitVec width)) source target ssa next tables := by
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  refine ⟨target.permute, ?_⟩
  cases found : WordSemStateFiniteExact.getVar name permuted with
  | none =>
    have absent : WordSemStateFiniteExact.getVar name {source with permute := target.permute} = none := found
    simp [WordSemStateFiniteExact.evaluate, absent]
  | some value =>
    cases value with
    | word word =>
      have wrong : WordSemStateFiniteExact.getVar name {source with permute := target.permute} = some (.word word) := found
      simp [WordSemStateFiniteExact.evaluate, wrong]
    | loc label offset =>
      cases valuesFound : WordSemStateFiniteExact.getVars names permuted with
      | none =>
        have read : WordSemStateFiniteExact.getVar name {source with permute := target.permute} = some (.loc label offset) := found
        have absent : WordSemStateFiniteExact.getVars names {source with permute := target.permute} = none := valuesFound
        simp [WordSemStateFiniteExact.evaluate, read, absent]
      | some values =>
        let renamedNames := names.map (optionLookup ssa)
        let rets := (List.range renamedNames.length).map fun x => 2 * (x + 1)
        have lengthValues := Flapjack.WordAlloc.getVarsLength names permuted values valuesFound
        have lengths : rets.length = values.length := by simp [rets, renamedNames, lengthValues]
        have distinct : rets.Nodup := by
          apply List.Nodup.map _ List.nodup_range
          intro x y equal
          change 2 * (x + 1) = 2 * (y + 1) at equal
          omega
        have physical : ∀ register ∈ rets, isPhyVar register := by
          intro register member
          obtain ⟨index, _, equal⟩ := List.mem_map.mp member
          subst register
          simp [isPhyVar]
        have renamedValues := ssaLocalsRelGetVars names values next ssa permuted target ⟨h.2.1, valuesFound⟩
        have moveRun : WordSemStateFiniteExact.evaluate (.move 0 (rets.zip renamedNames)) target =
            (none, WordSemStateFiniteExact.setVars rets values target) := by
          have same : rets.length = renamedNames.length := by simp [rets]
          simp [WordSemStateFiniteExact.evaluate, List.map_fst_zip (Nat.le_of_eq same),
            List.map_snd_zip (Nat.le_of_eq same.symm), distinct, renamedNames, renamedValues]
        have updatedLocals := ssaLocalsRelIgnoreListInsert next ssa permuted target rets values
          ⟨h.2.2.2.2.1, h.2.1, physical, lengths⟩
        have targetLoc := ssaLocalsRelGetVar next ssa permuted
          (WordSemStateFiniteExact.setVars rets values target) name (.loc label offset)
          ⟨updatedLocals, found⟩
        have targetValues := getVarsSetVarsEq rets values target ⟨distinct, lengths.symm⟩
        have compiled : ssaCcTrans (width := width) (.return name names) ssa next tables =
            (.seq (.move 0 (rets.zip renamedNames)) (.return (optionLookup ssa name) rets), ssa, next) := rfl
        dsimp only
        simp only [compiled, evaluateSeqNative, moveRun]
        simp only [WordSemStateFiniteExact.evaluate, targetLoc, targetValues]
        simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.flushState,
          WordSemStateFiniteExact.setVars, Flapjack.WordAlloc.wordStateEqRel, permuted]

end Flapjack.Compiler.Backend.WordAlloc
