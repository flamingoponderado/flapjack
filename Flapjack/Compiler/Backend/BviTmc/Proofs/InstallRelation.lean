import Flapjack.Compiler.Backend.BviTmc.Proofs.StateRelation
import Flapjack.Compiler.Backend.BviTailrec.Proofs.PrimitiveRelation

/-! Dynamic installation under the TMC state relation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem BviSem

/-- Flapjack helper: successful installation is reproduced in the related
state with related input values and the same entry pointer. -/
theorem doInstall_success_rel {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (args relatedArgs : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value) (related : stateRel f source target)
    (valuesRelated : List.Forall₂ (valueRel f) args relatedArgs)
    (run : doInstall (R := ExnOrRet) args source = .val (value, sourceNext)) :
    ∃ targetNext, doInstall (R := ExnOrRet) relatedArgs target = .val (value, targetNext) ∧
      stateRel f sourceNext targetNext ∧ (∃ key, value = .codePtr key) ∧ targetNext.refs = target.refs := by
  obtain ⟨v1, v2, len1, len2, bytes, data, cfg, key, arity, body, rest, cfgNext,
    argsEq, decode1, decode2, lenEq1, lenEq2, oracle0, absent, unique, callback, oracle1, valueEq, stateEq⟩ :=
    BviTailrec.doInstall_success_inv args source sourceNext value run
  subst args
  cases valuesRelated with
  | @cons a targetV1 xs ys firstRel restRel =>
    cases restRel with
    | @cons a targetV2 xs ys secondRel restRel =>
      cases restRel with
      | cons len1Rel restRel =>
        cases len1Rel
        cases restRel with
        | cons len2Rel restRel =>
          cases len2Rel
          cases restRel
          have targetDecode1 := valueToBytes_rel v1 bytes f targetV1 decode1 firstRel
          have targetDecode2 := valueToWords_rel v2 data f targetV2 decode2 secondRel
          obtain ⟨next, config⟩ := cfg
          let code := (key, arity, body) :: rest
          let compiled := (compileEachSource next code).2
          have oracleRelation := related.2.2.2.2.1
          have compilerRelation := related.2.2.2.2.2.1
          have condition : inputCondition next code := by
            have cond := related.2.2.2.2.2.2.2.2.1 0
            simpa [oracle0, code] using cond
          have sourceAbsent : ∀ n ∈ code.map Prod.fst, ¬sptMem n source.code := by
            intro n member present
            obtain ⟨entry, entryMem, eq⟩ := List.mem_map.mp member
            subst n
            have no := absent entry entryMem
            obtain ⟨foundValue, lookup⟩ := (sptMem_iff_lookup _ _).mp present
            rw [no] at lookup
            contradiction
          have namespaces := related.2.2.2.2.2.2.2.1
          have workerBound := related.2.2.2.2.2.2.2.2.2.1
          have targetAbsent := compileEachSource_install_disjoint next code source.code target.code
            condition namespaces (by simpa [oracle0] using workerBound) sourceAbsent
          have ⟨_, _, targetUnique⟩ := compileEachSource_install_relations next code condition
          have targetAbsent' : ∀ entry ∈ compiled, sptLookup entry.1 target.code = none := by
            intro entry member
            have mem : sptMem entry.1 (sptFromAList compiled) :=
              (BviTailrec.sptFromAList_mem_iff compiled entry.1).mpr (List.mem_map_of_mem member)
            have absent' := targetAbsent entry.1 mem
            cases found : sptLookup entry.1 target.code with
            | none => rfl
            | some v => exact (absent' ((sptMem_iff_lookup _ _).mpr ⟨v, found⟩)).elim
          have targetOracle0 : target.compileOracle 0 = (config, compiled) := by
            rw [oracleRelation]
            simp [BackendProps.stateCo, oracle0, code, compiled]
          have targetCallback : ∃ config',
              target.compile config compiled = some (bytes, data, config') ∧
              cfgNext = ((compileEachSource next code).1, config') := by
            rw [compilerRelation] at callback
            change BackendProps.stateCc compileEachSource target.compile (next, config) code =
              some (bytes, data, cfgNext) at callback
            unfold BackendProps.stateCc at callback
            have pairEq : compileEachSource next code =
                ((compileEachSource next code).1, (compileEachSource next code).2) :=
              (Prod.eta (compileEachSource next code)).symm
            rw [pairEq] at callback
            dsimp only at callback
            cases res : target.compile config compiled with
            | none => simp [← show compiled = (compileEachSource next code).2 from rfl, res] at callback
            | some output =>
              obtain ⟨b, d, c⟩ := output
              simp [← show compiled = (compileEachSource next code).2 from rfl, res] at callback
              obtain ⟨rfl, rfl, eq⟩ := callback
              exact ⟨c, rfl, eq.symm⟩
          obtain ⟨config', targetCallback, cfgNextEq⟩ := targetCallback
          have nextEq : (source.compileOracle 1).1.1 = (compileEachSource next code).1 := by
            rw [oracle1, cfgNextEq]
          have targetOracle1 : (target.compileOracle 1).1 = config' := by
            rw [oracleRelation]
            simp [BackendProps.stateCo, oracle1, cfgNextEq]
          obtain ⟨compiledBody, compiledRest, head⟩ := compileEachSource_head next key arity body rest
          have head' : compiled = (key, arity, compiledBody) :: compiledRest := by simpa [compiled, code] using head
          have targetRun : doInstall (R := ExnOrRet) [targetV1, targetV2, .number len1, .number len2] target =
              .val (.codePtr key, { target with code := sptUnion target.code (sptFromAList compiled), compileOracle := fun n => target.compileOracle (n + 1) }) := by
            have targetUniqueHead : (((key, arity, compiledBody) :: compiledRest).map Prod.fst).Nodup := by
              rw [← head']
              exact targetUnique
            cases target
            simp_all [BviSem.doInstall]
            exact targetAbsent'.2
          have stateRelated := stateRel_install_code_and_oracle f source target related
            (by simpa [oracle0, code] using sourceAbsent) (by simpa [oracle0, code] using nextEq)
          refine ⟨{ target with code := sptUnion target.code (sptFromAList compiled), compileOracle := fun n => target.compileOracle (n + 1) },
            ?_, ?_, ⟨key, valueEq⟩, rfl⟩
          · simpa [valueEq] using targetRun
          · simpa [stateEq, oracle0, code, compiled] using stateRelated

end Flapjack.Compiler.Backend.BviTmc
