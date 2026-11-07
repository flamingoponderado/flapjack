import Flapjack.Compiler.Backend.BviInline.Proofs.StateRelation
import Flapjack.Compiler.Backend.BviInline.Proofs.ProgramRelation
import Flapjack.Compiler.Backend.BviTailrec.Proofs.PrimitiveRelation

/-! State invariants for dynamically installed BVI code. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem BackendProps

/-- Flapjack infrastructure: installing fresh, distinctly labelled code and
advancing the oracle preserves the inliner state relation. The next cache is
the one produced by the compiler, as required by successful installation. -/
theorem inStateRel_after_install {C F : Type}
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F) (target : BviState C F)
    (related : InStateRel source target)
    (distinct : ((source.compileOracle 0).2.map Prod.fst).Nodup)
    (fresh : ∀ name, sptDomain source.code name → name ∉ (source.compileOracle 0).2.map Prod.fst)
    (nextCache : (source.compileOracle 1).1.1 =
      (inlineAllSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).1) :
    InStateRel
      { source with
        code := sptUnion source.code (sptFromAList (source.compileOracle 0).2)
        compileOracle := fun n => source.compileOracle (n + 1) }
      { target with
        code := sptUnion target.code
          (sptFromAList (inlineAllSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)
        compileOracle := fun n => target.compileOracle (n + 1) } := by
  rcases related with ⟨refs, clock, global, ffi, oracle, cache, compiler, domains, codeRel⟩
  have targetFresh : ∀ name, sptMem name target.code → name ∉ (source.compileOracle 0).2.map Prod.fst := by
    intro name present
    apply fresh name
    rwa [← domains]
  have range := inlineAllSource_cache_subspt (source.compileOracle 0).2
    (source.compileOracle 0).1.1 target.code distinct cache targetFresh
  have codes := inlineAllSource_union_related (source.compileOracle 0).2
    (source.compileOracle 0).1.1 source.code target.code distinct cache targetFresh codeRel
  have newDomains : sptDomain (sptUnion target.code
      (sptFromAList (inlineAllSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)) =
      sptDomain (sptUnion source.code (sptFromAList (source.compileOracle 0).2)) := by
    rw [sptDomain_sptUnion, sptDomain_sptUnion, domains]
    funext name
    apply propext
    change sptDomain source.code name ∨ sptMem name (sptFromAList
      (inlineAllSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2) ↔
      sptDomain source.code name ∨ sptMem name (sptFromAList (source.compileOracle 0).2)
    rw [BviTailrec.sptFromAList_mem_iff, BviTailrec.sptFromAList_mem_iff, inlineAllSource_names]
  refine ⟨refs, clock, global, ffi, ?_, ?_, compiler, newDomains, codes⟩
  · funext n
    exact congrFun oracle (n + 1)
  · simpa [nextCache] using range

/-- Flapjack infrastructure: a successful source installation is reproduced
by the inlined target, with the same entry pointer and related states. -/
theorem doInstall_success_rel {C F : Type} (args : List Value)
    (source sourceNext : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (target : BviState C F) (value : Value) (related : InStateRel source target)
    (run : doInstall (R := ExnOrRet) args source = .val (value, sourceNext)) :
    ∃ targetNext, doInstall (R := ExnOrRet) args target = .val (value, targetNext) ∧
      InStateRel sourceNext targetNext := by
  obtain ⟨v1, v2, len1, len2, bytes, data, cfg, key, arity, body, rest, cfgNext,
    argsEq, decode1, decode2, lenEq1, lenEq2, oracle0, absent, unique, callback, oracle1, valueEq, stateEq⟩ :=
    BviTailrec.doInstall_success_inv args source sourceNext value run
  obtain ⟨cache, config⟩ := cfg
  let code := (key, arity, body) :: rest
  let compiled := (inlineAllSource cache code).2
  have oracleRelation := related.2.2.2.2.1
  have compilerRelation := related.2.2.2.2.2.2.1
  have targetAbsent : ∀ entry ∈ compiled, sptLookup entry.1 target.code = none := by
    intro entry member
    have memberNames : entry.1 ∈ code.map Prod.fst := by
      have h : entry.1 ∈ compiled.map Prod.fst := List.mem_map_of_mem member
      simpa [compiled, inlineAllSource_names] using h
    obtain ⟨original, originalMem, same⟩ := List.mem_map.mp memberNames
    have no := absent original (by simpa [code] using originalMem)
    cases lookup : sptLookup entry.1 target.code with
    | none => rfl
    | some value =>
      have present : sptDomain target.code entry.1 := (sptMem_iff_lookup _ _).2 ⟨value, lookup⟩
      rw [related.2.2.2.2.2.2.2.1] at present
      have absentSource : sptLookup entry.1 source.code = none := by simpa [same] using no
      simp [sptDomain, absentSource] at present
  have targetUnique : (compiled.map Prod.fst).Nodup := by
    simpa [compiled, inlineAllSource_names, code] using unique
  have targetOracle0 : target.compileOracle 0 = (config, compiled) := by
    rw [oracleRelation]
    simp [inCo, stateCo, oracle0, code, compiled]
  have targetCallback : ∃ config',
      target.compile config compiled = some (bytes, data, config') ∧
      cfgNext = ((inlineAllSource cache code).1, config') := by
    rw [compilerRelation] at callback
    change stateCc inlineAllSource target.compile (cache, config) code =
      some (bytes, data, cfgNext) at callback
    unfold stateCc at callback
    have pairEq : inlineAllSource cache code =
        ((inlineAllSource cache code).1, (inlineAllSource cache code).2) :=
      (Prod.eta (inlineAllSource cache code)).symm
    rw [pairEq] at callback
    dsimp only at callback
    cases res : target.compile config compiled with
    | none => simp [← show compiled = (inlineAllSource cache code).2 from rfl, res] at callback
    | some output =>
      obtain ⟨b, d, c⟩ := output
      simp [← show compiled = (inlineAllSource cache code).2 from rfl, res] at callback
      obtain ⟨rfl, rfl, eq⟩ := callback
      exact ⟨c, rfl, eq.symm⟩
  obtain ⟨config', targetCallback, cfgNextEq⟩ := targetCallback
  have nextEq : (source.compileOracle 1).1.1 = (inlineAllSource cache code).1 := by
    rw [oracle1, cfgNextEq]
  have targetOracle1 : (target.compileOracle 1).1 = config' := by
    rw [oracleRelation]
    simp [inCo, stateCo, oracle1, cfgNextEq]
  have head' : compiled = (key, arity, inlineExpSource cache body) ::
      (inlineAllSource (if canonicalWrapper key arity (inlineExpSource cache body) then
        sptInsert key (arity, inlineExpSource cache body) cache else cache) rest).2 := by
    simp [compiled, code, inlineAllSource]
  have targetRun : doInstall (R := ExnOrRet) args target =
      .val (.codePtr key, { target with
        code := sptUnion target.code (sptFromAList compiled)
        compileOracle := fun n => target.compileOracle (n + 1) }) := by
    have targetUniqueHead : (((key, arity, inlineExpSource cache body) ::
        (inlineAllSource (if canonicalWrapper key arity (inlineExpSource cache body) then
          sptInsert key (arity, inlineExpSource cache body) cache else cache) rest).2).map Prod.fst).Nodup := by
      rw [← head']
      exact targetUnique
    cases target
    simp_all [BviSem.doInstall]
    exact targetAbsent.2
  have sourceFresh : ∀ name, sptDomain source.code name → name ∉ code.map Prod.fst := by
    intro name present member
    obtain ⟨entry, entryMem, same⟩ := List.mem_map.mp member
    have no := absent entry (by simpa [code] using entryMem)
    obtain ⟨foundValue, lookup⟩ := (sptMem_iff_lookup _ _).1 present
    rw [same] at no
    rw [no] at lookup
    contradiction
  have stateRelated := inStateRel_after_install source target related
    (by simpa [oracle0, code] using unique)
    (by simpa [oracle0, code] using sourceFresh) (by simpa [oracle0, code] using nextEq)
  refine ⟨{ target with
    code := sptUnion target.code (sptFromAList compiled)
    compileOracle := fun n => target.compileOracle (n + 1) }, ?_, ?_⟩
  · simpa [valueEq] using targetRun
  · simpa [stateEq, oracle0, code, compiled] using stateRelated

/-- Flapjack infrastructure: the installation case of the primitive
simulation. A source type error is intentionally unconstrained, matching
the error convention of the evaluator simulation. -/
theorem doApp_install_rel {C F : Type} (args : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F) (target : BviState C F)
    (related : InStateRel source target) :
    match doApp .install args source with
    | .err error => error ≠ .abort .typeError → doApp .install args target = .err error
    | .val (value, sourceNext) =>
      ∃ targetNext, InStateRel sourceNext targetNext ∧
        doApp .install args target = .val (value, targetNext) := by
  cases run : doApp .install args source with
  | err error =>
    have errorEq := BviTailrec.doApp_install_error args source error run
    simp [errorEq]
  | val result =>
    obtain ⟨value, sourceNext⟩ := result
    have installRun : doInstall (R := ExnOrRet) args source = .val (value, sourceNext) := by
      simpa only [BviSem.doApp] using run
    obtain ⟨targetNext, targetRun, states⟩ :=
      doInstall_success_rel args source sourceNext target value related installRun
    exact ⟨targetNext, states, by simpa only [BviSem.doApp] using targetRun⟩

end Flapjack.Compiler.Backend.BviInline
