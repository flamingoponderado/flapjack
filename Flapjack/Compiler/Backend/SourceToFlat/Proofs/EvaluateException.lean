import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateSequence

/-! Exception-declaration prerequisites for the factored source-to-flat
simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open OracleInvariant

/-- The next reserved exception index has no constructor-map entry at any
arity. -/
theorem idxRangeRel_exception_free {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (range : idxRangeRel interp genv nextType nextExn evalState (start, finish, other))
    (fits : start.eidx < finish.eidx) (arity : Nat) :
    genv.c.lookup ((start.eidx, none), arity) = none := by
  obtain ⟨_, _, _, _, tuple, _, _, disjoint, _, _⟩ := range
  cases tuple
  have separate := disjoint 0 3 (by simp) (by simp) (by decide)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at separate
  have block : (start.eidx, IndexKind.exception) ∈ idxBlock start finish := by
    change idxBlock start finish (start.eidx, IndexKind.exception)
    simp [idxBlock, fits]
  cases lookup : genv.c.lookup ((start.eidx, none), arity) with
  | none => rfl
  | some stamp =>
    have allocated : (start.eidx, IndexKind.exception) ∈ genvAllocatedIndices genv := by
      exact ⟨arity, by simp [lookup]⟩
    have member : (start.eidx, IndexKind.exception) ∈ idxBlock start finish ∩ genvAllocatedIndices genv :=
      ⟨block, allocated⟩
    rw [separate] at member
    exact member.elim

/-- The next source exception stamp is absent from the current constructor
map, by the index-range freshness condition. -/
theorem idxRangeRel_exceptionStamp_fresh {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (range : idxRangeRel interp genv nextType nextExn evalState (start, finish, other)) :
    ∀ key, genv.c.lookup key ≠ some (.exnStamp nextExn) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, fresh⟩ := range
  intro key found
  exact fresh nextExn (Nat.le_refl _) ⟨key, found⟩

/-- Installing a fresh exception constructor extends the factored global
environment while leaving existing values and type entries unchanged. -/
theorem GlobalGrowth.installException (genv : GlobalEnv) (idx arity stamp : Nat)
    (fresh : genv.c.lookup ((idx, none), arity) = none) :
    GlobalGrowth genv { genv with c := finiteUpdate genv.c ((idx, none), arity) (.exnStamp stamp) } := by
  classical
  refine ⟨Nat.le_refl _, ?_, ?_, fun _ _ h => h⟩
  · intro _ _ lookup
    exact lookup
  · intro key value lookup
    have different : key ≠ ((idx, none), arity) := by
      intro eq
      subst key
      rw [fresh] at lookup
      contradiction
    simpa [finiteUpdate, FUPDATE_HOL, different] using lookup

/-- Adding an exception constructor adds exactly its exception index to the
allocated-index set. -/
theorem allocatedIndices_installException (genv : GlobalEnv) (idx arity stamp : Nat) :
    genvAllocatedIndices { genv with c := finiteUpdate genv.c ((idx, none), arity) (.exnStamp stamp) } =
      genvAllocatedIndices genv ∪ {(idx, .exception)} := by
  classical
  ext ⟨i, kind⟩
  cases kind with
  | «variable» =>
    change (i < genv.v.length ∧ genv.v[i]?.getD none ≠ none) ↔
      (i < genv.v.length ∧ genv.v[i]?.getD none ≠ none) ∨ (i, IndexKind.variable) = (idx, .exception)
    simp
  | «type» =>
    change ((∃ cn a, ((finiteUpdate genv.c ((idx, none), arity) (.exnStamp stamp)).lookup ((cn, some i), a)).isSome) ∨
      (genv.tys.lookup i).isSome) ↔
      ((∃ cn a, (genv.c.lookup ((cn, some i), a)).isSome) ∨ (genv.tys.lookup i).isSome) ∨
        (i, IndexKind.type) = (idx, .exception)
    simp [finiteUpdate, FUPDATE_HOL]
  | «exception» =>
    change (∃ a, ((finiteUpdate genv.c ((idx, none), arity) (.exnStamp stamp)).lookup ((i, none), a)).isSome) ↔
      (∃ a, (genv.c.lookup ((i, none), a)).isSome) ∨ (i, IndexKind.exception) = (idx, .exception)
    by_cases same : i = idx
    · subst i
      constructor
      · intro _
        exact Or.inr rfl
      · intro _
        exact ⟨arity, by simp [finiteUpdate, FUPDATE_HOL]⟩
    · simp [finiteUpdate, FUPDATE_HOL, same]

/-- Installing a fresh exception consumes the next reserved exception index
and advances the source exception-stamp freshness bound. -/
theorem idxRangeRel_installException {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind)) (arity : Nat)
    (range : idxRangeRel interp genv nextType nextExn evalState (start, finish, other))
    (fits : start.eidx + 1 ≤ finish.eidx) :
    idxRangeRel interp { genv with c := finiteUpdate genv.c ((start.eidx, none), arity) (.exnStamp nextExn) }
      nextType (nextExn + 1) evalState ({ start with eidx := start.eidx + 1 }, finish, other) := by
  classical
  obtain ⟨_, _, final, _, tuple, nextMatch, previous, disjoint, types, exceptions⟩ := range
  cases tuple
  refine ⟨_, _, final, other, rfl, nextMatch, previous, ?_, ?_, ?_⟩
  · rw [allocatedIndices_installException]
    apply allDisjoint_consume (idxBlock start finish)
      (idxBlock { start with eidx := start.eidx + 1 } finish) (idxFinalBlock final)
      other (genvAllocatedIndices genv) (start.eidx, .exception) disjoint
    · intro ⟨i, kind⟩ member
      change idxBlock { start with eidx := start.eidx + 1 } finish (i, kind) at member
      change idxBlock start finish (i, kind)
      cases kind <;> simp only [idxBlock] at member ⊢ <;> omega
    · change idxBlock start finish (start.eidx, .exception)
      simp only [idxBlock]
      omega
    · change ¬ idxBlock { start with eidx := start.eidx + 1 } finish (start.eidx, .exception)
      simp only [idxBlock]
      omega
  · intro cn t bound ⟨key, found⟩
    by_cases same : key = ((start.eidx, none), arity)
    · subst key
      simp [finiteUpdate, FUPDATE_HOL] at found
    · have original : genv.c.lookup key = some (.typeStamp cn t) := by
        simpa [finiteUpdate, FUPDATE_HOL, same] using found
      exact types cn t bound ⟨key, original⟩
  · intro cn bound ⟨key, found⟩
    by_cases same : key = ((start.eidx, none), arity)
    · subst key
      simp [finiteUpdate, FUPDATE_HOL] at found
      omega
    · have original : genv.c.lookup key = some (.exnStamp cn) := by
        simpa [finiteUpdate, FUPDATE_HOL, same] using found
      exact exceptions cn (by omega) ⟨key, original⟩

/-- Installing an exception constructor does not change typed-constructor
lookup, so the type-constructor consistency condition is preserved. -/
theorem genvCTysOk_installException (genv : GlobalEnv) (idx arity stamp : Nat)
    (valid : genvCTysOk genv.c genv.tys) :
    genvCTysOk (finiteUpdate genv.c ((idx, none), arity) (.exnStamp stamp)) genv.tys := by
  classical
  intro cn tyId a present
  apply valid cn tyId a
  simpa [finiteUpdate, FUPDATE_HOL] using present

/-- Every existing constructor is an exception exactly when its flat type
identifier is absent. The built-in division exception supplies the reference
point for the constructor-map compatibility condition. -/
theorem genvCOk_exception_class (genv : GlobalEnv) (valid : genvCOk genv.c)
    (cn : FlatLang.CtorId × FlatLang.TypeId) (arity : Nat) (stamp : Stamp)
    (lookup : genv.c.lookup (cn, arity) = some stamp) :
    SemanticPrimitivesHOL.sameType (.exnStamp 0) stamp = true ↔ cn.2 = none := by
  have h := valid.2.2.2.1 (Flapjack.Compiler.Backend.BackendCommon.divTag, none) cn 0 arity
    divStamp stamp valid.2.1.1 lookup
  cases stamp <;> simpa [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType,
    FlatSem.ctorSameType, divStamp, eq_comm] using h

/-- A fresh exception index and source stamp preserve constructor-map
compatibility when the new exception constructor is installed. -/
theorem genvCOk_installException (genv : GlobalEnv) (idx arity stamp : Nat)
    (valid : genvCOk genv.c)
    (free : genv.c.lookup ((idx, none), arity) = none)
    (fresh : ∀ key, genv.c.lookup key ≠ some (.exnStamp stamp)) :
    genvCOk (finiteUpdate genv.c ((idx, none), arity) (.exnStamp stamp)) := by
  classical
  let updated := finiteUpdate genv.c ((idx, none), arity) (.exnStamp stamp)
  have growth := GlobalGrowth.installException genv idx arity stamp free
  have oldLookup {key value} (h : genv.c.lookup key = some value) : updated.lookup key = some value :=
    growth.constructors key value h
  have classify (cn : FlatLang.CtorId × FlatLang.TypeId) (a : Nat) (s : Stamp)
      (h : updated.lookup (cn, a) = some s) :
      ((cn, a) = ((idx, none), arity) ∧ s = .exnStamp stamp) ∨ genv.c.lookup (cn, a) = some s := by
    by_cases same : (cn, a) = ((idx, none), arity)
    · left
      refine ⟨same, ?_⟩
      simp [updated, finiteUpdate, FUPDATE_HOL, same] at h
      exact h.symm
    · right
      simpa [updated, finiteUpdate, FUPDATE_HOL, same] using h
  refine ⟨⟨oldLookup valid.1.1, oldLookup valid.1.2⟩,
    ⟨oldLookup valid.2.1.1, oldLookup valid.2.1.2.1, oldLookup valid.2.1.2.2.1, oldLookup valid.2.1.2.2.2⟩,
    ⟨oldLookup valid.2.2.1.1, oldLookup valid.2.2.1.2⟩, ?_, ?_⟩
  · intro cn1 cn2 a1 a2 s1 s2 h1 h2
    rcases classify cn1 a1 s1 h1 with ⟨eq1, rfl⟩ | old1 <;>
      rcases classify cn2 a2 s2 h2 with ⟨eq2, rfl⟩ | old2
    · cases cn1; cases cn2
      simp_all [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType, FlatSem.ctorSameType]
    · have kind := genvCOk_exception_class genv valid cn2 a2 s2 old2
      cases cn1 with
      | mk c t =>
        cases cn2 with
        | mk c' t' =>
          cases s2 <;> cases t' <;>
            simp_all [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType, FlatSem.ctorSameType]
    · have kind := genvCOk_exception_class genv valid cn1 a1 s1 old1
      cases cn1 with
      | mk c t =>
        cases cn2 with
        | mk c' t' =>
          cases s1 <;> cases t <;>
            simp_all [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType, FlatSem.ctorSameType]
    · exact valid.2.2.2.1 cn1 cn2 a1 a2 s1 s2 old1 old2
  · intro cn1 cn2 a1 a2 s h1 h2
    rcases classify cn1 a1 s h1 with ⟨eq1, eqStamp1⟩ | old1 <;>
      rcases classify cn2 a2 s h2 with ⟨eq2, eqStamp2⟩ | old2
    · cases cn1; cases cn2
      simp_all
    · subst s
      exact False.elim (fresh (cn2, a2) old2)
    · subst s
      exact False.elim (fresh (cn1, a1) old1)
    · exact valid.2.2.2.2 cn1 cn2 a1 a2 s old1 old2

/-- Installing a fresh exception stamp preserves the factored invariant and
advances both source and compiler exception counters. -/
theorem factoredInvariant_installException {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (arity : Nat)
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (fits : start.eidx + 1 ≤ finish.eidx) :
    factoredInvariant interp transform gen
      { genv with c := finiteUpdate genv.c ((start.eidx, none), arity) (.exnStamp source.nextExnStamp) }
      ({ start with eidx := start.eidx + 1 }, finish, other)
      { source with nextExnStamp := source.nextExnStamp + 1 } flat := by
  have copy := valid
  obtain ⟨cOk, typesOk, states, range, invs, oracle, globals, reserved, genInv, fin⟩ := copy
  have free := idxRangeRel_exception_free interp genv source.nextTypeStamp source.nextExnStamp source.evalState
    start finish other range (by omega) arity
  have fresh := idxRangeRel_exceptionStamp_fresh interp genv source.nextTypeStamp source.nextExnStamp
    source.evalState start finish other range
  have growth := GlobalGrowth.installException genv start.eidx arity source.nextExnStamp free
  have grownStates := stateRel_growth genv _ growth source flat states
  have nextStates : StateRel
      { genv with c := finiteUpdate genv.c ((start.eidx, none), arity) (.exnStamp source.nextExnStamp) }
      { source with nextExnStamp := source.nextExnStamp + 1 } flat := by
    cases grownStates with
    | intro nonempty refs clock ffi => exact .intro _ _ nonempty refs clock ffi
  have nextRange := idxRangeRel_installException interp genv source.nextTypeStamp source.nextExnStamp
    source.evalState start finish other arity range fits
  have nextInvs : srcOracInvs interp transform
      { genv with c := finiteUpdate genv.c ((start.eidx, none), arity) (.exnStamp source.nextExnStamp) }
      source.evalState := ⟨invs.1, srcOracEnvInvs_growth interp genv _ growth _ invs.2.1, invs.2.2⟩
  exact ⟨genvCOk_installException genv start.eidx arity source.nextExnStamp cOk free fresh,
    genvCTysOk_installException genv start.eidx arity source.nextExnStamp typesOk,
    nextStates, nextRange, nextInvs, oracle, globals, reserved, genInv, fin⟩

/-- The source and compiler exception declarations export the same domains. -/
theorem envDomainEq_exception (name : ConN) (idx arity stamp : Nat) :
    EnvDomainEq { v := nsEmpty, c := nsSing name (idx, none) }
      ({ v := nsEmpty, c := nsSing name (arity, .exnStamp stamp) } : SemEnv Value) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext id
    apply propext
    cases id <;> simp [nsDom, nsLookup, nsEmpty]
  · funext path
    apply propext
    cases path <;> simp [nsDomMod, nsLookupMod, nsEmpty]
  · funext id
    apply propext
    cases id with
    | short key =>
      by_cases same : key = name
      · subst key; simp [nsDom, nsLookup, nsSing]
      · simp [nsDom, nsLookup, nsSing, List.lookup, BEq.beq, same]
    | long moduleName rest => simp [nsDom, nsLookup, nsSing]
  · funext path
    apply propext
    cases path <;> simp [nsDomMod, nsLookupMod, nsSing]

/-- The newly installed exception stamp relates the singleton constructor
environments returned by source and compiler. -/
theorem globalEnvInv_exception (genv : GlobalEnv) (name : ConN) (idx arity stamp : Nat) :
    GlobalEnvInv { genv with c := finiteUpdate genv.c ((idx, none), arity) (.exnStamp stamp) }
      { v := nsEmpty, c := nsSing name (idx, none) } (fun _ => False)
      { v := nsEmpty, c := nsSing name (arity, .exnStamp stamp) } := by
  classical
  apply GlobalEnvInv.intro
  · intro id value _ lookup
    cases id <;> simp [nsEmpty, nsLookup] at lookup
  · intro id a s lookup
    cases id with
    | short key =>
      by_cases same : key = name
      · subst key
        simp [nsLookup, nsSing] at lookup
        obtain ⟨rfl, rfl⟩ := lookup
        refine ⟨idx, none, ?_, ?_, ?_⟩
        · simp [nsLookup, nsSing]
        · simp [finiteUpdate, FUPDATE_HOL]
        · intro tyId ctors impossible
          cases impossible
      · simp [nsLookup, nsSing, List.lookup, BEq.beq, same] at lookup
    | long moduleName rest => simp [nsLookup, nsSing] at lookup

/-- Exception declarations satisfy the factored declaration induction
hypothesis. The relations and evaluator carriers still need HOL review. -/
theorem factoredDecIH_dexn {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (location : Flapjack.Misc.Location.Locs) (name : ConN) (types : List AstT) :
    FactoredDecIH (F := F) interp transform [.dexn location name types] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result sourceRun invariant compiled _envInv _notTypeError generation _future bounded
  have compEq := compiled
  simp only [compileDecs, Prod.mk.injEq] at compEq
  obtain ⟨_, nextEq, envEq, genEq, codeEq⟩ := compEq
  subst next
  subst nextEnv
  subst nextGen
  subst flatDecs
  have sourceEq := sourceRun
  simp only [EvaluateHOL.evaluateDecs, Prod.mk.injEq] at sourceEq
  obtain ⟨stateEq, resultEq⟩ := sourceEq
  subst sourceLast
  subst result
  have fits : start.eidx + 1 ≤ finish.eidx := bounded.2.2
  have range := invariant.2.2.2.1
  have free := idxRangeRel_exception_free interp genv source.nextTypeStamp source.nextExnStamp source.evalState
    start finish other range (by omega) types.length
  have growth := GlobalGrowth.installException genv start.eidx types.length source.nextExnStamp free
  have finalInvariant := factoredInvariant_installException interp transform gen genv start finish other
    source flat types.length invariant fits
  refine ⟨flat, _, none, ?_, finalInvariant.2.2.1, ?_, ?_, ?_⟩
  · simp [FlatSem.evaluateDecs]
  · intro _
    exact ⟨finalInvariant, oracForwardRel_refl interp source.evalState, growth⟩
  · intro resultEnv same
    cases same
    exact ⟨rfl, envDomainEq_exception name start.eidx types.length source.nextExnStamp,
      generation, globalEnvInv_exception genv name start.eidx types.length source.nextExnStamp⟩
  · intro error impossible
    cases impossible

end Flapjack.Compiler.Backend.SourceToFlat
