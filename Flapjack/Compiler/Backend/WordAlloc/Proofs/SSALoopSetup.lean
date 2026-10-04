import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFakeConstChain
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMovePreserve
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsBounds

namespace Flapjack.Compiler.Backend.WordAlloc

namespace LoopSetupWitnesses

/-- Canonical roundtrip of the imported native finite-map state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopSetupWitnesses


-- Flapjack factoring of the original inline fake-initialization argument;
-- no independently claimed HOL declaration or public simulation assumption.
private theorem initializedLookup {α : Type} (names : List Nat) (value : α)
    (locals : Spt α) (key : Nat) :
    sptLookup key (names.foldr (fun name tree => sptInsert name value tree) locals) =
      if key ∈ names then some value else sptLookup key locals := by
  induction names with
  | nil => simp
  | cons name names ih =>
    simp only [List.foldr_cons]
    by_cases equal : key = name
    · subst key
      simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne _ _ _ _ equal,ih]
      simp [equal]

private theorem extendedLocals {width : Nat} [NeZero width]
    (names : List Nat) (ssa : Spt Nat) (next : Nat)
    (source target : Spt (WordLocW width))
    (outputs : List Nat) (mapOut : Spt Nat) (counter : Nat)
    (produced : listNextVarRename names ssa next = (outputs,mapOut,counter))
    (distinct : names.Nodup) (missing : ∀ key ∈ names, sptLookup key ssa = none)
    (valid : ssaMapOK next ssa) (related : ssaLocalsRel next ssa source target) :
    ssaLocalsRel counter mapOut source
      (outputs.foldr (fun key locals => sptInsert key (.word 0) locals) target) := by
  have arithmetic := listNextVarRenameLemma1 names ssa next outputs mapOut counter produced
  have lookup := listNextVarRenameLemma2Prime names ssa next outputs mapOut counter produced distinct
  have fresh : ∀ register ∈ outputs, next ≤ register := by
    intro register member
    rw [arithmetic.2.1] at member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    omega
  have preserved : ∀ register, register < next →
      sptLookup register (outputs.foldr (fun key locals => sptInsert key (.word 0) locals) target) =
        sptLookup register target := by
    intro register bound
    have absent : register ∉ outputs := by intro member; have := fresh register member; omega
    simp [initializedLookup,absent]
  refine ⟨?_,?_⟩
  · intro key register read
    apply (sptMem_iff_lookup register _).mpr
    by_cases member : key ∈ names
    · have written : register ∈ outputs := by
        rw [lookup.1]
        exact List.mem_map.mpr ⟨key,member,by simp [read]⟩
      exact ⟨.word 0,by simp [initializedLookup,written]⟩
    · have original : sptLookup key ssa = some register := by
        rw [←lookup.2.2.1 key member]
        exact read
      obtain ⟨value,found⟩ := (sptMem_iff_lookup register target).mp (related.1 key register original)
      exact ⟨value,by rw [preserved register (valid key register original).2]; exact found⟩
  · intro key value found
    obtain ⟨domain,matched,bound⟩ := related.2 key value found
    obtain ⟨register,original⟩ := (sptMem_iff_lookup key ssa).mp domain
    have absent : key ∉ names := by
      intro member
      rw [missing key member] at original
      contradiction
    have read : sptLookup key mapOut = some register := by
      rw [lookup.2.2.1 key absent]
      exact original
    refine ⟨(sptMem_iff_lookup key _).mpr ⟨register,read⟩,?_,?_⟩
    · simp only [read,Option.getD_some]
      rw [preserved register (valid key register original).2]
      simpa only [original,Option.getD_some] using matched
    · intro allocated
      have := bound allocated
      rw [arithmetic.2.2]
      omega

-- The two original renaming intervals are disjoint, so the setup map is
-- injective over their combined input names. This is private inline factoring.
private theorem renameStagesInjective (first second : List Nat) (ssa : Spt Nat)
    (next : Nat) (firstOut secondOut : List Nat) (middle finalMap : Spt Nat)
    (middleNext finalNext : Nat)
    (firstProduced : listNextVarRename first ssa next = (firstOut,middle,middleNext))
    (secondProduced : listNextVarRename second middle middleNext = (secondOut,finalMap,finalNext))
    (distinct : (first ++ second).Nodup) :
    ∀ x ∈ first ++ second, ∀ y ∈ first ++ second,
      optionLookup finalMap x = optionLookup finalMap y → x = y := by
  have parts := List.nodup_append.mp distinct
  have firstArithmetic := listNextVarRenameLemma1 first ssa next firstOut middle middleNext firstProduced
  have secondArithmetic := listNextVarRenameLemma1 second middle middleNext secondOut finalMap finalNext secondProduced
  have firstLookup := listNextVarRenameLemma2Prime first ssa next firstOut middle middleNext firstProduced parts.1
  have secondLookup := listNextVarRenameLemma2Prime second middle middleNext secondOut finalMap finalNext secondProduced parts.2.1
  have early : ∀ register ∈ firstOut, register < middleNext := by
    intro register member
    rw [firstArithmetic.2.1] at member
    obtain ⟨index,indexMember,rfl⟩ := List.mem_map.mp member
    have bound := List.mem_range.mp indexMember
    rw [firstArithmetic.2.2]
    omega
  have late : ∀ register ∈ secondOut, middleNext ≤ register := by
    intro register member
    rw [secondArithmetic.2.1] at member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    omega
  have outputDistinct : (firstOut ++ secondOut).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨firstArithmetic.1,secondArithmetic.1,?_⟩
    intro x inFirst y inSecond equal
    have := early x inFirst
    have := late y inSecond
    omega
  have selector : optionLookup finalMap = (fun key => (sptLookup key finalMap).getD 0) := by
    funext key
    unfold optionLookup
    cases sptLookup key finalMap <;> rfl
  have mapFirst : first.map (optionLookup finalMap) = firstOut := by
    rw [firstLookup.1,selector]
    apply List.map_congr_left
    intro key member
    have absent : key ∉ second := by
      intro both
      exact parts.2.2 key member key both rfl
    rw [secondLookup.2.2.1 key absent]
  have mapSecond : second.map (optionLookup finalMap) = secondOut := by
    rw [secondLookup.1,selector]
  have mappedDistinct : ((first ++ second).map (optionLookup finalMap)).Nodup := by
    simpa only [List.map_append,mapFirst,mapSecond] using outputDistinct
  exact (List.nodup_map_iff_inj_on distinct).mp mappedDistinct

/-- Full original Loop entry setup theorem. The original five premises derive
actual setup execution and all ten state/map/counter/scoped-injection results;
no target execution, post-state relation or global injection is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopSetupCorrect {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (names exitNames : Spt Unit)
    (setupProg : WordLangProgHOL (BitVec width)) (mapOut : Spt Nat) (nextOut : Nat)
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ ssaMapOK next ssa ∧
      isAllocVar next ∧ loopSetup names exitNames ssa next = (setupProg,mapOut,nextOut)) :
    ∃ after : WordSemStateFiniteExact width C F,
      WordSemStateFiniteExact.evaluate setupProg target = (none,after) ∧
      Flapjack.WordAlloc.wordStateEqRel source after ∧
      ssaLocalsRel nextOut mapOut source.locals after.locals ∧ next ≤ nextOut ∧
      isAllocVar nextOut ∧ ssaMapOK nextOut mapOut ∧
      sptDomain mapOut = (fun key => sptDomain ssa key ∨ sptDomain (sptUnion names exitNames) key) ∧
      (∀ x y, sptDomain names x → sptDomain names y →
        optionLookup mapOut x = optionLookup mapOut y → x = y) ∧
      (∀ x y, sptDomain exitNames x → sptDomain exitNames y →
        optionLookup mapOut x = optionLookup mapOut y → x = y) ∧
      (∀ key, sptDomain mapOut key → sptDomain after.locals (optionLookup mapOut key)) := by
  rcases h with ⟨frame,related,valid,allocated,setup⟩
  let keys := (sptToAList (sptUnion names exitNames)).map Prod.fst
  let extend := keys.filter fun key => (sptLookup key ssa).isNone
  let refresh := keys.filter fun key => (sptLookup key ssa).isSome
  have keysDistinct : keys.Nodup := sptAllDistinctMapFstToAList _
  have extendDistinct : extend.Nodup := keysDistinct.filter _
  have refreshDistinct : refresh.Nodup := keysDistinct.filter _
  have missing : ∀ key ∈ extend, sptLookup key ssa = none := by
    intro key member
    simpa [extend,List.mem_filter] using (List.mem_filter.mp member).2
  have partitionDistinct : (extend ++ refresh).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨extendDistinct,refreshDistinct,?_⟩
    intro x inExtend y inRefresh equal
    subst y
    have absent := missing x inExtend
    simp [refresh,absent] at inRefresh
  have partition : ∀ key, key ∈ extend ++ refresh ↔ sptDomain (sptUnion names exitNames) key := by
    intro key
    cases read : sptLookup key ssa <;>
      simpa [extend,refresh,read,keys] using (sptMemMapFstToAList (sptUnion names exitNames) key)
  simp only [loopSetup] at setup
  generalize firstProduced : listNextVarRename extend ssa next = firstResult at setup
  rcases firstResult with ⟨fresh,middle,middleNext⟩
  simp only [listNextVarRenameMove] at setup
  generalize secondProduced : listNextVarRename refresh middle middleNext = secondResult at setup
  rcases secondResult with ⟨refreshed,finalMap,finalNext⟩
  simp only [Prod.mk.injEq] at setup
  rcases setup with ⟨rfl,rfl,rfl⟩
  have firstProps := listNextVarRenameProps extend ssa next fresh middle middleNext firstProduced
    ⟨Or.inl allocated,valid⟩
  have secondProps := listNextVarRenameProps refresh middle middleNext refreshed finalMap finalNext secondProduced
    ⟨Or.inl (firstProps.2.1 allocated),firstProps.2.2.2⟩
  have firstLookup := listNextVarRenameLemma2Prime extend ssa next fresh middle middleNext firstProduced extendDistinct
  have secondLookup := listNextVarRenameLemma2Prime refresh middle middleNext refreshed finalMap finalNext secondProduced refreshDistinct
  let fakeState := {target with locals := fresh.foldr (fun key locals => sptInsert key (.word 0) locals) target.locals}
  have fakeRun : WordSemStateFiniteExact.evaluate ((fresh.map (fakeMove (width := width))).foldr .seq .skip) target =
      (none,fakeState) := evaluateFakeConstChain fresh target
  have fakeFrame : Flapjack.WordAlloc.wordStateEqRel source fakeState := by
    simpa [fakeState,Flapjack.WordAlloc.wordStateEqRel] using frame
  have fakeLocals : ssaLocalsRel middleNext middle source.locals fakeState.locals :=
    extendedLocals extend ssa next source.locals target.locals fresh middle middleNext
      firstProduced extendDistinct missing valid related
  have refreshPresent : ∀ key ∈ refresh, sptDomain middle key := by
    intro key member
    rw [firstLookup.2.1]
    apply Or.inl
    cases read : sptLookup key ssa with
    | none => simp [refresh,read] at member
    | some value => exact (sptMem_iff_lookup key ssa).mpr ⟨value,read⟩
  have moveRun := listNextVarRenameMovePreserveWeak source middle middleNext refresh fakeState
    ⟨fakeLocals,refreshPresent,refreshDistinct,firstProps.2.2.2,fakeFrame⟩
  simp only [listNextVarRenameMove,secondProduced] at moveRun
  generalize evaluated : WordSemStateFiniteExact.evaluate
    (.move 0 (refreshed.zip (refresh.map (optionLookup middle)))) fakeState = result at moveRun
  rcases result with ⟨returned,after⟩
  dsimp only at moveRun
  rcases moveRun with ⟨rfl,afterLocals,afterFrame⟩
  have injection := renameStagesInjective extend refresh ssa next fresh refreshed middle finalMap
    middleNext finalNext firstProduced secondProduced partitionDistinct
  refine ⟨after,?_,afterFrame,afterLocals,Nat.le_trans firstProps.1 secondProps.1,
    secondProps.2.1 (firstProps.2.1 allocated),secondProps.2.2.2,?_,?_,?_,?_⟩
  · rw [evaluateSeqCollapse _ _ _ _ fakeRun]
    exact evaluated
  · rw [secondLookup.2.1,firstLookup.2.1]
    funext key
    apply propext
    have member := partition key
    simp only [List.mem_append] at member
    tauto
  · intro x y inX inY equal
    apply injection x ((partition x).mpr ?_) y ((partition y).mpr ?_) equal
    · rw [sptDomain_sptUnion]
      exact Or.inl inX
    · rw [sptDomain_sptUnion]
      exact Or.inl inY
  · intro x y inX inY equal
    apply injection x ((partition x).mpr ?_) y ((partition y).mpr ?_) equal
    · rw [sptDomain_sptUnion]
      exact Or.inr inX
    · rw [sptDomain_sptUnion]
      exact Or.inr inY
  · intro key member
    obtain ⟨register,read⟩ := (sptMem_iff_lookup key finalMap).mp member
    simpa [optionLookup,read,sptMem] using afterLocals.1 key register read

end Flapjack.Compiler.Backend.WordAlloc
