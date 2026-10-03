import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.StackRemove.Proofs.ProgCompEta
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.Install
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps
/-- Flapjack-only first-match lookup transport for Install; no independent HOL declaration. -/
theorem compiledEntriesLookup {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer name : Nat)
    (entries : List (Nat × HolProg width)) :
    sptAListLookup name (entries.map (progComp jump bounds pointer)) =
      (sptAListLookup name entries).map (comp jump bounds pointer) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨other, program⟩
    by_cases same : name = other <;>
      simp [sptAListLookup, progComp, same, ih]

/-- Flapjack-only domain transport for Install, including duplicate names; no independent HOL declaration. -/
theorem compiledEntriesDomain {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (entries : List (Nat × HolProg width)) :
    sptDomain (sptFromAList (entries.map (progComp jump bounds pointer))) =
      sptDomain (sptFromAList entries) := by
  funext name
  simp only [sptDomain, sptLookup_sptFromAList, compiledEntriesLookup, Option.isSome_map]

/-- Original Install code-relation transition, derived from actual oracle
entry bounds. New code retains first-match lookup and cannot shadow stubs.
Flapjack-only transition factoring; no independent HOL declaration. -/
theorem codeRelInstall {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : Spt (HolProg width)) (entries : List (Nat × HolProg width))
    (relation : codeRelHOL jump bounds pointer source target)
    (entryBounds : ∀ name program, (name, program) ∈ entries →
      StackProps.regBound program pointer ∧ stackNumStubs ≤ name + 1) :
    codeRelHOL jump bounds pointer
      (sptUnion source (sptFromAList entries))
      (sptUnion target (sptFromAList (entries.map (progComp jump bounds pointer)))) := by
  rcases relation with ⟨lookupRel, domainRel⟩
  constructor
  · intro name program lookup
    rw [sptLookup_sptUnion] at lookup
    cases old : sptLookup name source with
    | some oldProgram =>
      simp only [old] at lookup
      cases Option.some.inj lookup
      obtain ⟨bound, compiled⟩ := lookupRel name program old
      exact ⟨bound, by rw [sptLookup_sptUnion, compiled]⟩
    | none =>
      simp only [old, sptLookup_sptFromAList] at lookup
      obtain ⟨bound, fresh⟩ := entryBounds name program
        (sptAListLookup_mem name entries program lookup)
      have targetOld : sptLookup name target = none := by
        cases found : sptLookup name target with
        | none => rfl
        | some value =>
          have member : sptDomain target name := by simp [sptDomain, found]
          rw [domainRel] at member
          simp only [sptDomain, old, Option.isSome_none, Bool.false_eq_true, false_or] at member
          simp only [stackNumStubs] at fresh
          omega
      refine ⟨bound, ?_⟩
      rw [sptLookup_sptUnion, targetOld, sptLookup_sptFromAList,
        compiledEntriesLookup, lookup]
      rfl
  · rw [sptDomain_sptUnion, sptDomain_sptUnion, compiledEntriesDomain, domainRel]
    funext name
    apply propext
    tauto
/-- Flapjack-only factoring of the successful Install record update; no independent HOL declaration. -/
def installedState {width : Nat} [NeZero width] {C F : Type}
    (register entry : Nat) (programs : List (Nat × HolProg width))
    (bitmaps : List (BitVec width)) (codeBuffer : WordSemBuffer width 8)
    (dataBuffer : WordSemBuffer width width)
    (state : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  {state with bitmaps := state.bitmaps ++ bitmaps, codeBuffer := codeBuffer, dataBuffer := dataBuffer, code := sptUnion state.code (sptFromAList programs), regs := (StackSemStateOps.restrictIn state.regs state.ffiSaveRegs).updateEq (register, .loc entry 0), fpRegs := HolFiniteMapExact.empty, compileOracle := holShiftSeq 1 state.compileOracle}

/-- Original Install post-relation, derived from the actual successful data
flush and oracle entry bounds. This local transition is infrastructure for
assembling the full constructor case, not an additional HOL declaration. -/
theorem stateRelInstall {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register entry : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (programs : List (Nat × HolProg width)) (bitmaps : List (BitVec width))
    (codeBuffer : WordSemBuffer width 8) (dataBuffer : WordSemBuffer width width)
    (dataStart dataEnd : BitVec width)
    (relation : stateRelHOL jump bounds pointer source target)
    (registerBound : register < pointer)
    (programsEq : programs = (source.compileOracle 0).2.1)
    (flush : wordSemBufferFlush source.dataBuffer dataStart dataEnd = some (bitmaps, dataBuffer)) :
    stateRelHOL jump bounds pointer
      (installedState register entry programs bitmaps codeBuffer dataBuffer source)
      (installedState register entry (programs.map (progComp jump bounds pointer))
        bitmaps codeBuffer target.dataBuffer target) := by
  have entryBounds : ∀ name program, (name, program) ∈ programs →
      StackProps.regBound program pointer ∧ stackNumStubs ≤ name + 1 := by
    intro name program member
    exact relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 name program
      (by simpa [programsEq] using member)
  have codeRelation := codeRelInstall jump bounds pointer source.code target.code programs
    relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 entryBounds
  unfold wordSemBufferFlush at flush
  split at flush
  next condition =>
    cases Option.some.inj flush
    simp only [stateRelHOL, installedState] at relation ⊢
    rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
    refine ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,True.intro,True.intro,h13,h14,?_,?_,h17,?_,codeRelation,?_,?_,h22,h23,h24,?_⟩
    · funext index
      simpa only [holShiftSeq] using congrFun h15 (index + 1)
    · intro index name program member
      exact h16 (index + 1) name program member
    · intro query queryBound
      simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        StackSemStateOps.restrictIn_lookup, h10]
      by_cases same : query = register
      · simp [same]
      · simp only [same, if_false]
        rw [h18 query queryBound]
    · rw [sptLookup_sptUnion, h20]
    · have different : pointer + 2 ≠ register := by omega
      simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different, if_false,
        StackSemStateOps.restrictIn_lookup, h22 (pointer + 2) (by simp), if_true, h21]
    · have position : dataEnd = source.dataBuffer.position +
          bytesInWord width * BitVec.ofNat width source.dataBuffer.buffer.length := by
        simpa only [bytesInWord] using condition.2.symm
      simp only [List.append_nil, List.length_append]
      rw [position]
      rcases h25 with ⟨oldPosition, heap⟩
      refine ⟨?_, ?_⟩
      · rw [oldPosition]
        simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
      · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          StackSemStateOps.restrictIn_lookup]
        have different : pointer + 1 ≠ register := by omega
        have saved := h22 (pointer + 1) (by simp)
        simp only [different, if_false, saved, if_true]
        have pointerDifferent : pointer ≠ register := by omega
        have pointerSaved := h22 pointer (by simp)
        simpa only [pointerDifferent, if_false, pointerSaved, if_true, List.length_append] using heap
  next => cases flush

/-- Canonical codec of the actual imported evaluator state. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Install constructor case (1932–1997). Retains all five
constructor registers and the original four premises. The native target
execution, compiler/oracle transport, code-union/stub facts, register
restriction and entire post-relation are derived. No target execution,
successful compilation, code relation or desired post-state is assumed.
The evaluator closure inherits the reviewed reals_as_rational_cuts FP
carrier (SOUNDNESS item 8); this constructor executes no FP instruction. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (first second third fourth fifth : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.install first second third fourth fifth, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.install first second third fourth fifth : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.install first second third fourth fifth),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer ∧ third < pointer ∧ fourth < pointer ∧ fifth < pointer at bound
  have firstRead := (RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩).symm
  have secondRead := (RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2.1⟩).symm
  have thirdRead := (RelationLaws.stateRelGetVar jump bounds pointer third source target ⟨relation, bound.2.2.1⟩).symm
  have fourthRead := (RelationLaws.stateRelGetVar jump bounds pointer fourth source target ⟨relation, bound.2.2.2.1⟩).symm
  rw [evaluate_install] at sourceRun
  split at sourceRun
  next _ _ _ _ w1 w2 w3 w4 lookup1 lookup2 lookup3 lookup4 =>
    rcases oracle : source.compileOracle 0 with ⟨cfg, programs, bitmaps⟩
    simp only [oracle, if_pos relation.1] at sourceRun
    split at sourceRun
    next _ _ bytes codeBuffer data dataBuffer codeFlush dataFlush =>
      split at sourceRun
      next _ _ _ compiledBytes nextConfig entry program rest compileRun =>
        split at sourceRun
        next condition =>
          have dataEq : data = bitmaps := by simpa only [oracle] using condition.2.1
          rw [dataEq] at dataFlush
          have programsEq : (entry, program) :: rest = (source.compileOracle 0).2.1 := by
            rw [oracle]
          have compileTransport := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have oracleTransport := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have targetCompile : target.compile cfg
              (((entry, program) :: rest).map (progComp jump bounds pointer)) =
              some (compiledBytes, nextConfig) :=
            (congrFun (congrFun compileTransport cfg) ((entry, program) :: rest)).symm.trans compileRun
          have targetCompileCons := targetCompile
          simp only [List.map_cons, progComp] at targetCompileCons
          have targetOracle : target.compileOracle 0 =
              (cfg, (((entry, program) :: rest).map (progComp jump bounds pointer)), bitmaps) := by
            rw [oracleTransport]
            simp only [oracle]
          have nextConfigEq : (holShiftSeq 1 target.compileOracle 0).1 = nextConfig := by
            simpa only [holShiftSeq, oracleTransport] using condition.2.2
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          refine ⟨0, installedState first entry
            (((entry, program) :: rest).map (progComp jump bounds pointer)) bitmaps
            codeBuffer target.dataBuffer target, ?_, ?_⟩
          · simpa only [comp, Nat.zero_add] using
              (evaluate_install first second third fourth fifth target).trans (by
                simp only [firstRead, secondRead, thirdRead, fourthRead,
                  lookup1, lookup2, lookup3, lookup4, targetOracle,
                  relation.2.2.1, Bool.false_eq_true, if_false,
                  relation.2.2.2.2.2.2.2.2.2.2.2.2.1, codeFlush,
                  targetCompileCons, List.map_cons, progComp, condition.1, nextConfigEq,
                  and_self, if_true, installedState])
          · exact stateRelInstall jump bounds pointer first entry source target
              ((entry, program) :: rest) bitmaps codeBuffer dataBuffer w3 w4
              relation bound.1 programsEq dataFlush
        next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
end Flapjack.Compiler.Backend.StackRemove.CompCorrect.Install
