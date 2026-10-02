import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSACutEnvsDomain
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMoveDistinct
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMovePreserve
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenamePropertyWrappers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalStateUpdates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvLemma
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterFlip
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq

namespace Flapjack.Compiler.Backend.WordAlloc

-- Flapjack factoring of the original FFI case's inline cut-map argument;
-- these derived intermediate premises are not public simulation premises.
private theorem cutLocalsRelation {α : Type} (next : Nat) (ssa : Spt Nat)
    (names : Spt Unit) (source target : Spt α)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (sourceDomain : sptDomain source = sptDomain names)
    (matching : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source target)
    (below : ∀ key, sptDomain names key → key < next) :
    ssaLocalsRel next (sptInter ssa names) source target := by
  have interRead : ∀ key register, sptLookup key (sptInter ssa names) = some register →
      sptLookup key ssa = some register ∧ sptDomain names key := by
    intro key register read
    rw [sptLookup_sptInterCases] at read
    cases left : sptLookup key ssa with
    | none => simp [left] at read
    | some value =>
      cases right : sptLookup key names with
      | none => simp [left,right] at read
      | some payload =>
        have equal : value = register := by simpa [left,right] using read
        subst value
        exact ⟨rfl,(sptMem_iff_lookup key names).mpr ⟨payload,right⟩⟩
  refine ⟨?_,?_⟩
  · intro key register read
    obtain ⟨original,inNames⟩ := interRead key register read
    have inSource : sptDomain source key := by rw [sourceDomain]; exact inNames
    obtain ⟨value,sourceRead⟩ := (sptMem_iff_lookup key source).mp inSource
    have targetRead := matching key value ⟨inNames,sourceRead⟩
    apply (sptMem_iff_lookup register target).mpr
    exact ⟨value,by simpa [optionLookup,original] using targetRead⟩
  · intro key value read
    have inNames : sptDomain names key := by
      rw [←sourceDomain]
      exact (sptMem_iff_lookup key source).mpr ⟨value,read⟩
    obtain ⟨register,original⟩ := (sptMem_iff_lookup key ssa).mp (mapped key inNames)
    obtain ⟨payload,nameRead⟩ := (sptMem_iff_lookup key names).mp inNames
    have interLookup : sptLookup key (sptInter ssa names) = some register := by
      simp [sptLookup_sptInterCases,original,nameRead]
    refine ⟨(sptMem_iff_lookup key _).mpr ⟨register,interLookup⟩,?_,fun _ => below key inNames⟩
    simpa only [interLookup,Option.getD_some,optionLookup,original] using
      matching key value ⟨inNames,read⟩

-- The source cut guards supply exactly the names read by the first refresh.
private theorem cutNamesPresent {α : Type} (first second : Spt Unit)
    (source output : Spt α)
    (cut : wordSemCutEnv (first,second) source = some output) :
    ∀ key, sptDomain (sptUnion first second) key → sptDomain source key := by
  cases cuts : wordSemCutEnvs (first,second) source with
  | none => simp [wordSemCutEnv,cuts] at cut
  | some pair =>
    have present := cutEnvsDomainSubset first second source pair cuts
    intro key member
    rw [sptDomain_sptUnion] at member
    exact member.elim (present.1 key) (present.2 key)

-- A successful source lookup discharges the guarded SSA selector before
-- applying the scoped relation required by the original cut_env_lemma.
private theorem scopedLocalsRelation {α : Type} (next : Nat) (ssa : Spt Nat)
    (names : Nat → Prop) (source target : Spt α)
    (related : ssaLocalsRel next ssa source target) :
    Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa) names source target := by
  intro key value found
  have matching := related.2 key value found.2
  obtain ⟨register,read⟩ := (sptMem_iff_lookup key ssa).mp matching.1
  simpa [optionLookup,read] using matching.2.1

-- Injection is only needed on the cut names, not over the entire SSA map.
private theorem cutNamesInjection {width : Nat} [NeZero width]
    (ssa : Spt Nat) (next : Nat) (first second : Spt Unit)
    (move : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : listNextVarRenameMove ssa next
      ((sptToAList (sptUnion first second)).map Prod.fst) = (move,ssaOut,nextOut)) :
    ∀ x y, (sptDomain first x ∨ sptDomain second x) →
      (sptDomain first y ∨ sptDomain second y) →
      optionLookup ssaOut x = optionLookup ssaOut y → x = y := by
  intro x y inX inY equal
  apply listNextVarRenameMoveDistinct ssa next _ move ssaOut nextOut x y
  refine ⟨produced,sptAllDistinctMapFstToAList _,?_,?_,equal⟩
  · apply (sptMemMapFstToAList _ x).mpr
    rw [sptDomain_sptUnion]
    exact inX
  · apply (sptMemMapFstToAList _ y).mpr
    rw [sptDomain_sptUnion]
    exact inY

-- Execute the actual first renaming Move from the original source cut guards.
-- This is private case factoring; its successful cut premise will be obtained
-- by the public evaluator case split, rather than added to the HOL statement.
private theorem refreshCutNames {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (first second : Spt Unit)
    (sourceEnv : Spt (WordLocW width))
    (cut : wordSemCutEnv (first,second) source.locals = some sourceEnv)
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (valid : ssaMapOK next ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move,mapOut,counter) := listNextVarRenameMove (width := width) ssa (next+2)
      ((sptToAList (sptUnion first second)).map Prod.fst)
    let (result,targetOut) := WordSemStateFiniteExact.evaluate move target
    result = none ∧ ssaLocalsRel counter mapOut source.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source targetOut := by
  have present := cutNamesPresent first second source.locals sourceEnv cut
  have result := listNextVarRenameMovePreserve source ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) target
    ⟨ssaLocalsRelMore next ssa source.locals target.locals (next+2) ⟨related,by omega⟩,
      (fun key member => present key ((sptMemMapFstToAList _ key).mp member)),
      sptAllDistinctMapFstToAList _,
      ssaMapOKMore next ssa (next+2) ⟨valid,by omega⟩,frame⟩
  generalize produced : listNextVarRenameMove (width := width) ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) = output at result ⊢
  rcases output with ⟨move,mapOut,counter⟩
  generalize evaluated : WordSemStateFiniteExact.evaluate move target = run at result ⊢
  rcases run with ⟨resultOut,targetOut⟩
  exact ⟨result.1,result.2.1,result.2.2.1⟩

-- Combine the original cut_env_lemma with refreshed-map injection. Physical
-- scratch writes are handled before this lemma through the checked update law.
private theorem refreshedCut {width : Nat} [NeZero width]
    (ssa : Spt Nat) (next : Nat) (first second : Spt Unit)
    (move : WordLangProgHOL (BitVec width)) (mapOut : Spt Nat) (counter : Nat)
    (source target sourceEnv : Spt (WordLocW width))
    (produced : listNextVarRenameMove ssa next
      ((sptToAList (sptUnion first second)).map Prod.fst) = (move,mapOut,counter))
    (cut : wordSemCutEnv (first,second) source = some sourceEnv)
    (related : ssaLocalsRel counter mapOut source target) :
    ∃ targetEnv,
      wordSemCutEnv (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) (first,second)) target =
        some targetEnv ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut)
        (sptDomain (sptUnion first second)) sourceEnv targetEnv ∧
      sptDomain sourceEnv = sptDomain (sptUnion first second) := by
  obtain ⟨targetEnv,targetCut,_,matching,_,sourceDomain⟩ :=
    Flapjack.WordAlloc.cutEnvLemma first second source target sourceEnv (optionLookup mapOut)
      ⟨cutNamesInjection ssa next first second move mapOut counter produced,cut,
        scopedLocalsRelation counter mapOut _ source target related⟩
  refine ⟨targetEnv,targetCut,?_,?_⟩
  · simpa only [sptDomain_sptUnion] using matching
  · simpa only [sptDomain_sptUnion] using sourceDomain

-- Execute the actual final Move after a returning FFI. Its source domain,
-- value correspondence and bounds are facts derived before/through the cut.
private theorem restoreCutNames {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (counter : Nat) (names : Spt Unit)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (matching : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source.locals target.locals)
    (below : ∀ key, sptDomain names key → key < counter)
    (valid : ssaMapOK counter ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move,mapOut,nextOut) := listNextVarRenameMove (width := width)
      (sptInter ssa names) (counter+2) ((sptToAList names).map Prod.fst)
    let (result,targetOut) := WordSemStateFiniteExact.evaluate move target
    result = none ∧ ssaLocalsRel nextOut mapOut source.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source targetOut := by
  have related := cutLocalsRelation counter ssa names source.locals target.locals
    mapped sourceDomain matching below
  have result := listNextVarRenameMovePreserve source (sptInter ssa names) (counter+2)
    ((sptToAList names).map Prod.fst) target
    ⟨ssaLocalsRelMore counter _ source.locals target.locals (counter+2) ⟨related,by omega⟩,
      (fun key member => by rw [sourceDomain]; exact (sptMemMapFstToAList _ key).mp member),
      sptAllDistinctMapFstToAList _,
      ssaMapOKMore counter _ (counter+2) ⟨ssaMapOKInter counter ssa names valid,by omega⟩,
      frame⟩
  generalize produced : listNextVarRenameMove (width := width)
    (sptInter ssa names) (counter+2) ((sptToAList names).map Prod.fst) = output at result ⊢
  rcases output with ⟨move,mapOut,nextOut⟩
  generalize evaluated : WordSemStateFiniteExact.evaluate move target = run at result ⊢
  rcases run with ⟨resultOut,targetOut⟩
  exact ⟨result.1,result.2.1,result.2.2.1⟩

-- Actual four-register scratch Move. Successful source input reads are local
-- branch facts; each target read follows from the current SSA locals relation.
private theorem ffiScratchMove {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next ptr1 len1 ptr2 len2 : Nat)
    (pointer1 length1 pointer2 length2 : BitVec width)
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (valid : ssaMapOK next ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (readPtr1 : WordSemStateFiniteExact.getVar ptr1 source = some (.word pointer1))
    (readLen1 : WordSemStateFiniteExact.getVar len1 source = some (.word length1))
    (readPtr2 : WordSemStateFiniteExact.getVar ptr2 source = some (.word pointer2))
    (readLen2 : WordSemStateFiniteExact.getVar len2 source = some (.word length2)) :
    let scratch := WordSemStateFiniteExact.setVars [2,4,6,8]
      [.word pointer1,.word length1,.word pointer2,.word length2] target
    WordSemStateFiniteExact.evaluate
      (.move 1 [(2,optionLookup ssa ptr1),(4,optionLookup ssa len1),
        (6,optionLookup ssa ptr2),(8,optionLookup ssa len2)]) target = (none,scratch) ∧
      ssaLocalsRel next ssa source.locals scratch.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source scratch := by
  have targetPtr1 := ssaLocalsRelGetVar next ssa source target ptr1 (.word pointer1)
    ⟨related,readPtr1⟩
  have targetLen1 := ssaLocalsRelGetVar next ssa source target len1 (.word length1)
    ⟨related,readLen1⟩
  have targetPtr2 := ssaLocalsRelGetVar next ssa source target ptr2 (.word pointer2)
    ⟨related,readPtr2⟩
  have targetLen2 := ssaLocalsRelGetVar next ssa source target len2 (.word length2)
    ⟨related,readLen2⟩
  refine ⟨?_,?_,?_⟩
  · simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVars,
      targetPtr1,targetLen1,targetPtr2,targetLen2]
  · exact ssaLocalsPhysicalListUpdate next ssa source.locals target.locals
      [2,4,6,8] [.word pointer1,.word length1,.word pointer2,.word length2]
      valid related (by simp [isPhyVar])
  · exact frame

private theorem evaluateSeqFFI {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq first second) state =
      match WordSemStateFiniteExact.evaluate first state with
      | (none,after) => WordSemStateFiniteExact.evaluate second after
      | (some result,after) => (some result,after) := by
  simp only [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.fix_clock_evaluate]
  cases WordSemStateFiniteExact.evaluate first state with
  | mk result after => cases result <;> rfl

-- Internal successful-read/cut/bytearray branch. These premises are discharged
-- by source evaluator case splits in the full public six-premise theorem.
private theorem ffiSuccessfulBranch {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next ptr1 len1 ptr2 len2 : Nat)
    (function : Flapjack.Basis.Pure.MlString.MlString) (first second : Spt Unit)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (pointer1 length1 pointer2 length2 : BitVec width)
    (sourceEnv : Spt (WordLocW width)) (bytes1 bytes2 : List (BitVec 8))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (allocated : isAllocVar next) (valid : ssaMapOK next ssa)
    (namesBelow : ∀ key, sptDomain (sptUnion first second) key → key < next)
    (readPtr1 : WordSemStateFiniteExact.getVar ptr1 source = some (.word pointer1))
    (readLen1 : WordSemStateFiniteExact.getVar len1 source = some (.word length1))
    (readPtr2 : WordSemStateFiniteExact.getVar ptr2 source = some (.word pointer2))
    (readLen2 : WordSemStateFiniteExact.getVar len2 source = some (.word length2))
    (cut : wordSemCutEnv (first,second) source.locals = some sourceEnv)
    (readBytes1 : readBytearrayWordHOL pointer1 length1.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) = some bytes1)
    (readBytes2 : readBytearrayWordHOL pointer2 length2.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) = some bytes2) :
    ssaSimulation (.ffi function ptr1 len1 ptr2 len2 (first,second))
      source target ssa next tables := by
  have refreshed := refreshCutNames source target ssa next first second sourceEnv
    cut related valid frame
  generalize produced : listNextVarRenameMove (width := width) ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) = output at refreshed
  rcases output with ⟨move,mapOut,counter⟩
  dsimp only at refreshed
  generalize refreshRun : WordSemStateFiniteExact.evaluate move target = run at refreshed
  rcases run with ⟨result,refreshedState⟩
  dsimp only at refreshed
  rcases refreshed with ⟨rfl,refreshedLocals,refreshedFrame⟩
  have properties := listNextVarRenameMoveProps _ ssa (next+2) move mapOut counter produced
    ⟨Or.inr (isAllocVarFlip next allocated),ssaMapOKMore next ssa (next+2) ⟨valid,by omega⟩⟩
  let scratch := WordSemStateFiniteExact.setVars [2,4,6,8]
    [.word pointer1,.word length1,.word pointer2,.word length2] refreshedState
  have scratchFacts := ffiScratchMove source refreshedState mapOut counter ptr1 len1 ptr2 len2
    pointer1 length1 pointer2 length2 refreshedLocals properties.2.2.2 refreshedFrame
    readPtr1 readLen1 readPtr2 readLen2
  change WordSemStateFiniteExact.evaluate _ refreshedState = (none,scratch) ∧
    ssaLocalsRel counter mapOut source.locals scratch.locals ∧
    Flapjack.WordAlloc.wordStateEqRel source scratch at scratchFacts
  obtain ⟨targetEnv,targetCut,cutMatching,sourceDomain⟩ :=
    refreshedCut ssa (next+2) first second move mapOut counter source.locals scratch.locals
      sourceEnv produced cut scratchFacts.2.1
  have sameMemory : scratch.memory = source.memory := scratchFacts.2.2.2.2.2.2.2.2.2.1
  have sameDomain : scratch.mdomain = source.mdomain := scratchFacts.2.2.2.2.2.2.2.2.2.2.1
  have sameEndian : scratch.be = source.be := scratchFacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sameFFI : scratch.ffi = source.ffi := scratchFacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have targetBytes1 : readBytearrayWordHOL pointer1 length1.toNat
      (memLoadByteAuxExact scratch.memory scratch.mdomain scratch.be) = some bytes1 := by
    simpa only [sameMemory,sameDomain,sameEndian] using readBytes1
  have targetBytes2 : readBytearrayWordHOL pointer2 length2.toNat
      (memLoadByteAuxExact scratch.memory scratch.mdomain scratch.be) = some bytes2 := by
    simpa only [sameMemory,sameDomain,sameEndian] using readBytes2
  have scratchPtr1 : WordSemStateFiniteExact.getVar 2 scratch = some (.word pointer1) := by
    simp [WordSemStateFiniteExact.getVar,scratch,WordSemStateFiniteExact.setVars,
      LoopSemStateFiniteExact.sptAlistInsert,sptLookup_sptInsert]
  have scratchLen1 : WordSemStateFiniteExact.getVar 4 scratch = some (.word length1) := by
    simp [WordSemStateFiniteExact.getVar,scratch,WordSemStateFiniteExact.setVars,
      LoopSemStateFiniteExact.sptAlistInsert,sptLookup_sptInsert]
  have scratchPtr2 : WordSemStateFiniteExact.getVar 6 scratch = some (.word pointer2) := by
    simp [WordSemStateFiniteExact.getVar,scratch,WordSemStateFiniteExact.setVars,
      LoopSemStateFiniteExact.sptAlistInsert,sptLookup_sptInsert]
  have scratchLen2 : WordSemStateFiniteExact.getVar 8 scratch = some (.word length2) := by
    simp [WordSemStateFiniteExact.getVar,scratch,WordSemStateFiniteExact.setVars,
      LoopSemStateFiniteExact.sptAlistInsert,sptLookup_sptInsert]
  refine ⟨target.permute,?_⟩
  cases called : callFFIHOL source.ffi (.extCall function) bytes1 bytes2 with
  | final outcome =>
    have ffiRun : WordSemStateFiniteExact.evaluate
        (.ffi function 2 4 6 8 (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut)
          (first,second))) scratch = (some (.finalFfi outcome),
          WordSemStateFiniteExact.flushState true scratch) := by
      simp only [WordSemStateFiniteExact.evaluate,scratchLen1,scratchPtr1,scratchLen2,
        scratchPtr2,targetCut,targetBytes1,targetBytes2,sameFFI,called]
    have compiledRun : WordSemStateFiniteExact.evaluate
        (ssaCcTrans (.ffi function ptr1 len1 ptr2 len2 (first,second)) ssa next tables).1 target =
        (some (.finalFfi outcome),WordSemStateFiniteExact.flushState true scratch) := by
      simp only [ssaCcTrans,produced]
      rw [evaluateSeqFFI,refreshRun]
      dsimp only
      rw [evaluateSeqFFI,scratchFacts.1]
      dsimp only
      rw [evaluateSeqFFI,ffiRun]
    simp only [WordSemStateFiniteExact.getVar] at readPtr1 readLen1 readPtr2 readLen2
    have sourceRun : WordSemStateFiniteExact.evaluate
        (.ffi function ptr1 len1 ptr2 len2 (first,second))
        {source with permute := target.permute} =
        (some (.finalFfi outcome),WordSemStateFiniteExact.flushState true
          {source with permute := target.permute}) := by
      simp only [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,
        readPtr1,readLen1,readPtr2,readLen2,cut,readBytes1,readBytes2,called]
    dsimp only
    rw [sourceRun,compiledRun]
    have finalFrame := scratchFacts.2.2
    simp_all [WordSemStateFiniteExact.flushState,Flapjack.WordAlloc.wordStateEqRel]
  | ret newFfi newBytes =>
    let memory := writeBytearrayExact pointer2 newBytes source.memory source.mdomain source.be
    let sourceAfter := {source with memory := memory,locals := sourceEnv,fpRegs := HolFiniteMapExact.empty,ffi := newFfi}
    let targetAfter := {scratch with memory := memory,locals := targetEnv,fpRegs := HolFiniteMapExact.empty,ffi := newFfi}
    have afterFrame : Flapjack.WordAlloc.wordStateEqRel sourceAfter targetAfter := by
      have preserved := scratchFacts.2.2
      simp_all [sourceAfter,targetAfter,Flapjack.WordAlloc.wordStateEqRel]
    have mapped : ∀ key, sptDomain (sptUnion first second) key → sptDomain mapOut key := by
      intro key member
      obtain ⟨value,read⟩ := (sptMem_iff_lookup key source.locals).mp
        (cutNamesPresent first second source.locals sourceEnv cut key member)
      exact (refreshedLocals.2 key value read).1
    have restored := restoreCutNames sourceAfter targetAfter mapOut counter (sptUnion first second)
      mapped sourceDomain cutMatching
      (fun key member => by have := namesBelow key member; have := properties.1; omega)
      properties.2.2.2 afterFrame
    generalize returned : listNextVarRenameMove (width := width)
      (sptInter mapOut (sptUnion first second)) (counter+2)
      ((sptToAList (sptUnion first second)).map Prod.fst) = finalOutput at restored
    rcases finalOutput with ⟨retMove,finalMap,finalCounter⟩
    dsimp only at restored
    generalize restoreRun : WordSemStateFiniteExact.evaluate retMove targetAfter = finalRun at restored
    rcases finalRun with ⟨retResult,finished⟩
    dsimp only at restored
    rcases restored with ⟨rfl,finishedLocals,finishedFrame⟩
    have ffiRun : WordSemStateFiniteExact.evaluate
        (.ffi function 2 4 6 8 (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut)
          (first,second))) scratch = (none,targetAfter) := by
      simp only [WordSemStateFiniteExact.evaluate,scratchLen1,scratchPtr1,scratchLen2,
        scratchPtr2,targetCut,targetBytes1,targetBytes2,sameFFI,called]
      simp only [targetAfter,memory,sameMemory,sameDomain,sameEndian]
    have compiledRun : WordSemStateFiniteExact.evaluate
        (ssaCcTrans (.ffi function ptr1 len1 ptr2 len2 (first,second)) ssa next tables).1 target =
        (none,finished) := by
      simp only [ssaCcTrans,produced,returned]
      rw [evaluateSeqFFI,refreshRun]
      dsimp only
      rw [evaluateSeqFFI,scratchFacts.1]
      dsimp only
      rw [evaluateSeqFFI,ffiRun]
      exact restoreRun
    simp only [WordSemStateFiniteExact.getVar] at readPtr1 readLen1 readPtr2 readLen2
    have sourceRun : WordSemStateFiniteExact.evaluate
        (.ffi function ptr1 len1 ptr2 len2 (first,second))
        {source with permute := target.permute} =
        (none,{sourceAfter with permute := target.permute}) := by
      simp only [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,
        readPtr1,readLen1,readPtr2,readLen2,cut,readBytes1,readBytes2,called,sourceAfter,memory]
    dsimp only
    rw [sourceRun,compiledRun]
    simp only [reduceCtorEq,if_false,ssaCcTrans,produced,returned]
    exact ⟨True.intro,finishedFrame,finishedLocals⟩

namespace SemanticFFIWitnesses

/-- Canonical roundtrip of the imported native finite-map state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticFFIWitnesses

/-- Full original FFI SSA case. The source evaluator supplies each successful
read, cut and bytearray branch; target execution is derived through the two
actual renaming Moves, physical scratch Move and shared FFI operation. All six
original premises and the full Error-exempt permutation/result/frame/locals
conclusion remain. Inherits the evaluator real-rendering boundary of
SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectFFI {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next ptr1 len1 ptr2 len2 : Nat)
    (function : Flapjack.Basis.Pure.MlString.MlString) (first second : Spt Unit)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun key => decide (key < next))
        (.ffi function ptr1 len1 ptr2 len2 (first,second)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.ffi function ptr1 len1 ptr2 len2 (first,second))
      source target ssa next tables := by
  have namesChecked : everyNameHOL (fun key => decide (key < next)) (first,second) = true := by
    have checked := h.2.2.2.1
    simp only [everyVarHOL,Bool.and_eq_true] at checked
    exact checked.2
  have cutBounds : (∀ key ∈ (sptToAList first).map Prod.fst, key < next) ∧
      (∀ key ∈ (sptToAList second).map Prod.fst, key < next) := by
    simpa [everyNameHOL,List.all_eq_true] using namesChecked
  have namesBelow : ∀ key, sptDomain (sptUnion first second) key → key < next := by
    intro key member
    rw [sptDomain_sptUnion] at member
    exact member.elim
      (fun member => cutBounds.1 key ((sptMemMapFstToAList first key).mpr member))
      (fun member => cutBounds.2 key ((sptMemMapFstToAList second key).mpr member))
  cases len1Read : WordSemStateFiniteExact.getVar len1 source with
  | none =>
    simp only [WordSemStateFiniteExact.getVar] at len1Read
    refine ⟨target.permute,?_⟩
    simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read]
  | some len1Value =>
    cases len1Value with
    | loc p q =>
      simp only [WordSemStateFiniteExact.getVar] at len1Read
      refine ⟨target.permute,?_⟩
      simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read]
    | word length1 =>
      cases ptr1Read : WordSemStateFiniteExact.getVar ptr1 source with
      | none =>
        simp only [WordSemStateFiniteExact.getVar] at len1Read ptr1Read
        refine ⟨target.permute,?_⟩
        simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read,ptr1Read]
      | some ptr1Value =>
        cases ptr1Value with
        | loc p q =>
          simp only [WordSemStateFiniteExact.getVar] at len1Read ptr1Read
          refine ⟨target.permute,?_⟩
          simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read,ptr1Read]
        | word pointer1 =>
          cases len2Read : WordSemStateFiniteExact.getVar len2 source with
          | none =>
            simp only [WordSemStateFiniteExact.getVar] at len1Read ptr1Read len2Read
            refine ⟨target.permute,?_⟩
            simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read,ptr1Read,len2Read]
          | some len2Value =>
            cases len2Value with
            | loc p q =>
              simp only [WordSemStateFiniteExact.getVar] at len1Read ptr1Read len2Read
              refine ⟨target.permute,?_⟩
              simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read,ptr1Read,len2Read]
            | word length2 =>
              cases ptr2Read : WordSemStateFiniteExact.getVar ptr2 source with
              | none =>
                simp only [WordSemStateFiniteExact.getVar] at len1Read ptr1Read len2Read ptr2Read
                refine ⟨target.permute,?_⟩
                simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read,ptr1Read,len2Read,ptr2Read]
              | some ptr2Value =>
                cases ptr2Value with
                | loc p q =>
                  simp only [WordSemStateFiniteExact.getVar] at len1Read ptr1Read len2Read ptr2Read
                  refine ⟨target.permute,?_⟩
                  simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read,ptr1Read,len2Read,ptr2Read]
                | word pointer2 =>
                  cases cut : wordSemCutEnv (first,second) source.locals with
                  | none =>
                    simp only [WordSemStateFiniteExact.getVar] at len1Read ptr1Read len2Read ptr2Read
                    refine ⟨target.permute,?_⟩
                    simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read,ptr1Read,len2Read,ptr2Read,cut]
                  | some sourceEnv =>
                    cases readBytes1 : readBytearrayWordHOL pointer1 length1.toNat
                        (memLoadByteAuxExact source.memory source.mdomain source.be) with
                    | none =>
                      simp only [WordSemStateFiniteExact.getVar] at len1Read ptr1Read len2Read ptr2Read
                      refine ⟨target.permute,?_⟩
                      simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read,ptr1Read,len2Read,ptr2Read,cut,readBytes1]
                    | some bytes1 =>
                      cases readBytes2 : readBytearrayWordHOL pointer2 length2.toNat
                          (memLoadByteAuxExact source.memory source.mdomain source.be) with
                      | none =>
                        simp only [WordSemStateFiniteExact.getVar] at len1Read ptr1Read len2Read ptr2Read
                        refine ⟨target.permute,?_⟩
                        simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVar,len1Read,ptr1Read,len2Read,ptr2Read,cut,readBytes1,readBytes2]
                      | some bytes2 =>
                        exact ffiSuccessfulBranch source target ssa next ptr1 len1 ptr2 len2
                          function first second tables pointer1 length1 pointer2 length2 sourceEnv bytes1 bytes2
                          h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 namesBelow ptr1Read len1Read ptr2Read len2Read
                          cut readBytes1 readBytes2

end Flapjack.Compiler.Backend.WordAlloc
