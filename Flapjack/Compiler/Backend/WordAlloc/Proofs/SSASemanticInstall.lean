import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticFFI
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert

namespace Flapjack.Compiler.Backend.WordAlloc

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

/-- Flapjack-specific preparation of the original Install case's first native
rename Move. There is no independent HOL declaration. The source cut premise
is the actual successful evaluator branch guard, not a premise to be added to
the final pass correctness theorem. It derives the actual target run and both
relations from the original SSA locals/map/frame inputs. Scratch-register,
four-argument and mapped-cut preparation remain to be composed below. -/
theorem installRefreshCutNames {width : Nat} [NeZero width] {C F : Type}
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


/-- Flapjack-specific Install argument preparation from actual successful source
reads. There is no standalone HOL theorem: the full case obtains these branch
guards by splitting the faithful evaluator. Scratch registers 2/4 are physical
and therefore cannot overwrite the refreshed SSA image, including data pointer
and length. The target execution, mapped cut and all reads are conclusions. -/
theorem installPrepareArguments {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next ptr len dptr dlen : Nat) (first second : Spt Unit)
    (pointer length dataPointer dataLength : BitVec width)
    (sourceEnv : Spt (WordLocW width))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (allocated : isAllocVar next) (valid : ssaMapOK next ssa)
    (readPtr : WordSemStateFiniteExact.getVar ptr source = some (.word pointer))
    (readLen : WordSemStateFiniteExact.getVar len source = some (.word length))
    (readDataPtr : WordSemStateFiniteExact.getVar dptr source = some (.word dataPointer))
    (readDataLen : WordSemStateFiniteExact.getVar dlen source = some (.word dataLength))
    (cut : wordSemCutEnv (first,second) source.locals = some sourceEnv) :
    let (move,mapOut,counter) := listNextVarRenameMove (width := width) ssa (next+2)
      ((sptToAList (sptUnion first second)).map Prod.fst)
    let (result,refreshed) := WordSemStateFiniteExact.evaluate move target
    let scratch := WordSemStateFiniteExact.setVars [2,4] [.word pointer,.word length] refreshed
    result = none ∧
      WordSemStateFiniteExact.evaluate
        (.move 1 [(2,optionLookup mapOut ptr),(4,optionLookup mapOut len)]) refreshed =
          (none,scratch) ∧
      WordSemStateFiniteExact.getVar 2 scratch = some (.word pointer) ∧
      WordSemStateFiniteExact.getVar 4 scratch = some (.word length) ∧
      WordSemStateFiniteExact.getVar (optionLookup mapOut dptr) scratch = some (.word dataPointer) ∧
      WordSemStateFiniteExact.getVar (optionLookup mapOut dlen) scratch = some (.word dataLength) ∧
      ssaLocalsRel counter mapOut source.locals scratch.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source scratch ∧
      ∃ targetEnv,
        wordSemCutEnv (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) (first,second))
          scratch.locals = some targetEnv ∧
        Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut)
          (sptDomain (sptUnion first second)) sourceEnv targetEnv ∧
        sptDomain sourceEnv = sptDomain (sptUnion first second) := by
  have preparation := installRefreshCutNames source target ssa next first second sourceEnv cut related valid frame
  generalize produced : listNextVarRenameMove (width := width) ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) = output at preparation ⊢
  rcases output with ⟨move,mapOut,counter⟩
  dsimp only at preparation ⊢
  generalize evaluated : WordSemStateFiniteExact.evaluate move target = run at preparation ⊢
  rcases run with ⟨result,refreshed⟩
  obtain ⟨rfl,refreshedRelated,refreshedFrame⟩ := preparation
  have stack : isStackVar (next+2) := isAllocVarFlip next allocated
  have properties := listNextVarRenameMoveProps _ ssa (next+2) move mapOut counter produced
    ⟨Or.inr stack,ssaMapOKMore next ssa (next+2) ⟨valid,by omega⟩⟩
  let scratch := WordSemStateFiniteExact.setVars [2,4] [.word pointer,.word length] refreshed
  have scratchRelated : ssaLocalsRel counter mapOut source.locals scratch.locals :=
    ssaLocalsPhysicalListUpdate counter mapOut source.locals refreshed.locals
      [2,4] [.word pointer,.word length] properties.2.2.2 refreshedRelated (by simp [isPhyVar])
  have scratchFrame : Flapjack.WordAlloc.wordStateEqRel source scratch := refreshedFrame
  have ptrRead := ssaLocalsRelGetVar counter mapOut source refreshed ptr (.word pointer)
    ⟨refreshedRelated,readPtr⟩
  have lenRead := ssaLocalsRelGetVar counter mapOut source refreshed len (.word length)
    ⟨refreshedRelated,readLen⟩
  have dataPtrRead := ssaLocalsRelGetVar counter mapOut source scratch dptr (.word dataPointer)
    ⟨scratchRelated,readDataPtr⟩
  have dataLenRead := ssaLocalsRelGetVar counter mapOut source scratch dlen (.word dataLength)
    ⟨scratchRelated,readDataLen⟩
  have cutResult := refreshedCut ssa (next+2) first second move mapOut counter
    source.locals scratch.locals sourceEnv produced cut scratchRelated
  refine ⟨rfl,?_,?_,?_,dataPtrRead,dataLenRead,scratchRelated,scratchFrame,cutResult⟩
  · simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVars,ptrRead,lenRead]
  · simp [WordSemStateFiniteExact.getVar,WordSemStateFiniteExact.setVars,
      LoopSemStateFiniteExact.sptAlistInsert,sptLookup_sptInsert]
  · simp [WordSemStateFiniteExact.getVar,WordSemStateFiniteExact.setVars,
      LoopSemStateFiniteExact.sptAlistInsert,sptLookup_sptInsert]

-- Flapjack factoring of the original Install case's inline cut-map argument;
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


/-- Flapjack-specific post-install locals algebra (original source9800-9840).
No independent HOL declaration exists. The mapped environment relation is
obtained from the actual source/target cuts before callback execution; this
helper derives the new SSA relation rather than assuming it. The physical
result at register2 cannot alias an old SSA value, and the fresh pointer copy
uses counter+2 exactly as the native nextVarRename producer does. -/
theorem installResultLocals {α : Type} (counter : Nat) (ssa : Spt Nat)
    (names : Spt Unit) (sourceEnv targetEnv : Spt α) (ptr : Nat) (value : α)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (sourceDomain : sptDomain sourceEnv = sptDomain names)
    (matching : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) sourceEnv targetEnv)
    (below : ∀ key, sptDomain names key → key < counter)
    (valid : ssaMapOK counter ssa) (ptrBound : ptr < counter+2) :
    ssaLocalsRel (counter+6) (sptInsert ptr (counter+2) (sptInter ssa names))
      (sptInsert ptr value sourceEnv)
      (sptInsert (counter+2) value (sptInsert 2 value targetEnv)) := by
  have cutRelated := cutLocalsRelation counter ssa names sourceEnv targetEnv
    mapped sourceDomain matching below
  have cutValid := ssaMapOKInter counter ssa names valid
  have physicalRelated := ssaLocalsRelIgnoreInsert counter (sptInter ssa names)
    sourceEnv targetEnv 2 value ⟨cutValid,cutRelated,by simp [isPhyVar]⟩
  have relatedMore := ssaLocalsRelMore counter (sptInter ssa names)
    sourceEnv (sptInsert 2 value targetEnv) (counter+2) ⟨physicalRelated,by omega⟩
  have validMore := ssaMapOKMore counter (sptInter ssa names) (counter+2) ⟨cutValid,by omega⟩
  simpa [Nat.add_assoc] using ssaLocalsRelInsert (counter+2) (sptInter ssa names)
    sourceEnv (sptInsert 2 value targetEnv) ptr value ⟨relatedMore,validMore,ptrBound⟩


/-- Flapjack-specific restoration after the actual successful Install callback.
There is no standalone HOL declaration. Input local shapes and frame are the
callback branch's computed states; the actual pointer-copy and final rename run,
full output SSA locals relation and frame are derived. In particular this helper
does not assume a target evaluation or its desired final locals relation. -/
theorem installRestoreResult {width : Nat} [NeZero width] {C F : Type}
    (sourceAfter targetAfter : WordSemStateFiniteExact width C F)
    (counter ptr : Nat) (ssa : Spt Nat) (names : Spt Unit)
    (sourceEnv targetEnv : Spt (WordLocW width)) (value : WordLocW width)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (sourceDomain : sptDomain sourceEnv = sptDomain names)
    (matching : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) sourceEnv targetEnv)
    (below : ∀ key, sptDomain names key → key < counter)
    (valid : ssaMapOK counter ssa) (stack : isStackVar counter)
    (ptrBound : ptr < counter+2)
    (sourceLocals : sourceAfter.locals = sptInsert ptr value sourceEnv)
    (targetLocals : targetAfter.locals = sptInsert 2 value targetEnv)
    (frame : Flapjack.WordAlloc.wordStateEqRel sourceAfter targetAfter) :
    let (ptrOut,ssaAfter,nextAfter) := nextVarRename ptr (sptInter ssa names) (counter+2)
    let (restore,ssaOut,nextOut) := listNextVarRenameMove (width := width) ssaAfter nextAfter
      ((sptToAList names).map Prod.fst)
    let (result,targetOut) := WordSemStateFiniteExact.evaluate
      (.seq (.move 1 [(ptrOut,2)]) restore) targetAfter
    result = none ∧ ssaLocalsRel nextOut ssaOut sourceAfter.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel sourceAfter targetOut := by
  dsimp only [nextVarRename]
  let copied := WordSemStateFiniteExact.setVar (counter+2) value targetAfter
  have copiedRelated : ssaLocalsRel (counter+6)
      (sptInsert ptr (counter+2) (sptInter ssa names)) sourceAfter.locals copied.locals := by
    simpa [copied,WordSemStateFiniteExact.setVar,sourceLocals,targetLocals] using
      installResultLocals counter ssa names sourceEnv targetEnv ptr value
        mapped sourceDomain matching below valid ptrBound
  have copiedFrame : Flapjack.WordAlloc.wordStateEqRel sourceAfter copied := frame
  have copyRun : WordSemStateFiniteExact.evaluate (.move 1 [(counter+2,2)]) targetAfter =
      (none,copied) := by
    simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVars,
      WordSemStateFiniteExact.getVar,targetLocals,copied,WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.setVars,LoopSemStateFiniteExact.sptAlistInsert,
      sptLookup_sptInsert_same]
  have originalValid := ssaMapOKMore counter (sptInter ssa names) (counter+2)
    ⟨ssaMapOKInter counter ssa names valid,by omega⟩
  have renamedProps := nextVarRenameProps ptr (sptInter ssa names) (counter+2)
    (counter+2) (sptInsert ptr (counter+2) (sptInter ssa names)) (counter+2+4) rfl
    ⟨Or.inl (isStackVarFlip counter stack),originalValid⟩
  have renamedValid : ssaMapOK (counter+6) (sptInsert ptr (counter+2) (sptInter ssa names)) := by
    simpa [Nat.add_assoc] using renamedProps.2.2.2
  have present : ∀ key ∈ (sptToAList names).map Prod.fst, sptDomain sourceAfter.locals key := by
    intro key member
    have inNames := (sptMemMapFstToAList names key).mp member
    obtain ⟨oldValue,read⟩ := (sptMem_iff_lookup key sourceEnv).mp (by change sptDomain sourceEnv key; rw [sourceDomain]; exact inNames)
    rw [sourceLocals]
    by_cases same : key = ptr
    · subst key; exact (sptMem_iff_lookup ptr _).mpr ⟨value,sptLookup_sptInsert_same ptr value sourceEnv⟩
    · exact (sptMem_iff_lookup key _).mpr ⟨oldValue,by rw [sptLookup_sptInsert_ne ptr key value sourceEnv same]; exact read⟩
  have restored := listNextVarRenameMovePreserve sourceAfter
    (sptInsert ptr (counter+2) (sptInter ssa names)) (counter+6)
    ((sptToAList names).map Prod.fst) copied
    ⟨copiedRelated,present,sptAllDistinctMapFstToAList _,renamedValid,copiedFrame⟩
  simp only [Nat.add_assoc] at *
  generalize produced : listNextVarRenameMove (width := width)
    (sptInsert ptr (counter+2) (sptInter ssa names)) (counter+6)
    ((sptToAList names).map Prod.fst) = output at restored ⊢
  rcases output with ⟨restore,ssaOut,nextOut⟩
  dsimp only at restored ⊢
  have seqRun : WordSemStateFiniteExact.evaluate
      (.seq (.move 1 [(counter+2,2)]) restore) targetAfter =
      WordSemStateFiniteExact.evaluate restore copied := by
    rw [WordSemStateFiniteExact.evaluate,copyRun]
    have fixed : targetAfter.fixClock ((none : Option (WordSemResult width)),copied) = (none,copied) := by
      simp [WordSemStateFiniteExact.fixClock,copied,WordSemStateFiniteExact.setVar]
    rw [fixed]
  rw [seqRun]
  exact ⟨restored.1,restored.2.1,restored.2.2.1⟩

end Flapjack.Compiler.Backend.WordAlloc
