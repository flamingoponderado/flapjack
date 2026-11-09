module

public import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticFFI
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCut

@[expose] public section

namespace Flapjack.Compiler.Backend.WordAlloc



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
  have preparation := refreshCutNames source target ssa next first second sourceEnv cut
    related valid frame
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


/-- Flapjack-specific aligned Install callback transport. Both sides' successful
argument/cut guards are internal facts derived by preparation, not public pass
correctness premises. The actual total evaluator's compile/buffer/oracle/code
branches determine the result and post-state frame; no target run is assumed.
The successful local shapes are proved for subsequent native restoration.
No standalone HOL declaration exists for this factoring. -/
theorem installCallbacksAligned {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ptr len dptr dlen targetPtr targetLen targetDptr targetDlen : Nat)
    (names targetNames : WordLangCutsetsHOL)
    (sourceEnv targetEnv : Spt (WordLocW width))
    (pointer length dataPointer dataLength : BitVec width)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (sourceCut : wordSemCutEnv names source.locals = some sourceEnv)
    (targetCut : wordSemCutEnv targetNames target.locals = some targetEnv)
    (sourcePtr : WordSemStateFiniteExact.getVar ptr source = some (.word pointer))
    (sourceLen : WordSemStateFiniteExact.getVar len source = some (.word length))
    (sourceDptr : WordSemStateFiniteExact.getVar dptr source = some (.word dataPointer))
    (sourceDlen : WordSemStateFiniteExact.getVar dlen source = some (.word dataLength))
    (targetPtrRead : WordSemStateFiniteExact.getVar targetPtr target = some (.word pointer))
    (targetLenRead : WordSemStateFiniteExact.getVar targetLen target = some (.word length))
    (targetDptrRead : WordSemStateFiniteExact.getVar targetDptr target = some (.word dataPointer))
    (targetDlenRead : WordSemStateFiniteExact.getVar targetDlen target = some (.word dataLength)) :
    let sourceRun := WordSemStateFiniteExact.evaluate (.install ptr len dptr dlen names) source
    let targetRun := WordSemStateFiniteExact.evaluate
      (.install targetPtr targetLen targetDptr targetDlen targetNames) target
    sourceRun.1 = targetRun.1 ∧
      Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
      (sourceRun.1 = none → ∃ label,
        sourceRun.2.locals = sptInsert ptr (.loc label 0) sourceEnv ∧
        targetRun.2.locals = sptInsert targetPtr (.loc label 0) targetEnv) := by
  rcases frame with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
  simp only [WordSemStateFiniteExact.evaluate,sourceCut,targetCut,sourcePtr,sourceLen,
    sourceDptr,sourceDlen,targetPtrRead,targetLenRead,targetDptrRead,targetDlenRead,
    h14,h18,h19,h20,h21]
  repeat' first
    | split
    | (solve | simp_all [Flapjack.WordAlloc.wordStateEqRel])
  all_goals simp_all [Flapjack.WordAlloc.wordStateEqRel]
  all_goals first | exact ⟨_,rfl,rfl⟩ | grind

end Flapjack.Compiler.Backend.WordAlloc
