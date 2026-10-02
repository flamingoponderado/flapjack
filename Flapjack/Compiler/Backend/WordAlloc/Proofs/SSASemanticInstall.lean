import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticFFI

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

end Flapjack.Compiler.Backend.WordAlloc
