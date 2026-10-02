import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticFFI
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvs
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Alloc
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack-specific first native Alloc rename Move, original9333-9380.
There is no independent HOL declaration. Successful source paired-cut guards
supply exactly the original union names; target execution and full SSA/frame
relations are derived. Count scratch Move and paired target cuts are composed by
allocPrepareArguments below; no full Alloc port tag is claimed. -/
theorem allocRefreshCutNames {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (first second : Spt Unit)
    (sourceEnvFirst sourceEnvSecond : Spt (WordLocW width))
    (cut : wordSemCutEnvs (first,second) source.locals = some (sourceEnvFirst,sourceEnvSecond))
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (valid : ssaMapOK next ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move,mapOut,counter) := listNextVarRenameMove (width := width) ssa (next+2)
      ((sptToAList (sptUnion first second)).map Prod.fst)
    let (result,targetOut) := WordSemStateFiniteExact.evaluate move target
    result = none ∧ ssaLocalsRel counter mapOut source.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source targetOut := by
  have subsets := cutEnvsDomainSubset first second source.locals (sourceEnvFirst,sourceEnvSecond) cut
  have present : ∀ key, sptDomain (sptUnion first second) key → sptDomain source.locals key := by
    intro key member
    rw [sptDomain_sptUnion] at member
    exact member.elim (subsets.1 key) (subsets.2 key)
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


/-- Flapjack-specific Alloc preparation (original9333-9410), with source
successful count/paired-cut guards obtained by the full evaluator case split.
There is no standalone HOL declaration. Actual rename and count Move runs,
target cut success, both restricted relations, exact image domains and inherited
injections are conclusions. No collector outcome or target evaluation is assumed. -/
theorem allocPrepareArguments {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next num : Nat) (first second : Spt Unit)
    (sourceEnvFirst sourceEnvSecond : Spt (WordLocW width)) (amount : BitVec width)
    (cut : wordSemCutEnvs (first,second) source.locals = some (sourceEnvFirst,sourceEnvSecond))
    (read : WordSemStateFiniteExact.getVar num source = some (.word amount))
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (allocated : isAllocVar next) (valid : ssaMapOK next ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move,mapOut,counter) := listNextVarRenameMove (width := width) ssa (next+2)
      ((sptToAList (sptUnion first second)).map Prod.fst)
    let (result,refreshed) := WordSemStateFiniteExact.evaluate move target
    let scratch := WordSemStateFiniteExact.setVar 2 (.word amount) refreshed
    result = none ∧
      WordSemStateFiniteExact.evaluate (.move 1 [(2,optionLookup mapOut num)]) refreshed =
        (none,scratch) ∧
      WordSemStateFiniteExact.getVar 2 scratch = some (.word amount) ∧
      ssaLocalsRel counter mapOut source.locals scratch.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source scratch ∧
      ∃ targetEnvFirst targetEnvSecond,
        wordSemCutEnvs (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) (first,second))
          scratch.locals = some (targetEnvFirst,targetEnvSecond) ∧
        sptDomain targetEnvFirst = (fun key => ∃ name, sptDomain first name ∧ optionLookup mapOut name = key) ∧
        sptDomain targetEnvSecond = (fun key => ∃ name, sptDomain second name ∧ optionLookup mapOut name = key) ∧
        Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut) (sptDomain first)
          sourceEnvFirst targetEnvFirst ∧
        Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut) (sptDomain second)
          sourceEnvSecond targetEnvSecond ∧
        (∀ a b, sptDomain sourceEnvFirst a → sptDomain sourceEnvFirst b →
          optionLookup mapOut a = optionLookup mapOut b → a = b) ∧
        (∀ a b, sptDomain sourceEnvSecond a → sptDomain sourceEnvSecond b →
          optionLookup mapOut a = optionLookup mapOut b → a = b) ∧
        sptDomain sourceEnvFirst = sptDomain first ∧ sptDomain sourceEnvSecond = sptDomain second := by
  have preparation := allocRefreshCutNames source target ssa next first second
    sourceEnvFirst sourceEnvSecond cut related valid frame
  generalize produced : listNextVarRenameMove (width := width) ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) = output at preparation ⊢
  rcases output with ⟨move,mapOut,counter⟩
  dsimp only at preparation ⊢
  generalize evaluated : WordSemStateFiniteExact.evaluate move target = run at preparation ⊢
  rcases run with ⟨result,refreshed⟩
  obtain ⟨rfl,refreshedRelated,refreshedFrame⟩ := preparation
  have properties := listNextVarRenameMoveProps _ ssa (next+2) move mapOut counter produced
    ⟨Or.inr (isAllocVarFlip next allocated),ssaMapOKMore next ssa (next+2) ⟨valid,by omega⟩⟩
  let scratch := WordSemStateFiniteExact.setVar 2 (.word amount) refreshed
  have scratchRelated : ssaLocalsRel counter mapOut source.locals scratch.locals :=
    ssaLocalsRelIgnoreSetVar counter mapOut source refreshed 2 (.word amount)
      ⟨properties.2.2.2,refreshedRelated,by simp [isPhyVar]⟩
  have scratchFrame : Flapjack.WordAlloc.wordStateEqRel source scratch := refreshedFrame
  have numberRead := ssaLocalsRelGetVar counter mapOut source refreshed num (.word amount)
    ⟨refreshedRelated,read⟩
  have injection : ∀ x y, sptDomain (sptUnion first second) x →
      sptDomain (sptUnion first second) y → optionLookup mapOut x = optionLookup mapOut y → x = y := by
    intro x y inX inY equal
    exact listNextVarRenameMoveDistinct ssa (next+2) _ move mapOut counter x y
      ⟨produced,sptAllDistinctMapFstToAList _,(sptMemMapFstToAList _ x).mpr inX,
        (sptMemMapFstToAList _ y).mpr inY,equal⟩
  have scopedRelation : ∀ names : Nat → Prop,
      Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut) names source.locals scratch.locals := by
    intro names key value found
    have matching := scratchRelated.2 key value found.2
    obtain ⟨register,lookup⟩ := (sptMem_iff_lookup key mapOut).mp matching.1
    simpa [optionLookup,lookup] using matching.2.1
  have cuts := Flapjack.WordAlloc.cutEnvsLemma first second source.locals scratch.locals
    sourceEnvFirst sourceEnvSecond (optionLookup mapOut)
    ⟨(fun x y inX inY equal => injection x y
        (by rw [sptDomain_sptUnion]; exact Or.inl inX)
        (by rw [sptDomain_sptUnion]; exact Or.inl inY) equal),
      (fun x y inX inY equal => injection x y
        (by rw [sptDomain_sptUnion]; exact Or.inr inX)
        (by rw [sptDomain_sptUnion]; exact Or.inr inY) equal),
      cut,scopedRelation _,scopedRelation _⟩
  refine ⟨rfl,?_,?_,scratchRelated,scratchFrame,cuts⟩
  · simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.getVars,numberRead,
      WordSemStateFiniteExact.setVars,WordSemStateFiniteExact.setVar,
      LoopSemStateFiniteExact.sptAlistInsert]
  · simp [WordSemStateFiniteExact.getVar,WordSemStateFiniteExact.setVar,sptLookup_sptInsert_same]

/-- Flapjack-specific factoring of original Alloc9460-9480. Actual normal
return supplies the branch guard; the post-GC locals domain is derived.
No standalone HOL declaration or full SSA Alloc tag is claimed. -/
theorem allocNormalLocalsDomain {width : Nat} [NeZero width] {C F : Type}
    (amount : BitVec width) (first second : Spt Unit)
    (source : WordSemStateFiniteExact width C F)
    (normal : (WordSemStateFiniteExact.alloc amount (first,second) source).1 = none) :
    sptDomain (WordSemStateFiniteExact.alloc amount (first,second) source).2.locals =
      (fun key => sptDomain first key ∨ sptDomain second key) := by
  classical
  unfold WordSemStateFiniteExact.alloc at normal ⊢
  cases cut : wordSemCutEnvs (first,second) source.locals with
  | none => simp [cut] at normal
  | some envs =>
    have subsets := cutEnvsDomainSubset first second source.locals envs cut
    have subsetFirst : LoopSemStateFiniteExact.sptSubsetLive first source.locals := subsets.1
    have subsetSecond : LoopSemStateFiniteExact.sptSubsetLive second source.locals := subsets.2
    have envDomains : sptDomain envs.1 = sptDomain first ∧
        sptDomain envs.2 = sptDomain second := by
      have shape : envs = (sptInter source.locals first,sptInter source.locals second) := by
        simpa [wordSemCutEnvs,wordSemCutNames,subsetFirst,subsetSecond] using cut.symm
      rw [shape]
      constructor <;> funext key <;> simp only [sptDomain_sptInter]
      · exact propext ⟨And.right,fun h => ⟨subsets.1 key h,h⟩⟩
      · exact propext ⟨And.right,fun h => ⟨subsets.2 key h,h⟩⟩
    cases collected : WordSemStateFiniteExact.gc
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.setStore .allocSize (.word amount) source)) with
    | none => simp [cut,collected] at normal
    | some gcState =>
      have keys := WordSemStackEq.gcSKeyEq _ _ collected
      obtain ⟨n,l,ls,opt,stackShape,popped,pop,locals,domains,restKeys⟩ :=
        WordSemStackEq.pushEnvPopEnvSKeyEq envs none
          (WordSemStateFiniteExact.setStore .allocSize (.word amount) source) gcState keys
      simp only [collected,pop]
      simp only [cut,collected,pop] at normal
      cases stored : WordSemStateFiniteExact.getStore .allocSize popped with
      | none => simp [stored] at normal
      | some value =>
        dsimp only
        cases space : WordSemStateFiniteExact.hasSpace value popped with
        | none => simp [stored,space] at normal
        | some available =>
          cases available with
          | false => simp [stored,space] at normal
          | true =>
            dsimp only
            rw [← domains,envDomains.1,envDomains.2]
            funext key
            exact propext or_comm

-- Internal restricted-map algebra from the original Alloc9478-9548 branch.
private theorem allocCutLocalsRelation {α : Type} (next : Nat) (ssa : Spt Nat)
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


/-- Flapjack-specific original Alloc final rename restoration (9548-9606).
The domain, scoped value relation and bounds are internal collector facts;
actual final Move execution and full SSA/frame are derived. No standalone
HOL declaration exists; the full Alloc simulation is assembled in ssaCcTransCorrectAlloc. -/
theorem allocRestoreLocals {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (names : Spt Unit) (counter : Nat)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (matching : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source.locals target.locals)
    (below : ∀ key, sptDomain names key → key < counter)
    (valid : ssaMapOK counter ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move,ssaOut,nextOut) := listNextVarRenameMove (width := width)
      (sptInter ssa names) (counter+2) ((sptToAList names).map Prod.fst)
    let (result,targetOut) := WordSemStateFiniteExact.evaluate move target
    result = none ∧ ssaLocalsRel nextOut ssaOut source.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source targetOut := by
  have restricted := allocCutLocalsRelation counter ssa names source.locals target.locals
    mapped sourceDomain matching below
  have present : ∀ key ∈ (sptToAList names).map Prod.fst, sptDomain source.locals key := by
    intro key member
    rw [sourceDomain]
    exact (sptMemMapFstToAList names key).mp member
  have restored := listNextVarRenameMovePreserve source (sptInter ssa names) (counter+2)
    ((sptToAList names).map Prod.fst) target
    ⟨ssaLocalsRelMore counter _ _ _ (counter+2) ⟨restricted,by omega⟩,
      present,sptAllDistinctMapFstToAList _,
      ssaMapOKMore counter _ (counter+2) ⟨ssaMapOKInter counter ssa names valid,by omega⟩,
      frame⟩
  generalize produced : listNextVarRenameMove (width := width)
    (sptInter ssa names) (counter+2) ((sptToAList names).map Prod.fst) = output at restored ⊢
  rcases output with ⟨move,ssaOut,nextOut⟩
  generalize evaluated : WordSemStateFiniteExact.evaluate move target = run at restored ⊢
  rcases run with ⟨result,targetOut⟩
  exact ⟨restored.1,restored.2.1,restored.2.2.1⟩

/-- Flapjack-specific original Alloc9410-9558 collector transport factoring.
The existing native allocation simulation chooses the source permutation;
actual results/frame agree, and normal return derives scoped locals and domain.
No target allocation outcome or desired post-relation is assumed. There is no
standalone HOL declaration; the full Alloc case is assembled in ssaCcTransCorrectAlloc. -/
theorem allocCollectorTransport {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (first second : Spt Unit) (amount : BitVec width)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) →
      optionLookup ssa a = optionLookup ssa b → a = b)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain first) source.locals target.locals)
    (secondRelated : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain second) source.locals target.locals) :
    ∃ perm,
      let sourceRun := WordSemStateFiniteExact.alloc amount (first,second)
        {source with permute := perm};
      let targetRun := WordSemStateFiniteExact.alloc amount
        (Flapjack.WordAlloc.applyNummapsKey (optionLookup ssa) (first,second)) target;
      sourceRun.1 ≠ some .error → sourceRun.1 = targetRun.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        (sourceRun.1 = none →
          Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
            (sptDomain (sptUnion first second)) sourceRun.2.locals targetRun.2.locals ∧
          sptDomain sourceRun.2.locals = sptDomain (sptUnion first second)) := by
  obtain ⟨perm,transport⟩ := Flapjack.WordAlloc.allocSim source target
    (optionLookup ssa) first second amount (sptUnion first second) []
    frame injective firstRelated secondRelated
  refine ⟨perm,?_⟩
  dsimp only
  intro nonError
  obtain ⟨result,shared,locals⟩ := transport nonError
  refine ⟨result,shared,?_⟩
  intro normal
  have related : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain (sptUnion first second))
      (WordSemStateFiniteExact.alloc amount (first,second) {source with permute := perm}).2.locals
      (WordSemStateFiniteExact.alloc amount
        (Flapjack.WordAlloc.applyNummapsKey (optionLookup ssa) (first,second)) target).2.locals := by
    simpa only [normal,Flapjack.WordAlloc.applyColourLocals] using locals
  refine ⟨related,?_⟩
  simpa only [sptDomain_sptUnion] using
    allocNormalLocalsDomain amount first second {source with permute := perm} normal

/-- Flapjack-specific exhaustive raw Alloc branch fact, used by the original
9558-9606 SSA failure branch. Error exemption leaves only normal return or
NotEnoughSpace, whose actual flush empties locals. No target outcome or locals
shape is assumed; no standalone HOL declaration or full Alloc tag exists. -/
theorem allocNonErrorShape {width : Nat} [NeZero width] {C F : Type}
    (amount : BitVec width) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact width C F)
    (nonError : (WordSemStateFiniteExact.alloc amount names source).1 ≠ some .error) :
    (WordSemStateFiniteExact.alloc amount names source).1 = none ∨
      ((WordSemStateFiniteExact.alloc amount names source).1 = some .notEnoughSpace ∧
        (WordSemStateFiniteExact.alloc amount names source).2.locals = .ln) := by
  unfold WordSemStateFiniteExact.alloc at nonError ⊢
  repeat' split <;> simp_all [WordSemStateFiniteExact.flushState]

end Flapjack.Compiler.Backend.WordAlloc
