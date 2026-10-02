import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticFFI
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvs

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

end Flapjack.Compiler.Backend.WordAlloc
