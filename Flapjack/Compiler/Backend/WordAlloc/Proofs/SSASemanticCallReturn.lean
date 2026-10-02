import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallTail
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvs
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSACutEnvsDomain
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMoveDistinct

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack-specific first returning Call rename factoring (8298-8360).
Actual source argument/cut guards derive the generated Move execution, new SSA
and frame plus argument rereads through the ORIGINAL SSA map, as the actual
compiler requires. No standalone HOL declaration or full Call port tag exists. -/
theorem returningRefreshArguments {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (args : List Nat) (values : List (WordLocW width)) (first second : Spt Unit)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (cut : wordSemCutEnvs (first,second) source.locals = some envs)
    (read : WordSemStateFiniteExact.getVars args source = some values)
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (valid : ssaMapOK next ssa) (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move,mapOut,counter) := listNextVarRenameMove (width := width) ssa (next+2)
      ((sptToAList (sptUnion first second)).map Prod.fst)
    let (result,refreshed) := WordSemStateFiniteExact.evaluate move target
    result = none ∧ ssaLocalsRel counter mapOut source.locals refreshed.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source refreshed ∧
      WordSemStateFiniteExact.getVars (args.map (optionLookup ssa)) refreshed = some values := by
  have subsets := cutEnvsDomainSubset first second source.locals envs cut
  have present : ∀ key ∈ (sptToAList (sptUnion first second)).map Prod.fst,
      sptDomain source.locals key := by
    intro key member
    have inNames := (sptMemMapFstToAList _ key).mp member
    rw [sptDomain_sptUnion] at inNames
    exact inNames.elim (subsets.1 key) (subsets.2 key)
  have preparation := listNextVarRenameMovePreserve source ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) target
    ⟨ssaLocalsRelMore next ssa _ _ (next+2) ⟨related,by omega⟩,
      present,sptAllDistinctMapFstToAList _,
      ssaMapOKMore next ssa (next+2) ⟨valid,by omega⟩,frame⟩
  generalize produced : listNextVarRenameMove (width := width) ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) = output at preparation ⊢
  rcases output with ⟨move,mapOut,counter⟩
  dsimp only at preparation ⊢
  generalize evaluated : WordSemStateFiniteExact.evaluate move target = run at preparation ⊢
  rcases run with ⟨result,refreshed⟩
  dsimp only at preparation ⊢
  obtain ⟨normal,newRelated,newFrame,physical,originalReads⟩ := preparation
  have originalRelation : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (fun _ => True) source.locals refreshed.locals := by
    intro key value found
    obtain ⟨register,lookup⟩ := (sptMem_iff_lookup key ssa).mp (related.2 key value found.2).1
    simpa [optionLookup,holThe,lookup] using originalReads key value found.2
  exact ⟨normal,newRelated,newFrame,
    Flapjack.WordAlloc.strongLocalsRelGetVars args values (optionLookup ssa)
      (fun _ => True) source refreshed ⟨originalRelation,fun _ _ => trivial,read⟩⟩

/-- Flapjack-specific returning Call argument Move and paired-cut preparation
(8330-8410). Generated convention registers are 2*(i+1); old SSA argument reads
survive the first stack rename, while new SSA locals survive their physical
updates. Actual Move, rereads, frame and full mapped paired-cut relations/domain
are conclusions. No target-run premise or full returning Call tag is claimed. -/
theorem returningPrepareArguments {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (args : List Nat) (values : List (WordLocW width)) (first second : Spt Unit)
    (sourceFirst sourceSecond : Spt (WordLocW width))
    (cut : wordSemCutEnvs (first,second) source.locals = some (sourceFirst,sourceSecond))
    (read : WordSemStateFiniteExact.getVars args source = some values)
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (allocated : isAllocVar next) (valid : ssaMapOK next ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move,mapOut,counter) := listNextVarRenameMove (width := width) ssa (next+2)
      ((sptToAList (sptUnion first second)).map Prod.fst)
    let (result,refreshed) := WordSemStateFiniteExact.evaluate move target
    let renamed := args.map (optionLookup ssa)
    let registers := (List.range renamed.length).map fun key => 2*(key+1)
    let prepared := WordSemStateFiniteExact.setVars registers values refreshed
    result = none ∧
      WordSemStateFiniteExact.evaluate (.move 1 (registers.zip renamed)) refreshed = (none,prepared) ∧
      WordSemStateFiniteExact.getVars registers prepared = some values ∧
      ssaLocalsRel counter mapOut source.locals prepared.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source prepared ∧
      ∃ targetFirst targetSecond,
        wordSemCutEnvs (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) (first,second))
          prepared.locals = some (targetFirst,targetSecond) ∧
        sptDomain targetFirst = (fun key => ∃ name, sptDomain first name ∧ optionLookup mapOut name = key) ∧
        sptDomain targetSecond = (fun key => ∃ name, sptDomain second name ∧ optionLookup mapOut name = key) ∧
        Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut) (sptDomain first) sourceFirst targetFirst ∧
        Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut) (sptDomain second) sourceSecond targetSecond ∧
        (∀ a b, sptDomain sourceFirst a → sptDomain sourceFirst b → optionLookup mapOut a = optionLookup mapOut b → a = b) ∧
        (∀ a b, sptDomain sourceSecond a → sptDomain sourceSecond b → optionLookup mapOut a = optionLookup mapOut b → a = b) ∧
        sptDomain sourceFirst = sptDomain first ∧ sptDomain sourceSecond = sptDomain second := by
  have preparation := returningRefreshArguments source target ssa next args values first second
    (sourceFirst,sourceSecond) cut read related valid frame
  generalize produced : listNextVarRenameMove (width := width) ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) = output at preparation ⊢
  rcases output with ⟨move,mapOut,counter⟩
  dsimp only at preparation ⊢
  generalize evaluated : WordSemStateFiniteExact.evaluate move target = run at preparation ⊢
  rcases run with ⟨result,refreshed⟩
  dsimp only at preparation ⊢
  obtain ⟨normal,newRelated,newFrame,renamedRead⟩ := preparation
  let renamed := args.map (optionLookup ssa)
  let registers := (List.range renamed.length).map fun key => 2*(key+1)
  let prepared := WordSemStateFiniteExact.setVars registers values refreshed
  have lengths := Flapjack.WordAlloc.getVarsLength args source values read
  have distinct : registers.Nodup := by
    apply List.Nodup.map _ List.nodup_range
    intro x y equal
    change 2*(x+1) = 2*(y+1) at equal
    omega
  have same : registers.length = renamed.length := by simp [registers]
  have valueLength : values.length = registers.length := by simp [registers,renamed,lengths]
  have properties := listNextVarRenameMoveProps _ ssa (next+2) move mapOut counter produced
    ⟨Or.inr (isAllocVarFlip next allocated),ssaMapOKMore next ssa (next+2) ⟨valid,by omega⟩⟩
  have physical : ∀ register ∈ registers, isPhyVar register := by
    intro register member
    obtain ⟨key,_,rfl⟩ := List.mem_map.mp member
    simp [isPhyVar]
  have preparedRelated : ssaLocalsRel counter mapOut source.locals prepared.locals :=
    ssaLocalsRelIgnoreListInsert counter mapOut source refreshed registers values
      ⟨properties.2.2.2,newRelated,physical,valueLength.symm⟩
  have preparedFrame : Flapjack.WordAlloc.wordStateEqRel source prepared := newFrame
  have scopedRelation : ∀ live : Nat → Prop,
      Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut) live source.locals prepared.locals := by
    intro live key value found
    obtain ⟨register,lookup⟩ := (sptMem_iff_lookup key mapOut).mp (preparedRelated.2 key value found.2).1
    simpa [optionLookup,lookup] using (preparedRelated.2 key value found.2).2.1
  have injection : ∀ a b, sptDomain (sptUnion first second) a →
      sptDomain (sptUnion first second) b → optionLookup mapOut a = optionLookup mapOut b → a = b := by
    intro a b inA inB equal
    exact listNextVarRenameMoveDistinct ssa (next+2) _ move mapOut counter a b
      ⟨produced,sptAllDistinctMapFstToAList _,(sptMemMapFstToAList _ a).mpr inA,
        (sptMemMapFstToAList _ b).mpr inB,equal⟩
  have cuts := Flapjack.WordAlloc.cutEnvsLemma first second source.locals prepared.locals
    sourceFirst sourceSecond (optionLookup mapOut)
    ⟨(fun a b inA inB equal => injection a b
        (by rw [sptDomain_sptUnion]; exact Or.inl inA)
        (by rw [sptDomain_sptUnion]; exact Or.inl inB) equal),
      (fun a b inA inB equal => injection a b
        (by rw [sptDomain_sptUnion]; exact Or.inr inA)
        (by rw [sptDomain_sptUnion]; exact Or.inr inB) equal),
      cut,scopedRelation _,scopedRelation _⟩
  refine ⟨normal,?_,getVarsSetVarsEq registers values refreshed ⟨distinct,valueLength⟩,
    preparedRelated,preparedFrame,cuts⟩
  change WordSemStateFiniteExact.evaluate (.move 1 (registers.zip renamed)) refreshed = (none,prepared)
  simp only [WordSemStateFiniteExact.evaluate,List.map_fst_zip (Nat.le_of_eq same),
    List.map_snd_zip (Nat.le_of_eq same.symm),distinct,if_true]
  rw [show WordSemStateFiniteExact.getVars renamed refreshed = some values from renamedRead]

end Flapjack.Compiler.Backend.WordAlloc
