import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallTail
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Alloc
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvs
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSACutEnvsDomain
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsListRename
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMoveDistinct
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap

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

/-- Flapjack-specific original returning Call8422-8477 pushed-stack/callee
transport. The source root permutation is chosen from actual cut relations;
full callee-entry state equality after stack replacement and stack values are
derived. Total body stack-swap transport is available for every result branch.
No target run or desired callee-state equality premise; no standalone HOL tag. -/
theorem returningCalleeTransport {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (sourceFirst sourceSecond targetFirst targetSecond : Spt (WordLocW width))
    (f : Nat → Nat)
    (handler targetHandler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (args : List (WordLocW width)) (size : Option Nat) (body : WordLangProgHOL (BitVec width))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (firstDomain : sptDomain targetFirst =
      (fun key => ∃ name, sptDomain sourceFirst name ∧ f name = key))
    (secondDomain : sptDomain targetSecond =
      (fun key => ∃ name, sptDomain sourceSecond name ∧ f name = key))
    (firstInjective : ∀ a b, sptDomain sourceFirst a → sptDomain sourceFirst b → f a = f b → a = b)
    (secondInjective : ∀ a b, sptDomain sourceSecond a → sptDomain sourceSecond b → f a = f b → a = b)
    (secondRelated : Flapjack.WordAlloc.strongLocalsRel f (sptDomain sourceSecond)
      sourceSecond targetSecond)
    (handlerAligned : match handler with
      | none => targetHandler = none
      | some (_,_,l1,l2) => match targetHandler with
        | none => False
        | some (_,_,r1,r2) => r1 = l1 ∧ r2 = l2) :
    ∃ perm,
      let sourceEntry := WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (sourceFirst,sourceSecond) handler
          {WordSemStateFiniteExact.decClock source with permute := perm});
      let targetEntry := WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) targetHandler
          (WordSemStateFiniteExact.decClock target));
      (wordSemEnvToList sourceSecond perm).2 = (wordSemEnvToList targetSecond target.permute).2 ∧
      {sourceEntry with stack := targetEntry.stack} = targetEntry ∧
      WordSemStackEq.sValEq sourceEntry.stack targetEntry.stack ∧
      WordSemStackEq.stackSwapPost body sourceEntry := by
  have fields := frame
  rcases fields with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
  obtain ⟨perm,roots,values⟩ := Flapjack.WordAlloc.pushEnvSValEq
    (WordSemStateFiniteExact.decClock source) (WordSemStateFiniteExact.decClock target)
    sourceSecond sourceFirst targetSecond targetFirst f handler targetHandler
    (wordSemEnvToList targetSecond target.permute).2
    ⟨h12.symm,h4.symm,h3.symm,secondDomain,secondInjective,firstDomain,firstInjective,secondRelated,handlerAligned⟩
  have permutation : (wordSemEnvToList sourceSecond perm).2 =
      (wordSemEnvToList targetSecond target.permute).2 := roots.1
  have sameKind : handler.isSome = targetHandler.isSome := by
    cases handler with
    | none => rw [handlerAligned]
    | some payload =>
      rcases payload with ⟨name,prog,l1,l2⟩
      cases targetHandler with
      | none => exact False.elim handlerAligned
      | some payload => rfl
  have entry := Flapjack.WordAlloc.calleeSwap frame sourceFirst sourceSecond targetFirst targetSecond
    handler targetHandler sameKind perm permutation values args size
  refine ⟨perm,permutation,entry,values,?_⟩
  exact WordSemStackEq.evaluateStackSwap body _


/-- Flapjack-specific returning Call continuation preparation (original8550-8575).
The restored cut SSA is an internal pop-environment fact. Physical return
register insertion preserves it and the actual generated retMov executes with
NONE and derives new SSA/frame. No standalone HOL tag or target run premise. -/
theorem returningRestoreRegisters {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (names : Spt Unit) (counter count : Nat) (values : List (WordLocW width))
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (length : values.length = count)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let registers := (List.range count).map (fun index => 2*(index+1))
    let prepared := WordSemStateFiniteExact.setVars registers values target
    let (move,mapOut,nextOut) := listNextVarRenameMove (width := width)
      (sptInter ssa names) (counter+2) ((sptToAList names).map Prod.fst)
    let (result,targetOut) := WordSemStateFiniteExact.evaluate move prepared
    result = none ∧ ssaLocalsRel nextOut mapOut source.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source targetOut := by
  let registers := (List.range count).map (fun index => 2*(index+1))
  have physical : ∀ register ∈ registers, isPhyVar register := by
    intro register member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    simp [isPhyVar]
  have inserted := ssaLocalsRelIgnoreListInsert counter (sptInter ssa names)
    source target registers values
    ⟨ssaMapOKInter counter ssa names valid,related,physical,by simp [registers,length]⟩
  have present : ∀ key ∈ (sptToAList names).map Prod.fst, sptDomain source.locals key := by
    intro key member
    rw [sourceDomain]
    exact (sptMemMapFstToAList names key).mp member
  have restored := listNextVarRenameMovePreserve source (sptInter ssa names) (counter+2)
    ((sptToAList names).map Prod.fst) (WordSemStateFiniteExact.setVars registers values target)
    ⟨ssaLocalsRelMore counter _ _ _ (counter+2) ⟨inserted,by omega⟩,
      present,sptAllDistinctMapFstToAList _,
      ssaMapOKMore counter _ (counter+2) ⟨ssaMapOKInter counter ssa names valid,by omega⟩,frame⟩
  dsimp only at restored ⊢
  exact ⟨restored.1,restored.2.1,restored.2.2.1⟩


/-- Flapjack-specific original8477-8550 pop-environment lookup factoring.
The key/value stack facts are produced by total callee stack-swap transport;
actual successful pops, full frame, cut domains and all popped value lookups
are derived. No popped-local relation or desired target run is assumed. -/
theorem returningPopCutRelation {width : Nat} [NeZero width] {C F : Type}
    (source target returned : WordSemStateFiniteExact width C F)
    (first second targetFirst targetSecond : Spt (WordLocW width))
    (handler targetHandler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (targetStack : List (WordSemStackFrame width)) (f : Nat → Nat)
    (sourceRoots targetRoots : List (Nat × WordLocW width))
    (sourcePerm targetPerm : Nat → Nat → Nat)
    (sameStack : source.stack = target.stack)
    (sourceRootRead : wordSemEnvToList second source.permute = (sourceRoots,sourcePerm))
    (targetRootRead : wordSemEnvToList targetSecond target.permute = (targetRoots,targetPerm))
    (rootMap : sourceRoots.map (fun (key,value) => (f key,value)) = targetRoots)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel f (sptDomain first) first targetFirst)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) → f a = f b → a = b)
    (sourceKeys : WordSemStackEq.sKeyEq
      (WordSemStateFiniteExact.pushEnv (first,second) handler source).stack returned.stack)
    (targetKeys : WordSemStackEq.sKeyEq
      (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) targetHandler target).stack targetStack)
    (values : WordSemStackEq.sValEq returned.stack targetStack) :
    ∃ popped targetPopped,
      WordSemStateFiniteExact.popEnv returned = some popped ∧
      WordSemStateFiniteExact.popEnv {returned with stack := targetStack} = some targetPopped ∧
      Flapjack.WordAlloc.wordStateEqRel popped targetPopped ∧
      sptDomain popped.locals = (fun key => sptDomain first key ∨ sptDomain second key) ∧
      (∀ live, Flapjack.WordAlloc.strongLocalsRel f live popped.locals targetPopped.locals) := by
  open WordSemStackEq in
    obtain ⟨nS,lS,restS,optS,sourceShape,popped,sourcePop,sourceLocals,sourceDomain,sourceTail⟩ :=
      pushEnvPopEnvSKeyEq (first,second) handler source returned sourceKeys
  open WordSemStackEq in
    obtain ⟨nT,lT,restT,optT,targetShape,targetPopped,targetPop,targetLocals,targetDomain,targetTail⟩ :=
      pushEnvPopEnvSKeyEq (targetFirst,targetSecond) targetHandler target
        {returned with stack := targetStack} targetKeys
  have frame := Flapjack.WordAlloc.popEnvFrame returned popped targetPopped targetStack
    ⟨values,WordSemStackEq.sKeyEqTrans _ _ _
      ⟨(WordSemStackEq.sKeyEqSym _ _).mp sourceTail,by rw [sameStack]; exact targetTail⟩,
      targetPop,sourcePop⟩
  have sourceRootKeys := Flapjack.WordAlloc.sKeyEqPushEnvImpMapFst source first second handler
    nS (sptToAList first) lS optS restS sourceRoots sourcePerm
    ⟨by rw [←sourceShape]; exact sourceKeys,sourceRootRead⟩
  have targetRootKeys := Flapjack.WordAlloc.sKeyEqPushEnvImpMapFst target targetFirst targetSecond targetHandler
    nT (sptToAList targetFirst) lT optT restT targetRoots targetPerm
    ⟨by rw [←targetShape]; exact targetKeys,targetRootRead⟩
  change targetStack = WordSemStackFrame.stackFrame nT (sptToAList targetFirst) lT optT :: restT at targetShape
  have rootValues : lS.map Prod.snd = lT.map Prod.snd := by
    rw [sourceShape,targetShape] at values
    exact ((WordSemStackEq.sFrameValEqDef2 _ _ _ _ _ _ _ _).mp values.2).1
  have keyMap : lT.map Prod.fst = (lS.map Prod.fst).map f := by
    rw [←targetRootKeys.1,←Flapjack.WordAlloc.keyMapImplies f sourceRoots targetRoots rootMap,
      sourceRootKeys.1]
  have keysDomain := Flapjack.WordAlloc.envToListKeys second source.permute
  rw [sourceRootRead] at keysDomain
  have inSecond : ∀ key ∈ lS.map Prod.fst, sptDomain second key := by
    intro key member
    rw [←sourceRootKeys.1] at member
    rw [←keysDomain]
    exact member
  refine ⟨popped,targetPopped,sourcePop,targetPop,frame,?_,?_⟩
  · funext key
    apply propext
    have equal := congrFun sourceDomain key
    rw [←equal]
    exact Or.comm
  · intro live
    rw [sourceLocals,targetLocals]
    have zip : lS = (lS.map Prod.fst).zip (lT.map Prod.snd) := by
      rw [←rootValues]
      have pairs : ∀ entries : List (Nat × WordLocW width),
          (entries.map Prod.fst).zip (entries.map Prod.snd) = entries := by
        intro entries
        induction entries with
        | nil => rfl
        | cons pair rest ih => simp [ih]
      exact (pairs lS).symm
    rw [zip]
    apply Flapjack.WordAlloc.allocLocalsRel f first targetFirst (lS.map Prod.fst) lT keyMap
      _ firstRelated live
    intro a b inA inB equal
    apply injective a b _ _ equal
    · exact inA.elim (fun h => Or.inr (inSecond a h)) Or.inl
    · exact inB.elim (fun h => Or.inr (inSecond b h)) Or.inl

/-- Flapjack-specific original8477-8550 restricted SSA reconstruction.
Actual popped cut domain and remapped lookup relation establish every conjunct
of the restricted SSA map, including defined lookups and original source bounds.
These internal lookup/domain facts are derived by returningPopCutRelation; no
output SSA relation is assumed. No standalone HOL declaration or tag exists. -/
theorem returningCutSSA {α : Type} (next : Nat) (ssa : Spt Nat)
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


/-- Flapjack-specific original8575-8590 physical return reread factoring.
The actual rename's physical lookup preservation and duplicate-free convention
writes derive the getVars result after retMov; no successful target read is
assumed. No standalone HOL declaration exists. -/
theorem returningRestoreRegistersRead {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (names : Spt Unit) (counter count : Nat) (values : List (WordLocW width))
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (length : values.length = count) (nonphysical : ¬ isPhyVar (counter+2))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let registers := (List.range count).map (fun index => 2*(index+1))
    let prepared := WordSemStateFiniteExact.setVars registers values target
    let (move,mapOut,nextOut) := listNextVarRenameMove (width := width)
      (sptInter ssa names) (counter+2) ((sptToAList names).map Prod.fst)
    let (result,targetOut) := WordSemStateFiniteExact.evaluate move prepared
    result = none ∧ ssaLocalsRel nextOut mapOut source.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source targetOut ∧
      WordSemStateFiniteExact.getVars registers targetOut = some values := by
  let registers := (List.range count).map (fun index => 2*(index+1))
  have physical : ∀ register ∈ registers, isPhyVar register := by
    intro register member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    simp [isPhyVar]
  have distinct : registers.Nodup := by
    apply List.Nodup.map _ List.nodup_range
    intro x y equal
    change 2*(x+1) = 2*(y+1) at equal
    omega
  have lengths : registers.length = values.length := by simp [registers,length]
  have inserted := ssaLocalsRelIgnoreListInsert counter (sptInter ssa names)
    source target registers values
    ⟨ssaMapOKInter counter ssa names valid,related,physical,lengths⟩
  have present : ∀ key ∈ (sptToAList names).map Prod.fst, sptDomain source.locals key := by
    intro key member
    rw [sourceDomain]
    exact (sptMemMapFstToAList names key).mp member
  have restored := listNextVarRenameMovePreserve source (sptInter ssa names) (counter+2)
    ((sptToAList names).map Prod.fst) (WordSemStateFiniteExact.setVars registers values target)
    ⟨ssaLocalsRelMore counter _ _ _ (counter+2) ⟨inserted,by omega⟩,
      present,sptAllDistinctMapFstToAList _,
      ssaMapOKMore counter _ (counter+2) ⟨ssaMapOKInter counter ssa names valid,by omega⟩,frame⟩
  dsimp only at restored ⊢
  refine ⟨restored.1,restored.2.1,restored.2.2.1,?_⟩
  apply ssaGetVarsOfZip registers values _ lengths
  intro register value member
  rw [restored.2.2.2.1 nonphysical register (physical register (List.of_mem_zip member).1)]
  exact ssaAlistInsertLookupMember registers values target.locals distinct lengths register value member

/-- Flapjack-specific original8590-8610 actual continuation result binding.
The internal return-register read and renamed cut SSA derive the generated
copy Move and the source/target result-variable SSA relation. No target run or
post-relation premise; the continuation IH is applied by the full case. -/
theorem returningBindResults {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (names : List Nat) (values : List (WordLocW width))
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (valid : ssaMapOK next ssa) (nonphysical : ¬ isPhyVar next)
    (below : ∀ name ∈ names, name < next) (distinct : names.Nodup)
    (lengths : names.length = values.length)
    (read : WordSemStateFiniteExact.getVars
      ((List.range names.length).map (fun index => 2*(index+1))) target = some values)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (outputs,mapOut,nextOut) := listNextVarRename names ssa next
    let registers := (List.range names.length).map (fun index => 2*(index+1))
    WordSemStateFiniteExact.evaluate (.move 1 (outputs.zip registers)) target =
      (none,WordSemStateFiniteExact.setVars outputs values target) ∧
    ssaLocalsRel nextOut mapOut
      (WordSemStateFiniteExact.setVars names values source).locals
      (WordSemStateFiniteExact.setVars outputs values target).locals ∧
    Flapjack.WordAlloc.wordStateEqRel (WordSemStateFiniteExact.setVars names values source)
      (WordSemStateFiniteExact.setVars outputs values target) := by
  generalize produced : listNextVarRename names ssa next = output
  rcases output with ⟨outputs,mapOut,nextOut⟩
  have arithmetic := listNextVarRenameLemma1 names ssa next outputs mapOut nextOut produced
  have outputLength : outputs.length = names.length := by rw [arithmetic.2.1]; simp
  have matching := ssaLocalsRelListNextVarRename names ssa next source.locals target.locals
    outputs mapOut nextOut values ⟨produced,related,valid,lengths,below,distinct,nonphysical⟩
  dsimp only
  refine ⟨?_,matching,frame⟩
  have zipLengths : outputs.length =
      ((List.range names.length).map (fun index => 2*(index+1))).length := by
    simpa using outputLength
  simp only [WordSemStateFiniteExact.evaluate,
    List.map_fst_zip (Nat.le_of_eq zipLengths),
    List.map_snd_zip (Nat.le_of_eq zipLengths.symm),
    arithmetic.1,if_true,read]

end Flapjack.Compiler.Backend.WordAlloc
