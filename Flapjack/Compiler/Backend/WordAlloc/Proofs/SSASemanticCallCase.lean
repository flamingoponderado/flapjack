import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallReturn
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSemanticHelpers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameShiftedProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectRight

namespace Flapjack.Compiler.Backend.WordAlloc

open Classical

/-!
Full returning Call semantic assembly in progress on flapjack-sola-callreturn.7.
The handler NONE case must keep the original six premises and only the actual
return-continuation IH. The local guards below are internal compiler/evaluator
algebra, not independently claimed HOL ports. No full case tag is installed
before the complete source-shaped statement is proved.
-/

private theorem returningDestinationGuard (dest : Option Nat) (args : List Nat)
    (ssa : Spt Nat) :
    wordSemBadDestArgs dest
      ((List.range (args.map (optionLookup ssa)).length).map (fun index => 2*(index+1))) =
      wordSemBadDestArgs dest args := by
  cases args <;> simp [wordSemBadDestArgs]

private theorem returningConventionDistinct (count : Nat) :
    ((List.range count).map (fun index => 2*(index+1))).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro x y equal
  change 2*(x+1) = 2*(y+1) at equal
  omega


private def returningPost {width : Nat} [NeZero width] {C F : Type}
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target : Option (WordSemResult width) × WordSemStateFiniteExact width C F) : Prop :=
  if source.1 = some .error then True else
    source.1 = target.1 ∧ Flapjack.WordAlloc.wordStateEqRel source.2 target.2 ∧
      match source.1 with
      | none => ssaLocalsRel next map source.2.locals target.2.locals
      | some (.break n) => match tables[n]? with
        | none => True
        | some (dest,_,exits) => Flapjack.WordAlloc.strongLocalsRel
            (optionLookup dest) (sptDomain exits) source.2.locals target.2.locals
      | some (.continue n) => match tables[n]? with
        | none => True
        | some (dest,entries,_) => Flapjack.WordAlloc.strongLocalsRel
            (optionLookup dest) (sptDomain entries) source.2.locals target.2.locals
      | some _ => source.2.locals = target.2.locals

/-- Private successful-return branch assembly. Every producer is an actual
compiler equation, and the pop-domain/SSA facts are internal callee facts.
The generated prefix evaluations and the continuation simulation are derived;
no target run or desired post relation is a premise of the full Call case. -/
private theorem returningGeneralContinuation {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (names : Spt Unit) (counter : Nat) (returns : List Nat) (values : List (WordLocW width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec width)) (moveMap : Spt Nat) (moveNext bindNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec width)) (finalMap : Spt Nat) (finalNext : Nat)
    (moveProduced : listNextVarRenameMove (width := width) (sptInter ssa names) (counter+2)
      ((sptToAList names).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap bindNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,finalMap,finalNext))
    (bindingIncrease : moveNext ≤ bindNext) (bindingClass : isAllocVar bindNext)
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (lengths : returns.length = values.length) (distinct : returns.Nodup)
    (below : ∀ name ∈ returns, name < counter)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) (tableValid : ltOK tables)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation body st ct map na lt) :
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let prepared := WordSemStateFiniteExact.setVars registers values target
    ∃ permutation : Nat → Nat → Nat,
      let sourceRun := WordSemStateFiniteExact.evaluate body
        {WordSemStateFiniteExact.setVars returns values source with permute := permutation}
      let targetRun := WordSemStateFiniteExact.evaluate
        (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) prepared
      if sourceRun.1 = some .error then True else
        sourceRun.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        match sourceRun.1 with
        | none => ssaLocalsRel finalNext finalMap sourceRun.2.locals targetRun.2.locals
        | some (.break n) => match tables[n]? with
          | none => True
          | some (map,_,exits) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup map) (sptDomain exits) sourceRun.2.locals targetRun.2.locals
        | some (.continue n) => match tables[n]? with
          | none => True
          | some (map,entries,_) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup map) (sptDomain entries) sourceRun.2.locals targetRun.2.locals
        | some _ => sourceRun.2.locals = targetRun.2.locals := by
  classical
  let registers := (List.range returns.length).map (fun index => 2*(index+1))
  let prepared := WordSemStateFiniteExact.setVars registers values target
  have allocated := isStackVarFlip counter stackClass
  have nonphysical : ¬ isPhyVar (counter+2) := ((conventionPartitions _).2.2.mp allocated).1
  have restoration := returningRestoreRegistersRead source target ssa names counter returns.length
    values related valid sourceDomain lengths.symm nonphysical frame
  rw [moveProduced] at restoration
  dsimp only at restoration
  rcases run : WordSemStateFiniteExact.evaluate retMove prepared with ⟨result,refreshed⟩
  change WordSemStateFiniteExact.evaluate retMove prepared = _ at run
  change (WordSemStateFiniteExact.evaluate retMove prepared).1 = none ∧
    ssaLocalsRel moveNext moveMap source.locals (WordSemStateFiniteExact.evaluate retMove prepared).2.locals ∧
    Flapjack.WordAlloc.wordStateEqRel source (WordSemStateFiniteExact.evaluate retMove prepared).2 ∧
    WordSemStateFiniteExact.getVars registers (WordSemStateFiniteExact.evaluate retMove prepared).2 =
      some values at restoration
  rw [run] at restoration
  dsimp only at restoration
  obtain ⟨normal,refreshedRelated,refreshedFrame,reread⟩ := restoration
  subst result
  have moveProps := listNextVarRenameMoveProps _ (sptInter ssa names) (counter+2)
    retMove moveMap moveNext moveProduced
    ⟨Or.inl allocated,ssaMapOKMore counter _ (counter+2)
      ⟨ssaMapOKInter counter ssa names valid,by omega⟩⟩
  have bindingRelated := ssaLocalsRelMore moveNext moveMap source.locals refreshed.locals bindNext
    ⟨refreshedRelated,bindingIncrease⟩
  have bindingValid := ssaMapOKMore moveNext moveMap bindNext ⟨moveProps.2.2.2,bindingIncrease⟩
  have retProps := listNextVarRenameProps returns moveMap bindNext renamed retMap retNext
    renameProduced ⟨Or.inl bindingClass,bindingValid⟩
  have movedBelow : ∀ name ∈ returns, name < bindNext := by
    intro name member
    have := below name member
    omega
  have binding := returningBindResults source refreshed moveMap bindNext returns values
    bindingRelated bindingValid ((conventionPartitions _).2.2.mp bindingClass).1
    movedBelow distinct lengths reread refreshedFrame
  rw [renameProduced] at binding
  dsimp only at binding
  obtain ⟨copyRun,copyRelated,copyFrame⟩ := binding
  have boundIncrease : counter ≤ retNext := by omega
  have finalBodyBounds : everyVarHOL (fun key => decide (key < retNext)) body = true := Flapjack.everyVarMono _ body _
    ⟨fun key bound => by
      simp only [decide_eq_true_eq] at bound ⊢
      exact Nat.lt_of_lt_of_le bound boundIncrease,bodyBounds⟩
  obtain ⟨permutation,post⟩ := bodyIH
    (WordSemStateFiniteExact.setVars returns values source)
    (WordSemStateFiniteExact.setVars renamed values refreshed) retMap retNext tables
    ⟨copyFrame,copyRelated,retProps.2.1 bindingClass,finalBodyBounds,retProps.2.2.2,tableValid⟩
  refine ⟨permutation,?_⟩
  dsimp only
  rw [evaluateSeqCollapse _ _ _ _ run,evaluateSeqCollapse _ _ _ _ copyRun]
  dsimp only [ssaSimulation] at post
  rw [bodyProduced] at post
  exact post


/-- Specialization to the immediate result binder used by returning Call without a handler. -/
private theorem returningNormalContinuation {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (names : Spt Unit) (counter : Nat) (returns : List Nat) (values : List (WordLocW width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec width)) (moveMap : Spt Nat) (moveNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec width)) (finalMap : Spt Nat) (finalNext : Nat)
    (moveProduced : listNextVarRenameMove (width := width) (sptInter ssa names) (counter+2)
      ((sptToAList names).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap moveNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,finalMap,finalNext))
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (lengths : returns.length = values.length) (distinct : returns.Nodup)
    (below : ∀ name ∈ returns, name < counter)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) (tableValid : ltOK tables)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation body st ct map na lt) :
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let prepared := WordSemStateFiniteExact.setVars registers values target
    ∃ permutation : Nat → Nat → Nat,
      let sourceRun := WordSemStateFiniteExact.evaluate body
        {WordSemStateFiniteExact.setVars returns values source with permute := permutation}
      let targetRun := WordSemStateFiniteExact.evaluate
        (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) prepared
      if sourceRun.1 = some .error then True else
        sourceRun.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        match sourceRun.1 with
        | none => ssaLocalsRel finalNext finalMap sourceRun.2.locals targetRun.2.locals
        | some (.break n) => match tables[n]? with
          | none => True
          | some (map,_,exits) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup map) (sptDomain exits) sourceRun.2.locals targetRun.2.locals
        | some (.continue n) => match tables[n]? with
          | none => True
          | some (map,entries,_) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup map) (sptDomain entries) sourceRun.2.locals targetRun.2.locals
        | some _ => sourceRun.2.locals = targetRun.2.locals := by
  have allocated := isStackVarFlip counter stackClass
  have moveProps := listNextVarRenameMoveProps _ (sptInter ssa names) (counter+2)
    retMove moveMap moveNext moveProduced
    ⟨Or.inl allocated,ssaMapOKMore counter _ (counter+2)
      ⟨ssaMapOKInter counter ssa names valid,by omega⟩⟩
  exact returningGeneralContinuation body source target ssa names counter returns values tables
    retMove moveMap moveNext moveNext renamed retMap retNext compiled finalMap finalNext
    moveProduced renameProduced bodyProduced (Nat.le_refl _) (moveProps.2.1 allocated)
    related valid stackClass sourceDomain lengths distinct below bodyBounds frame tableValid bodyIH


/-- Internal successful exception continuation: native retMove preserves
physical register 2, and the later nextVarRename binds its value before the
actual handler compiler. The full Call case derives all internal inputs. -/
private theorem returningExceptionContinuation {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (names : Spt Unit) (counter name : Nat) (value : WordLocW width)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec width)) (moveMap : Spt Nat) (moveNext bindNext : Nat)
    (renamed : Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec width)) (finalMap : Spt Nat) (finalNext : Nat)
    (moveProduced : listNextVarRenameMove (width := width) (sptInter ssa names) (counter+2)
      ((sptToAList names).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : nextVarRename name moveMap bindNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,finalMap,finalNext))
    (bindingIncrease : moveNext ≤ bindNext) (bindingClass : isAllocVar bindNext)
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (below : name < counter)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) (tableValid : ltOK tables)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation body st ct map na lt) :
    ∃ permutation : Nat → Nat → Nat,
      returningPost finalMap finalNext tables
        (WordSemStateFiniteExact.evaluate body
          {WordSemStateFiniteExact.setVar name value source with permute := permutation})
        (WordSemStateFiniteExact.evaluate (.seq retMove (.seq (.move 1 [(renamed,2)]) compiled))
          (WordSemStateFiniteExact.setVar 2 value target)) := by
  have listProduced : listNextVarRename [name] moveMap bindNext = ([renamed],retMap,retNext) := by
    simp only [listNextVarRename,renameProduced]
  have continuation := returningGeneralContinuation body source target ssa names counter [name] [value]
    tables retMove moveMap moveNext bindNext [renamed] retMap retNext compiled finalMap finalNext
    moveProduced listProduced bodyProduced bindingIncrease bindingClass related valid stackClass
    sourceDomain rfl (by simp) (by simpa using below) bodyBounds frame tableValid bodyIH
  exact continuation


/-- Private callee-outcome assembly for the no-handler case. Internal cuts,
root ordering and entry alignment are obtained from the original six premises
before this branch; actual target body execution is proved by stack-swap. -/
private theorem returningCalleeOutcomes {width : Nat} [NeZero width] {C F : Type}
    (body callee : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (counter : Nat) (firstNames secondNames : Spt Unit)
    (first second targetFirst targetSecond : Spt (WordLocW width))
    (args : List (WordLocW width)) (size : Option Nat)
    (returns : List Nat) (l1 l2 : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec width)) (moveMap : Spt Nat) (moveNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec width)) (finalMap : Spt Nat) (finalNext : Nat)
    (moveProduced : listNextVarRenameMove (width := width) (sptInter ssa (sptUnion firstNames secondNames))
      (counter+2) ((sptToAList (sptUnion firstNames secondNames)).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap moveNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,finalMap,finalNext))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (firstDomain : sptDomain first = sptDomain firstNames)
    (secondDomain : sptDomain second = sptDomain secondNames)
    (mapped : ∀ key, sptDomain (sptUnion firstNames secondNames) key → sptDomain ssa key)
    (cutBounds : ∀ key, sptDomain (sptUnion firstNames secondNames) key → key < counter)
    (below : ∀ name ∈ returns, name < counter) (distinct : returns.Nodup)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (tableValid : ltOK tables)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa) (sptDomain first) first targetFirst)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) → optionLookup ssa a = optionLookup ssa b → a = b)
    (sourceRoots targetRoots : List (Nat × WordLocW width)) (sourcePerm targetPerm : Nat → Nat → Nat)
    (sourceRootRead : wordSemEnvToList second source.permute = (sourceRoots,sourcePerm))
    (targetRootRead : wordSemEnvToList targetSecond target.permute = (targetRoots,targetPerm))
    (rootMap : sourceRoots.map (fun (key,value) => (optionLookup ssa key,value)) = targetRoots)
    (entry : {WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (first,second) none source) with stack :=
        (WordSemStateFiniteExact.callEnv args size
          (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none target)).stack} =
      WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none target))
    (stackValues : WordSemStackEq.sValEq
      (WordSemStateFiniteExact.pushEnv (first,second) none source).stack
      (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none target).stack)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation body st ct map na lt) :
    let sourceEntry := WordSemStateFiniteExact.callEnv args size
      (WordSemStateFiniteExact.pushEnv (first,second) none source)
    let targetEntry := WordSemStateFiniteExact.callEnv args size
      (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none target)
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let continuation := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
    ∃ permutation : Nat → Nat → Nat,
      returningPost finalMap finalNext tables
        (Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) none
          ((WordSemStateFiniteExact.evaluate callee sourceEntry).1,
            {(WordSemStateFiniteExact.evaluate callee sourceEntry).2 with permute := permutation}))
        (Flapjack.WordAlloc.callRetTail registers continuation l1 l2 (targetFirst,targetSecond) none
          (WordSemStateFiniteExact.evaluate callee targetEntry)) := by
  let sourceEntry := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (first,second) none source)
  let targetEntry := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none target)
  let registers := (List.range returns.length).map (fun index => 2*(index+1))
  let continuation := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
  have transport := WordSemStackEq.evaluateStackSwap callee sourceEntry
  unfold WordSemStackEq.stackSwapPost at transport
  rcases sourceRun : WordSemStateFiniteExact.evaluate callee sourceEntry with ⟨result,returned⟩
  rw [sourceRun] at transport
  dsimp only
  rw [sourceRun]
  dsimp only
  have targetTransport : ∀ result,
      WordSemStateFiniteExact.evaluate callee {sourceEntry with stack := targetEntry.stack} = result →
      WordSemStateFiniteExact.evaluate callee targetEntry = result := by
    intro result run
    rw [entry] at run
    exact run
  have sameStack : source.stack = target.stack := frame.2.2.2.1.symm
  cases result with
  | none => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,returningPost]⟩
  | some result =>
    cases result with
    | error => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,returningPost]⟩
    | «break» n => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,returningPost]⟩
    | «continue» n => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,returningPost]⟩
    | timeOut =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,returningPost,Flapjack.WordAlloc.wordStateEqRel]
    | notEnoughSpace =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,returningPost,Flapjack.WordAlloc.wordStateEqRel]
    | finalFfi event =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,returningPost,Flapjack.WordAlloc.wordStateEqRel]
    | exception x y =>
      have sourceShape : sourceEntry.stack =
          .stackFrame source.localsSize (sptToAList first) sourceRoots none :: source.stack := by
        simp only [sourceEntry,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv,sourceRootRead]
      have targetShape : targetEntry.stack =
          .stackFrame target.localsSize (sptToAList targetFirst) targetRoots none :: source.stack := by
        simp only [targetEntry,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv,targetRootRead]
        rw [sameStack]
      have actual := returningNoHandlerException callee sourceEntry targetEntry returned source.stack
        source.localsSize target.localsSize (sptToAList first) sourceRoots (sptToAList targetFirst)
        targetRoots x y sourceShape targetShape entry stackValues sourceRun
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,returningPost,Flapjack.WordAlloc.wordStateEqRel]
    | result x values =>
      by_cases badReturn : x ≠ .loc l1 l2 ∨ values.length ≠ returns.length
      · refine ⟨returned.permute,?_⟩
        rw [Flapjack.WordAlloc.callRetTail_result_err _ _ _ _ _ _ _ _ _ badReturn]
        simp [returningPost]
      have targetGood : ¬ (x ≠ .loc l1 l2 ∨ values.length ≠ registers.length) := by
        simpa [registers] using badReturn
      obtain ⟨sourceKeys,_,swapped⟩ := transport
      obtain ⟨targetStack,swappedRun,valuesEqual,targetKeys⟩ := swapped targetEntry.stack stackValues
      have actual := targetTransport _ swappedRun
      obtain ⟨popped,targetPopped,sourcePop,targetPop,poppedFrame,poppedDomain,poppedValues⟩ :=
        returningPopCutRelation source target returned first second targetFirst targetSecond none none
          targetStack (optionLookup ssa) sourceRoots targetRoots sourcePerm targetPerm sameStack
          sourceRootRead targetRootRead rootMap firstRelated injective sourceKeys targetKeys valuesEqual
      have sourceNames : sptDomain popped.locals = sptDomain (sptUnion firstNames secondNames) := by
        rw [poppedDomain,sptDomain_sptUnion,firstDomain,secondDomain]
      have restricted := returningCutSSA counter ssa (sptUnion firstNames secondNames)
        popped.locals targetPopped.locals mapped sourceNames (poppedValues _) cutBounds
      have sourceUnion : sptDomainEqUnion popped.locals first second := by
        intro key
        change sptDomain popped.locals key ↔ sptDomain first key ∨ sptDomain second key
        have equality := congrFun poppedDomain key
        rw [equality]
      obtain ⟨_,_,_,_,_,otherPop,otherPopRun,_,targetDomain,_⟩ :=
        WordSemStackEq.pushEnvPopEnvSKeyEq (targetFirst,targetSecond) none target
          {returned with stack := targetStack} targetKeys
      have samePop : otherPop = targetPopped := by
        rw [targetPop] at otherPopRun
        exact Option.some.inj otherPopRun.symm
      rw [samePop] at targetDomain
      have targetUnion : sptDomainEqUnion targetPopped.locals targetFirst targetSecond := by
        intro key
        change sptDomain targetPopped.locals key ↔ sptDomain targetFirst key ∨ sptDomain targetSecond key
        have equality := congrFun targetDomain key
        rw [←equality]
        exact Or.comm
      have lengths : returns.length = values.length := by
        have := (not_or.mp badReturn).2
        omega
      obtain ⟨permutation,post⟩ := returningNormalContinuation body popped targetPopped ssa
        (sptUnion firstNames secondNames) counter returns values tables retMove moveMap moveNext
        renamed retMap retNext compiled finalMap finalNext moveProduced renameProduced bodyProduced
        restricted valid stackClass sourceNames lengths distinct below bodyBounds poppedFrame tableValid bodyIH
      refine ⟨permutation,?_⟩
      rw [actual,
        Flapjack.WordAlloc.callRetTail_result_pop _ _ _ _ _ _ _ _ _ {popped with permute := permutation}
          badReturn (by rw [Flapjack.WordAlloc.popEnv_withPermute,sourcePop]; rfl),
        Flapjack.WordAlloc.callRetTail_result_pop _ _ _ _ _ _ _ _ _ targetPopped targetGood targetPop]
      rw [if_pos sourceUnion,if_pos targetUnion]
      exact post



/-- Internal handler-present exception restoration from total stack swapping.
The selected frame is derived from the actual pushed handler position. Root
keys and values reconstruct restored locals; no target evaluation is assumed. -/
private theorem returningHandlerException {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width))
    (callee targetCallee returned : WordSemStateFiniteExact width C F)
    (original : List (WordSemStackFrame width)) (size : Option Nat)
    (first second targetFirst targetSecond : Spt (WordLocW width))
    (roots targetRoots : List (Nat × WordLocW width))
    (oldHandler l1 l2 : Nat) (x y : WordLocW width) (f : Nat → Nat)
    (sourceShape : callee.stack = .stackFrame size (sptToAList first) roots
      (some (oldHandler,l1,l2)) :: original)
    (targetShape : targetCallee.stack = .stackFrame size (sptToAList targetFirst) targetRoots
      (some (oldHandler,l1,l2)) :: original)
    (handlerPosition : callee.handler = original.length)
    (entry : {callee with stack := targetCallee.stack} = targetCallee)
    (values : WordSemStackEq.sValEq callee.stack targetCallee.stack)
    (rootKeys : ∀ key, key ∈ roots.map Prod.fst ↔ sptDomain second key)
    (targetRootKeys : ∀ key, key ∈ targetRoots.map Prod.fst ↔ sptDomain targetSecond key)
    (rootMap : roots.map (fun (key,value) => (f key,value)) = targetRoots)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel f (sptDomain first) first targetFirst)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) → f a = f b → a = b)
    (run : WordSemStateFiniteExact.evaluate body callee = (some (.exception x y),returned)) :
    ∃ targetReturned,
      WordSemStateFiniteExact.evaluate body targetCallee = (some (.exception x y),targetReturned) ∧
      Flapjack.WordAlloc.wordStateEqRel returned targetReturned ∧
      sptDomain returned.locals = (fun key => sptDomain first key ∨ sptDomain second key) ∧
      sptDomain targetReturned.locals = (fun key => sptDomain targetFirst key ∨ sptDomain targetSecond key) ∧
      (∀ live, Flapjack.WordAlloc.strongLocalsRel f live returned.locals targetReturned.locals) := by
  have transport := WordSemStackEq.evaluateStackSwap body callee
  unfold WordSemStackEq.stackSwapPost at transport
  rw [run] at transport
  obtain ⟨_,e0,e,n,tail,m,locals,handlerFrame,_,⟨keys,localShape⟩,
    tailKeys,returnedHandler,swapped⟩ := transport
  have length : callee.handler+1 = callee.stack.length := by
    rw [handlerPosition,sourceShape]
    simp
  rw [WordSemStackEq.lastNLengthCond _ _ length,sourceShape] at handlerFrame
  simp only [List.cons.injEq,WordSemStackFrame.stackFrame.injEq,Option.some.injEq] at handlerFrame
  obtain ⟨⟨rfl,rfl,rfl,rfl⟩,rfl⟩ := handlerFrame
  have targetFrame : wordSemLastN (callee.handler+1) targetCallee.stack =
      .stackFrame size (sptToAList targetFirst) targetRoots (some (oldHandler,l1,l2)) :: original := by
    rw [WordSemStackEq.lastNLengthCond _ _ (by rw [handlerPosition,targetShape]; simp)]
    exact targetShape
  obtain ⟨stack,restored,actual,⟨newLocals,newKeys,newShape,sameValues⟩,stackValues,stackKeys⟩ :=
    swapped targetCallee.stack (sptToAList targetFirst) targetRoots original ⟨targetFrame,values⟩
  have stackEqual : stack = returned.stack :=
    (WordSemStackEq.sValAndKeyEq _ _ ⟨stackValues,
      WordSemStackEq.sKeyEqTrans _ _ _ ⟨tailKeys,stackKeys⟩⟩).symm
  rw [entry,stackEqual,←returnedHandler] at actual
  refine ⟨{returned with locals := restored},actual,?_,?_,?_,?_⟩
  · simp [Flapjack.WordAlloc.wordStateEqRel]
  · rw [localShape,sptDomain_sptUnion]
    funext key
    apply propext
    simp only [sptDomainFromAList]
    rw [←keys,rootKeys]
    simpa only [sptMemMapFstToAList] using (Or.comm :
      (sptDomain second key ∨ sptDomain first key) ↔ (sptDomain first key ∨ sptDomain second key))
  · change sptDomain restored = _
    rw [newShape,sptDomain_sptUnion]
    funext key
    apply propext
    simp only [sptDomainFromAList]
    rw [←newKeys,targetRootKeys]
    simpa only [sptMemMapFstToAList] using (Or.comm :
      (sptDomain targetSecond key ∨ sptDomain targetFirst key) ↔
        (sptDomain targetFirst key ∨ sptDomain targetSecond key))
  · have keyMap : newLocals.map Prod.fst = (locals.map Prod.fst).map f := by
      rw [←newKeys,←Flapjack.WordAlloc.keyMapImplies f roots targetRoots rootMap,keys]
    have zip : locals = (locals.map Prod.fst).zip (newLocals.map Prod.snd) := by
      rw [←sameValues]
      have pairs : ∀ entries : List (Nat × WordLocW width),
          (entries.map Prod.fst).zip (entries.map Prod.snd) = entries := by
        intro entries
        induction entries with
        | nil => rfl
        | cons pair rest ih => simp [ih]
      exact (pairs locals).symm
    intro live
    rw [localShape,newShape,zip]
    apply Flapjack.WordAlloc.allocLocalsRel f first targetFirst (locals.map Prod.fst) newLocals
      keyMap _ firstRelated live
    intro a b inA inB equal
    apply injective a b _ _ equal
    · exact inA.elim (fun h => Or.inr ((rootKeys a).mp (keys ▸ h))) Or.inl
    · exact inB.elim (fun h => Or.inr ((rootKeys b).mp (keys ▸ h))) Or.inl

/-- Internal native Seq normalization, with clock fix derived from evaluation. -/
private theorem returningEvaluateSeqNative {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq first second) state =
      match WordSemStateFiniteExact.evaluate first state with
      | (none, after) => WordSemStateFiniteExact.evaluate second after
      | (some result, after) => (some result, after) := by
  simp only [WordSemStateFiniteExact.evaluate,
    WordSemStateFiniteExact.fix_clock_evaluate]
  cases WordSemStateFiniteExact.evaluate first state with
  | mk result after => cases result <;> rfl


/-- Internal returning-handler reconciliation composition. Its move specification
is derived from native fixInconsistenciesCorrectL/R inside the full handler case;
it is not an extra premise of a HOL correctness statement. -/
private theorem returningAppendReconciliation {width : Nat} [NeZero width] {C F : Type}
    (sourceRun : Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (target : WordSemStateFiniteExact width C F)
    (compiled moves : WordLangProgHOL (BitVec width))
    (mapOut finalMap : Spt Nat) (nextOut nextFinal : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (moveSpec : ∀ (sourceAfter targetAfter : WordSemStateFiniteExact width C F),
      ssaLocalsRel nextOut mapOut sourceAfter.locals targetAfter.locals →
      let run := WordSemStateFiniteExact.evaluate moves targetAfter
      run.1 = none ∧ ssaLocalsRel nextFinal finalMap sourceAfter.locals run.2.locals ∧
        Flapjack.WordAlloc.wordStateEqRel targetAfter run.2)
    (post : returningPost mapOut nextOut tables sourceRun
      (WordSemStateFiniteExact.evaluate compiled target)) :
    returningPost finalMap nextFinal tables sourceRun
      (WordSemStateFiniteExact.evaluate (.seq compiled moves) target) := by
  classical
  rcases sourceRun with ⟨result,sourceAfter⟩
  unfold returningPost at post ⊢
  cases result with
  | none =>
    cases targetEval : WordSemStateFiniteExact.evaluate compiled target with
    | mk targetResult targetAfter =>
      simp only [targetEval,reduceCtorEq,if_false] at post
      have equal : targetResult = none := post.1.symm
      subst targetResult
      have moved := moveSpec sourceAfter targetAfter post.2.2
      cases moveEval : WordSemStateFiniteExact.evaluate moves targetAfter with
      | mk moveResult moveAfter =>
        simp only [moveEval] at moved
        have equal : moveResult = none := moved.1
        subst moveResult
        rw [evaluateSeqCollapse compiled moves target targetAfter targetEval,moveEval]
        simp only [reduceCtorEq,if_false]
        refine ⟨trivial,?_,moved.2.1⟩
        simp_all [Flapjack.WordAlloc.wordStateEqRel]
  | some result =>
    by_cases error : result = .error
    · subst result
      simp
    · cases targetEval : WordSemStateFiniteExact.evaluate compiled target with
      | mk targetResult targetAfter =>
        have noError : (some result : Option (WordSemResult width)) ≠ some .error := by simpa using error
        simp only [if_neg noError,targetEval] at post
        have equal : targetResult = some result := post.1.symm
        subst targetResult
        simp only [returningEvaluateSeqNative,targetEval,if_neg noError]
        cases result <;> try (simpa only using post)


/-- Internal complete callee outcomes for the handler-present Call assembly. -/
private theorem returningHandlerCalleeOutcomes {width : Nat} [NeZero width] {C F : Type}
    (body handlerBody callee : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (counter : Nat) (firstNames secondNames : Spt Unit)
    (first second targetFirst targetSecond : Spt (WordLocW width))
    (args : List (WordLocW width)) (size : Option Nat)
    (returns : List Nat) (l1 l2 exceptionVar handlerL1 handlerL2 : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec width)) (moveMap : Spt Nat) (moveNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec width)) (leftMap : Spt Nat) (leftNext : Nat)
    (exceptionOut : Nat) (exceptionMap : Spt Nat) (exceptionNext : Nat)
    (compiledException : WordLangProgHOL (BitVec width)) (rightMap : Spt Nat) (rightNext : Nat)
    (prio : Option (Unit ⊕ Unit)) (retCons excCons : WordLangProgHOL (BitVec width))
    (finalMap : Spt Nat) (finalNext : Nat)
    (exceptionProduced : nextVarRename exceptionVar moveMap leftNext =
      (exceptionOut,exceptionMap,exceptionNext))
    (handlerProduced : ssaCcTrans handlerBody exceptionMap exceptionNext tables =
      (compiledException,rightMap,rightNext))
    (reconcileProduced : fixInconsistencies prio leftMap rightMap rightNext =
      (retCons,excCons,finalNext,finalMap))
    (leftAllocated : isAllocVar leftNext) (rightAllocated : isAllocVar rightNext)
    (leftValid : ssaMapOK leftNext leftMap) (rightValid : ssaMapOK rightNext rightMap)
    (moveIncrease : moveNext ≤ leftNext) (leftIncrease : leftNext ≤ rightNext)
    (exceptionBelow : exceptionVar < counter)
    (handlerBounds : everyVarHOL (fun key => decide (key < counter)) handlerBody = true)
    (moveProduced : listNextVarRenameMove (width := width) (sptInter ssa (sptUnion firstNames secondNames))
      (counter+2) ((sptToAList (sptUnion firstNames secondNames)).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap moveNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,leftMap,leftNext))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (firstDomain : sptDomain first = sptDomain firstNames)
    (secondDomain : sptDomain second = sptDomain secondNames)
    (mapped : ∀ key, sptDomain (sptUnion firstNames secondNames) key → sptDomain ssa key)
    (cutBounds : ∀ key, sptDomain (sptUnion firstNames secondNames) key → key < counter)
    (below : ∀ name ∈ returns, name < counter) (distinct : returns.Nodup)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (tableValid : ltOK tables)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa) (sptDomain first) first targetFirst)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) → optionLookup ssa a = optionLookup ssa b → a = b)
    (sourceRoots targetRoots : List (Nat × WordLocW width)) (sourcePerm targetPerm : Nat → Nat → Nat)
    (sourceRootRead : wordSemEnvToList second source.permute = (sourceRoots,sourcePerm))
    (targetRootRead : wordSemEnvToList targetSecond target.permute = (targetRoots,targetPerm))
    (rootMap : sourceRoots.map (fun (key,value) => (optionLookup ssa key,value)) = targetRoots)
    (entry : {WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) source) with stack :=
        (WordSemStateFiniteExact.callEnv args size
          (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target)).stack} =
      WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target))
    (stackValues : WordSemStackEq.sValEq
      (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) source).stack
      (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target).stack)
    (handlerIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) handlerBody = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation handlerBody st ct map na lt)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation body st ct map na lt) :
    let sourceEntry := WordSemStateFiniteExact.callEnv args size
      (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) source)
    let targetEntry := WordSemStateFiniteExact.callEnv args size
      (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target)
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let retBody := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
    let continuation := WordLangProgHOL.seq retBody retCons
    let exceptionBody := WordLangProgHOL.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)
    let exceptionContinuation := WordLangProgHOL.seq exceptionBody excCons
    ∃ permutation : Nat → Nat → Nat,
      returningPost finalMap finalNext tables
        (Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2))
          ((WordSemStateFiniteExact.evaluate callee sourceEntry).1,
            {(WordSemStateFiniteExact.evaluate callee sourceEntry).2 with permute := permutation}))
        (Flapjack.WordAlloc.callRetTail registers continuation l1 l2 (targetFirst,targetSecond) (some (2,exceptionContinuation,handlerL1,handlerL2))
          (WordSemStateFiniteExact.evaluate callee targetEntry)) := by
  let sourceEntry := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) source)
  let targetEntry := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target)
  let registers := (List.range returns.length).map (fun index => 2*(index+1))
  let retBody := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
  let continuation := WordLangProgHOL.seq retBody retCons
  let exceptionBody := WordLangProgHOL.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)
  let exceptionContinuation := WordLangProgHOL.seq exceptionBody excCons
  have normalReconcile : ∀ (st ct : WordSemStateFiniteExact width C F),
      ssaLocalsRel leftNext leftMap st.locals ct.locals →
      let run := WordSemStateFiniteExact.evaluate retCons ct
      run.1 = none ∧ ssaLocalsRel finalNext finalMap st.locals run.2.locals ∧
        Flapjack.WordAlloc.wordStateEqRel ct run.2 := by
    intro st ct related
    have fixed := fixInconsistenciesCorrectL rightNext leftMap rightMap prio st ct
      ⟨rightAllocated,ssaMapOKMore leftNext leftMap rightNext ⟨leftValid,leftIncrease⟩⟩
    rw [reconcileProduced] at fixed
    dsimp only at fixed
    exact fixed (ssaLocalsRelMore leftNext leftMap st.locals ct.locals rightNext ⟨related,leftIncrease⟩)
  have exceptionReconcile : ∀ (st ct : WordSemStateFiniteExact width C F),
      ssaLocalsRel rightNext rightMap st.locals ct.locals →
      let run := WordSemStateFiniteExact.evaluate excCons ct
      run.1 = none ∧ ssaLocalsRel finalNext finalMap st.locals run.2.locals ∧
        Flapjack.WordAlloc.wordStateEqRel ct run.2 := by
    intro st ct related
    have fixed := fixInconsistenciesCorrectR rightNext leftMap rightMap prio st ct ⟨rightAllocated,rightValid⟩
    rw [reconcileProduced] at fixed
    dsimp only at fixed
    exact fixed related
  have transport := WordSemStackEq.evaluateStackSwap callee sourceEntry
  unfold WordSemStackEq.stackSwapPost at transport
  rcases sourceRun : WordSemStateFiniteExact.evaluate callee sourceEntry with ⟨result,returned⟩
  rw [sourceRun] at transport
  dsimp only
  rw [sourceRun]
  dsimp only
  have targetTransport : ∀ result,
      WordSemStateFiniteExact.evaluate callee {sourceEntry with stack := targetEntry.stack} = result →
      WordSemStateFiniteExact.evaluate callee targetEntry = result := by
    intro result run
    rw [entry] at run
    exact run
  have sameStack : source.stack = target.stack := frame.2.2.2.1.symm
  cases result with
  | none => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,returningPost]⟩
  | some result =>
    cases result with
    | error => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,returningPost]⟩
    | «break» n => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,returningPost]⟩
    | «continue» n => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,returningPost]⟩
    | timeOut =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,returningPost,Flapjack.WordAlloc.wordStateEqRel]
    | notEnoughSpace =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,returningPost,Flapjack.WordAlloc.wordStateEqRel]
    | finalFfi event =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,returningPost,Flapjack.WordAlloc.wordStateEqRel]
    | exception x y =>
      by_cases badLabel : x ≠ .loc handlerL1 handlerL2
      · refine ⟨returned.permute,?_⟩
        simp [Flapjack.WordAlloc.callRetTail,badLabel,returningPost]
      have sourceShape : sourceEntry.stack = .stackFrame source.localsSize (sptToAList first) sourceRoots
          (some (source.handler,handlerL1,handlerL2)) :: source.stack := by
        simp only [sourceEntry,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv,sourceRootRead]
      have targetShape : targetEntry.stack = .stackFrame source.localsSize (sptToAList targetFirst) targetRoots
          (some (source.handler,handlerL1,handlerL2)) :: source.stack := by
        simp only [targetEntry,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv,targetRootRead]
        rw [frame.2.2.1,frame.2.2.2.1,frame.2.2.2.2.2.2.2.2.2.2.2.1]
      have sourceRootKeys : ∀ key, key ∈ sourceRoots.map Prod.fst ↔ sptDomain second key := by
        have equality := Flapjack.WordAlloc.envToListKeys second source.permute
        rw [sourceRootRead] at equality
        intro key
        exact (congrFun equality key).to_iff
      have targetRootKeys : ∀ key, key ∈ targetRoots.map Prod.fst ↔ sptDomain targetSecond key := by
        have equality := Flapjack.WordAlloc.envToListKeys targetSecond target.permute
        rw [targetRootRead] at equality
        intro key
        exact (congrFun equality key).to_iff
      obtain ⟨targetReturned,actual,returnedFrame,returnedDomain,targetDomain,returnedValues⟩ :=
        returningHandlerException callee sourceEntry targetEntry returned source.stack source.localsSize
          first second targetFirst targetSecond sourceRoots targetRoots source.handler handlerL1 handlerL2 x y
          (optionLookup ssa) sourceShape targetShape (by rfl) entry stackValues sourceRootKeys targetRootKeys
          rootMap firstRelated injective sourceRun
      have sourceNames : sptDomain returned.locals = sptDomain (sptUnion firstNames secondNames) := by
        rw [returnedDomain,sptDomain_sptUnion,firstDomain,secondDomain]
      have restricted := returningCutSSA counter ssa (sptUnion firstNames secondNames)
        returned.locals targetReturned.locals mapped sourceNames (returnedValues _) cutBounds
      have sourceUnion : sptDomainEqUnion returned.locals first second := by
        intro key
        change sptDomain returned.locals key ↔ sptDomain first key ∨ sptDomain second key
        rw [congrFun returnedDomain key]
      have targetUnion : sptDomainEqUnion targetReturned.locals targetFirst targetSecond := by
        intro key
        change sptDomain targetReturned.locals key ↔ sptDomain targetFirst key ∨ sptDomain targetSecond key
        rw [congrFun targetDomain key]
      obtain ⟨permutation,post⟩ := returningExceptionContinuation handlerBody returned targetReturned ssa
        (sptUnion firstNames secondNames) counter exceptionVar y tables retMove moveMap moveNext leftNext
        exceptionOut exceptionMap exceptionNext compiledException rightMap rightNext moveProduced exceptionProduced
        handlerProduced moveIncrease leftAllocated restricted valid stackClass sourceNames exceptionBelow
        handlerBounds returnedFrame tableValid handlerIH
      have composed := returningAppendReconciliation
        (WordSemStateFiniteExact.evaluate handlerBody
          {WordSemStateFiniteExact.setVar exceptionVar y returned with permute := permutation})
        (WordSemStateFiniteExact.setVar 2 y targetReturned) exceptionBody excCons rightMap finalMap
        rightNext finalNext tables exceptionReconcile post
      refine ⟨permutation,?_⟩
      rw [actual]
      simp only [Flapjack.WordAlloc.callRetTail,if_neg badLabel,if_pos sourceUnion,if_pos targetUnion]
      exact composed
    | result x values =>
      by_cases badReturn : x ≠ .loc l1 l2 ∨ values.length ≠ returns.length
      · refine ⟨returned.permute,?_⟩
        rw [Flapjack.WordAlloc.callRetTail_result_err _ _ _ _ _ _ _ _ _ badReturn]
        simp [returningPost]
      have targetGood : ¬ (x ≠ .loc l1 l2 ∨ values.length ≠ registers.length) := by
        simpa [registers] using badReturn
      obtain ⟨sourceKeys,_,swapped⟩ := transport
      obtain ⟨targetStack,swappedRun,valuesEqual,targetKeys⟩ := swapped targetEntry.stack stackValues
      have actual := targetTransport _ swappedRun
      obtain ⟨popped,targetPopped,sourcePop,targetPop,poppedFrame,poppedDomain,poppedValues⟩ :=
        returningPopCutRelation source target returned first second targetFirst targetSecond (some (exceptionVar,handlerBody,handlerL1,handlerL2)) (some (2,exceptionContinuation,handlerL1,handlerL2))
          targetStack (optionLookup ssa) sourceRoots targetRoots sourcePerm targetPerm sameStack
          sourceRootRead targetRootRead rootMap firstRelated injective sourceKeys targetKeys valuesEqual
      have sourceNames : sptDomain popped.locals = sptDomain (sptUnion firstNames secondNames) := by
        rw [poppedDomain,sptDomain_sptUnion,firstDomain,secondDomain]
      have restricted := returningCutSSA counter ssa (sptUnion firstNames secondNames)
        popped.locals targetPopped.locals mapped sourceNames (poppedValues _) cutBounds
      have sourceUnion : sptDomainEqUnion popped.locals first second := by
        intro key
        change sptDomain popped.locals key ↔ sptDomain first key ∨ sptDomain second key
        have equality := congrFun poppedDomain key
        rw [equality]
      obtain ⟨_,_,_,_,_,otherPop,otherPopRun,_,targetDomain,_⟩ :=
        WordSemStackEq.pushEnvPopEnvSKeyEq (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target
          {returned with stack := targetStack} targetKeys
      have samePop : otherPop = targetPopped := by
        rw [targetPop] at otherPopRun
        exact Option.some.inj otherPopRun.symm
      rw [samePop] at targetDomain
      have targetUnion : sptDomainEqUnion targetPopped.locals targetFirst targetSecond := by
        intro key
        change sptDomain targetPopped.locals key ↔ sptDomain targetFirst key ∨ sptDomain targetSecond key
        have equality := congrFun targetDomain key
        rw [←equality]
        exact Or.comm
      have lengths : returns.length = values.length := by
        have := (not_or.mp badReturn).2
        omega
      obtain ⟨permutation,post⟩ := returningNormalContinuation body popped targetPopped ssa
        (sptUnion firstNames secondNames) counter returns values tables retMove moveMap moveNext
        renamed retMap retNext compiled leftMap leftNext moveProduced renameProduced bodyProduced
        restricted valid stackClass sourceNames lengths distinct below bodyBounds poppedFrame tableValid bodyIH
      change returningPost leftMap leftNext tables _ _ at post
      have composed := returningAppendReconciliation
        (WordSemStateFiniteExact.evaluate body
          {WordSemStateFiniteExact.setVars returns values popped with permute := permutation})
        (WordSemStateFiniteExact.setVars registers values targetPopped) retBody retCons leftMap finalMap
        leftNext finalNext tables normalReconcile post
      refine ⟨permutation,?_⟩
      rw [actual,
        Flapjack.WordAlloc.callRetTail_result_pop _ _ _ _ _ _ _ _ _ {popped with permute := permutation}
          badReturn (by rw [Flapjack.WordAlloc.popEnv_withPermute,sourcePop]; rfl),
        Flapjack.WordAlloc.callRetTail_result_pop _ _ _ _ _ _ _ _ _ targetPopped targetGood targetPop]
      rw [if_pos sourceUnion,if_pos targetUnion]
      exact composed




namespace SemanticCallReturningWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticCallReturningWitnesses

/-- Full no-handler returning Call assembly (original8298-8692).
All six original premises and only the return-body IH are retained. The source
permutation, all successful guard branches, target runs and post-state facts
are derived internally. The imported evaluator inherits reals_as_rational_cuts
(SOUNDNESS item 8). The handler-SOME case and full SSA assembly are also
ported; production migration and end-to-end correctness remain open. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectCallReturningNone {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (returns : List Nat) (firstNames secondNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation body st ct map na lt)
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next))
        (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none)
      source target ssa next tables := by
  classical
  obtain ⟨frame,related,allocated,vars,valid,tableValid⟩ := premises
  cases read : WordSemStateFiniteExact.getVars args source with
  | none =>
    refine ⟨source.permute,?_⟩
    simp [WordSemStateFiniteExact.evaluate,read]
  | some values =>
    by_cases bad : wordSemBadDestArgs dest args = true
    · refine ⟨source.permute,?_⟩
      simp [WordSemStateFiniteExact.evaluate,read,bad]
    cases found : wordSemFindCode dest (.loc l1 l2 :: values) source.code source.stackSize with
    | none =>
      refine ⟨source.permute,?_⟩
      simp [WordSemStateFiniteExact.evaluate,read,bad,wordSemAddRetLoc,found]
    | some triple =>
      obtain ⟨calleeArgs,callee,size⟩ := triple
      by_cases badCut : sptDomainEmpty firstNames ∨ ¬ returns.Nodup
      · refine ⟨source.permute,?_⟩
        simp [WordSemStateFiniteExact.evaluate,read,bad,wordSemAddRetLoc,found,badCut]
      cases cut : wordSemCutEnvs (firstNames,secondNames) source.locals with
      | none =>
        refine ⟨source.permute,?_⟩
        simp [WordSemStateFiniteExact.evaluate,read,bad,wordSemAddRetLoc,found,badCut,cut]
      | some pair =>
        obtain ⟨first,second⟩ := pair
        let names := sptUnion firstNames secondNames
        let nameList := (sptToAList names).map Prod.fst
        have prep := returningPrepareArguments source target ssa next args values firstNames secondNames
          first second cut read related allocated valid frame
        generalize stackProduced : listNextVarRenameMove (width := width) ssa (next+2) nameList = stackOutput
          at prep
        rcases stackOutput with ⟨stackMove,fresh,counter⟩
        dsimp only at prep
        generalize stackRun : WordSemStateFiniteExact.evaluate stackMove target = firstRun at prep
        rcases firstRun with ⟨firstResult,refreshed⟩
        dsimp only at prep
        obtain ⟨normal,argRun,argRead,newRelated,newFrame,targetFirst,targetSecond,targetCut,
          targetFirstDomain,targetSecondDomain,firstValues,secondValues,firstInjective,secondInjective,
          firstDomain,secondDomain⟩ := prep
        subst firstResult
        let renamedArgs := args.map (optionLookup ssa)
        let convArgs := (List.range renamedArgs.length).map (fun index => 2*(index+1))
        let prepared := WordSemStateFiniteExact.setVars convArgs values refreshed
        generalize moveProduced : listNextVarRenameMove (width := width) (sptInter fresh names)
          (counter+2) nameList = moveOutput
        rcases moveOutput with ⟨retMove,moveMap,moveNext⟩
        generalize renameProduced : listNextVarRename returns moveMap moveNext = retOutput
        rcases retOutput with ⟨renamed,retMap,retNext⟩
        generalize bodyProduced : ssaCcTrans body retMap retNext tables = bodyOutput
        rcases bodyOutput with ⟨compiled,finalMap,finalNext⟩
        let registers := (List.range returns.length).map (fun index => 2*(index+1))
        let continuation := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
        let targetNames := Flapjack.WordAlloc.applyNummapsKey (optionLookup fresh) (firstNames,secondNames)
        let targetCall := WordLangProgHOL.call (some (registers,targetNames,continuation,l1,l2)) dest convArgs none
        dsimp only [names,nameList] at stackProduced moveProduced
        have compiledWhole : ssaCcTrans
            (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none) ssa next tables =
            (.seq stackMove (.seq (.move 1 (convArgs.zip renamedArgs)) targetCall),finalMap,finalNext) := by
          simp only [ssaCcTrans,stackProduced,moveProduced,renameProduced,bodyProduced]
          rfl
        have prefixRun : WordSemStateFiniteExact.evaluate
            (.seq stackMove (.seq (.move 1 (convArgs.zip renamedArgs)) targetCall)) target =
            WordSemStateFiniteExact.evaluate targetCall prepared := by
          rw [evaluateSeqCollapse _ _ _ _ stackRun,evaluateSeqCollapse _ _ _ _ argRun]
        have properties := listNextVarRenameMoveProps2 nameList ssa next stackMove fresh counter
          stackProduced ⟨Or.inl allocated,valid⟩
        have cutBounds : ∀ key, sptDomain names key → key < counter := by
          have cutVars : (∀ key ∈ (sptToAList firstNames).map Prod.fst, key < next) ∧
              (∀ key ∈ (sptToAList secondNames).map Prod.fst, key < next) := by
            simp only [everyVarHOL,everyNameHOL,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at vars
            exact vars.2.1.1.2
          intro key member
          rw [sptDomain_sptUnion] at member
          have bound := member.elim
            (fun h => cutVars.1 key ((sptMemMapFstToAList _ key).mpr h))
            (fun h => cutVars.2 key ((sptMemMapFstToAList _ key).mpr h))
          omega
        have returnBounds : ∀ key ∈ returns, key < counter := by
          have retVars : ∀ key ∈ returns, key < next := by
            simp only [everyVarHOL,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at vars
            exact vars.2.1.1.1
          intro key member
          have := retVars key member
          omega
        have bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true := by
          have old : everyVarHOL (fun key => decide (key < next)) body = true := by
            simp only [everyVarHOL,Bool.and_eq_true] at vars
            exact vars.2.1.2
          apply Flapjack.everyVarMono _ body _
          refine ⟨?_,old⟩
          intro key bound
          simp only [decide_eq_true_eq] at bound ⊢
          omega
        have mapped : ∀ key, sptDomain names key → sptDomain fresh key := by
          have subset := cutEnvsDomainSubset firstNames secondNames source.locals (first,second) cut
          intro key member
          rw [sptDomain_sptUnion] at member
          obtain ⟨value,lookup⟩ := (sptMem_iff_lookup key source.locals).mp
            (member.elim (subset.1 key) (subset.2 key))
          exact (newRelated.2 key value lookup).1
        have injection : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
            (sptDomain first b ∨ sptDomain second b) →
            optionLookup fresh a = optionLookup fresh b → a = b := by
          intro a b inA inB equal
          have namedA : sptDomain names a := by
            rw [sptDomain_sptUnion]
            simpa [firstDomain,secondDomain] using inA
          have namedB : sptDomain names b := by
            rw [sptDomain_sptUnion]
            simpa [firstDomain,secondDomain] using inB
          exact listNextVarRenameMoveDistinct ssa (next+2) nameList stackMove fresh counter a b
            ⟨stackProduced,sptAllDistinctMapFstToAList _,(sptMemMapFstToAList _ a).mpr namedA,
              (sptMemMapFstToAList _ b).mpr namedB,equal⟩
        have targetNonempty : ¬ sptDomainEmpty targetNames.1 := by
          change ¬ sptDomainEmpty (Flapjack.WordAlloc.applyNummapKey (optionLookup fresh) firstNames)
          intro empty
          have sourceEmpty : sptDomainEmpty firstNames := by
            intro key present
            have namedTarget : sptDomain
                (Flapjack.WordAlloc.applyNummapKey (optionLookup fresh) firstNames)
                (optionLookup fresh key) := by
              rw [Flapjack.WordAlloc.applyNummapKeyDomain]
              exact ⟨key,present,rfl⟩
            exact empty _ namedTarget
          exact (not_or.mp badCut).1 sourceEmpty
        have targetGood : ¬ (sptDomainEmpty targetNames.1 ∨ ¬ registers.Nodup) :=
          not_or.mpr ⟨targetNonempty,not_not.mpr (returningConventionDistinct _)⟩
        have targetBad : ¬ wordSemBadDestArgs dest convArgs = true := by
          rw [returningDestinationGuard]
          exact bad
        have preparedFrame : Flapjack.WordAlloc.wordStateEqRel source prepared := by
          simpa [prepared,convArgs,renamedArgs] using newFrame
        have preparedRead : WordSemStateFiniteExact.getVars convArgs prepared = some values := by
          simpa [prepared,convArgs,renamedArgs] using argRead
        have preparedCut : wordSemCutEnvs targetNames prepared.locals = some (targetFirst,targetSecond) := by
          simpa [prepared,convArgs,renamedArgs,targetNames] using targetCut
        have fields := preparedFrame
        rcases fields with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
        have targetFound : wordSemFindCode dest
            (wordSemAddRetLoc (some (registers,targetNames,continuation,l1,l2)) values)
            prepared.code prepared.stackSize = some (calleeArgs,callee,size) := by
          simpa [wordSemAddRetLoc,h14,h7] using found
        have firstImage : sptDomain targetFirst =
            (fun key => ∃ name, sptDomain first name ∧ optionLookup fresh name = key) := by
          rw [firstDomain]; exact targetFirstDomain
        have secondImage : sptDomain targetSecond =
            (fun key => ∃ name, sptDomain second name ∧ optionLookup fresh name = key) := by
          rw [secondDomain]; exact targetSecondDomain
        have firstRelation : Flapjack.WordAlloc.strongLocalsRel (optionLookup fresh)
            (sptDomain first) first targetFirst := by rw [firstDomain]; exact firstValues
        have secondRelation : Flapjack.WordAlloc.strongLocalsRel (optionLookup fresh)
            (sptDomain second) second targetSecond := by rw [secondDomain]; exact secondValues
        obtain ⟨rootPermutation,roots,stackValues⟩ := Flapjack.WordAlloc.pushEnvSValEq
          (WordSemStateFiniteExact.decClock source) (WordSemStateFiniteExact.decClock prepared)
          second first targetSecond targetFirst (optionLookup fresh) none none
          (wordSemEnvToList targetSecond prepared.permute).2
          ⟨h12.symm,h4.symm,h3.symm,secondImage,secondInjective,firstImage,firstInjective,secondRelation,rfl⟩
        rcases targetRootRead : wordSemEnvToList targetSecond prepared.permute with ⟨targetRoots,targetPerm⟩
        rcases sourceRootRead : wordSemEnvToList second rootPermutation with ⟨sourceRoots,sourcePerm⟩
        have rootFacts := roots
        simp only [WordSemStateFiniteExact.decClock] at rootFacts
        rw [targetRootRead,sourceRootRead] at rootFacts
        dsimp only at rootFacts
        have permutation : (wordSemEnvToList second rootPermutation).2 =
            (wordSemEnvToList targetSecond prepared.permute).2 := by
          rw [sourceRootRead,targetRootRead]
          exact rootFacts.1
        have entry := Flapjack.WordAlloc.calleeSwap preparedFrame first second targetFirst targetSecond
          none none rfl rootPermutation permutation stackValues calleeArgs size
        let sourceBase := {WordSemStateFiniteExact.decClock source with permute := rootPermutation}
        let targetBase := WordSemStateFiniteExact.decClock prepared
        let sourceEntry := WordSemStateFiniteExact.callEnv calleeArgs size
          (WordSemStateFiniteExact.pushEnv (first,second) none sourceBase)
        let targetEntry := WordSemStateFiniteExact.callEnv calleeArgs size
          (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none targetBase)
        have baseFrame : Flapjack.WordAlloc.wordStateEqRel sourceBase targetBase := by
          simpa [sourceBase,targetBase,WordSemStateFiniteExact.decClock,
            Flapjack.WordAlloc.wordStateEqRel,h13] using preparedFrame
        by_cases zero : source.clock = 0
        · refine ⟨rootPermutation,?_⟩
          have sourceTimeout := Flapjack.WordAlloc.evaluate_call_ret_timeout
            {source with permute := rootPermutation} returns (firstNames,secondNames) body l1 l2
            dest args none values calleeArgs callee size (first,second)
            (by rw [WordSemStateFiniteExact.getVars_withPermute]; exact read) bad
            (by simpa [wordSemAddRetLoc] using found) badCut cut zero
          have targetTimeout := Flapjack.WordAlloc.evaluate_call_ret_timeout prepared registers targetNames
            continuation l1 l2 dest convArgs none values calleeArgs callee size (targetFirst,targetSecond)
            preparedRead targetBad targetFound targetGood preparedCut (by rw [h13]; exact zero)
          have maxEqual : (WordSemStateFiniteExact.callEnv calleeArgs size
                (WordSemStateFiniteExact.pushEnv (first,second) none {source with permute := rootPermutation})).stackMax =
              (WordSemStateFiniteExact.callEnv calleeArgs size
                (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none prepared)).stackMax := by
            simpa only [WordSemStateFiniteExact.decClock,WordSemStateFiniteExact.callEnv,
              WordSemStateFiniteExact.pushEnv] using congrArg WordSemStateFiniteExact.stackMax entry
          rw [compiledWhole]
          change returningPost finalMap finalNext tables _ _
          rw [prefixRun,sourceTimeout,targetTimeout]
          unfold returningPost
          rw [if_neg (by intro impossible; cases impossible)]
          simp only [WordSemStateFiniteExact.flushState]
          refine ⟨trivial,?_,trivial⟩
          exact ⟨h1,rfl,rfl,rfl,h5,maxEqual.symm,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
        · have targetRun := Flapjack.WordAlloc.evaluate_call_ret_eq prepared registers targetNames continuation
            l1 l2 dest convArgs none values calleeArgs callee size (targetFirst,targetSecond)
            preparedRead targetBad targetFound targetGood preparedCut (by rw [h13]; exact zero)
          have sourceSuffix : ∀ suffix,
              WordSemStateFiniteExact.evaluate
                (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none)
                {source with permute := Flapjack.WordAlloc.ppPerm rootPermutation suffix} =
              Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) none
                (WordSemStateFiniteExact.evaluate callee {sourceEntry with permute := suffix}) := by
            intro suffix
            rw [Flapjack.WordAlloc.evaluate_call_ret_eq
              {source with permute := Flapjack.WordAlloc.ppPerm rootPermutation suffix}
              returns (firstNames,secondNames) body l1 l2 dest args none values calleeArgs callee size
              (first,second) (by rw [WordSemStateFiniteExact.getVars_withPermute]; exact read) bad
              (by simpa [wordSemAddRetLoc] using found) badCut cut zero]
            change Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) none
              (WordSemStateFiniteExact.evaluate callee (WordSemStateFiniteExact.callEnv calleeArgs size
                (WordSemStateFiniteExact.pushEnv (first,second) none
                  {WordSemStateFiniteExact.decClock source with permute := (Flapjack.WordAlloc.ppPerm rootPermutation suffix)}))) = _
            rw [Flapjack.WordAlloc.pushEnv_ppPerm]
            rfl
          let Q := fun result => returningPost finalMap finalNext tables
            (Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) none result)
            (Flapjack.WordAlloc.callRetTail registers continuation l1 l2 (targetFirst,targetSecond) none
              (WordSemStateFiniteExact.evaluate callee targetEntry))
          have outcome := returningCalleeOutcomes body callee sourceBase targetBase fresh counter
            firstNames secondNames first second targetFirst targetSecond calleeArgs size returns l1 l2 tables
            retMove moveMap moveNext renamed retMap retNext compiled finalMap finalNext
            moveProduced renameProduced bodyProduced baseFrame properties.2.2.2 (properties.2.1 allocated)
            firstDomain secondDomain mapped cutBounds returnBounds (not_not.mp (not_or.mp badCut).2) bodyBounds tableValid
            firstRelation injection sourceRoots targetRoots sourcePerm targetPerm sourceRootRead targetRootRead
            rootFacts.2.1 entry stackValues bodyIH
          have errorQ : ∀ state, WordSemStateFiniteExact.evaluate callee sourceEntry = (some .error,state) →
              Q (some .error,state) := by
            intro state _
            simp [Q,Flapjack.WordAlloc.callRetTail,returningPost]
          obtain ⟨suffix,post⟩ := Flapjack.WordAlloc.permuteSwapLemma4 callee sourceEntry Q ⟨errorQ,outcome⟩
          refine ⟨Flapjack.WordAlloc.ppPerm rootPermutation suffix,?_⟩
          rw [compiledWhole]
          change returningPost finalMap finalNext tables _ _
          rw [prefixRun,targetRun,sourceSuffix]
          exact post


/-- Full original handler-present returning Call case (source8688-9226).
The six original premises and only the two genuine smaller return/exception
continuation IHs establish the complete existential source permutation,
Error exemption, actual target result/frame and result-sensitive locals.
All guards, stack/root transport, exception frame restoration, physical result
binding, handler IH premises and correctL/R reconciliation are derived internally.
The actual exception binder starts after the return compiler's output counter,
as in the original producer. Inherits reals_as_rational_cuts (SOUNDNESS item 8).
The whole returning Call constructor and full SSA assembly are also ported;
production migration and end-to-end correctness remain open. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.

theorem ssaCcTransCorrectCallReturningSome {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (returns : List Nat) (firstNames secondNames : Spt Unit)
    (body handlerBody : WordLangProgHOL (BitVec width)) (l1 l2 exceptionVar handlerL1 handlerL2 : Nat) (dest : Option Nat) (args : List Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (handlerIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) handlerBody = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation handlerBody st ct map na lt)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation body st ct map na lt)
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next))
        (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args (some (exceptionVar,handlerBody,handlerL1,handlerL2))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args (some (exceptionVar,handlerBody,handlerL1,handlerL2)))
      source target ssa next tables := by
  classical
  obtain ⟨frame,related,allocated,vars,valid,tableValid⟩ := premises
  cases read : WordSemStateFiniteExact.getVars args source with
  | none =>
    refine ⟨source.permute,?_⟩
    simp [WordSemStateFiniteExact.evaluate,read]
  | some values =>
    by_cases bad : wordSemBadDestArgs dest args = true
    · refine ⟨source.permute,?_⟩
      simp [WordSemStateFiniteExact.evaluate,read,bad]
    cases found : wordSemFindCode dest (.loc l1 l2 :: values) source.code source.stackSize with
    | none =>
      refine ⟨source.permute,?_⟩
      simp [WordSemStateFiniteExact.evaluate,read,bad,wordSemAddRetLoc,found]
    | some triple =>
      obtain ⟨calleeArgs,callee,size⟩ := triple
      by_cases badCut : sptDomainEmpty firstNames ∨ ¬ returns.Nodup
      · refine ⟨source.permute,?_⟩
        simp [WordSemStateFiniteExact.evaluate,read,bad,wordSemAddRetLoc,found,badCut]
      cases cut : wordSemCutEnvs (firstNames,secondNames) source.locals with
      | none =>
        refine ⟨source.permute,?_⟩
        simp [WordSemStateFiniteExact.evaluate,read,bad,wordSemAddRetLoc,found,badCut,cut]
      | some pair =>
        obtain ⟨first,second⟩ := pair
        let names := sptUnion firstNames secondNames
        let nameList := (sptToAList names).map Prod.fst
        have prep := returningPrepareArguments source target ssa next args values firstNames secondNames
          first second cut read related allocated valid frame
        generalize stackProduced : listNextVarRenameMove (width := width) ssa (next+2) nameList = stackOutput
          at prep
        rcases stackOutput with ⟨stackMove,fresh,counter⟩
        dsimp only at prep
        generalize stackRun : WordSemStateFiniteExact.evaluate stackMove target = firstRun at prep
        rcases firstRun with ⟨firstResult,refreshed⟩
        dsimp only at prep
        obtain ⟨normal,argRun,argRead,newRelated,newFrame,targetFirst,targetSecond,targetCut,
          targetFirstDomain,targetSecondDomain,firstValues,secondValues,firstInjective,secondInjective,
          firstDomain,secondDomain⟩ := prep
        subst firstResult
        let renamedArgs := args.map (optionLookup ssa)
        let convArgs := (List.range renamedArgs.length).map (fun index => 2*(index+1))
        let prepared := WordSemStateFiniteExact.setVars convArgs values refreshed
        generalize moveProduced : listNextVarRenameMove (width := width) (sptInter fresh names)
          (counter+2) nameList = moveOutput
        rcases moveOutput with ⟨retMove,moveMap,moveNext⟩
        generalize renameProduced : listNextVarRename returns moveMap moveNext = retOutput
        rcases retOutput with ⟨renamed,retMap,retNext⟩
        generalize bodyProduced : ssaCcTrans body retMap retNext tables = bodyOutput
        rcases bodyOutput with ⟨compiled,leftMap,leftNext⟩
        generalize exceptionProduced : nextVarRename exceptionVar moveMap leftNext = exceptionOutput
        rcases exceptionOutput with ⟨exceptionOut,exceptionMap,exceptionNext⟩
        generalize handlerProduced : ssaCcTrans handlerBody exceptionMap exceptionNext tables = handlerOutput
        rcases handlerOutput with ⟨compiledException,rightMap,rightNext⟩
        let registers := (List.range returns.length).map (fun index => 2*(index+1))
        let retBody := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
        let exceptionBody := WordLangProgHOL.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)
        let prio := mkPrio retBody exceptionBody
        generalize reconcileProduced : fixInconsistencies (width := width) prio leftMap rightMap rightNext = reconcileOutput
        rcases reconcileOutput with ⟨retCons,excCons,finalNext,finalMap⟩
        let continuation := WordLangProgHOL.seq retBody retCons
        let exceptionContinuation := WordLangProgHOL.seq exceptionBody excCons
        let targetNames := Flapjack.WordAlloc.applyNummapsKey (optionLookup fresh) (firstNames,secondNames)
        let targetCall := WordLangProgHOL.call (some (registers,targetNames,continuation,l1,l2)) dest convArgs (some (2,exceptionContinuation,handlerL1,handlerL2))
        dsimp only [names,nameList] at stackProduced moveProduced
        have compiledWhole : ssaCcTrans
            (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args (some (exceptionVar,handlerBody,handlerL1,handlerL2))) ssa next tables =
            (.seq stackMove (.seq (.move 1 (convArgs.zip renamedArgs)) targetCall),finalMap,finalNext) := by
          have reconcileExpanded := reconcileProduced
          dsimp only [prio,retBody,exceptionBody,registers] at reconcileExpanded
          simp only [ssaCcTrans,stackProduced,moveProduced,renameProduced,bodyProduced,exceptionProduced,handlerProduced,reconcileExpanded]
          rfl
        have prefixRun : WordSemStateFiniteExact.evaluate
            (.seq stackMove (.seq (.move 1 (convArgs.zip renamedArgs)) targetCall)) target =
            WordSemStateFiniteExact.evaluate targetCall prepared := by
          rw [evaluateSeqCollapse _ _ _ _ stackRun,evaluateSeqCollapse _ _ _ _ argRun]
        have properties := listNextVarRenameMoveProps2 nameList ssa next stackMove fresh counter
          stackProduced ⟨Or.inl allocated,valid⟩
        have moveProps := listNextVarRenameMoveProps nameList (sptInter fresh names) (counter+2)
          retMove moveMap moveNext moveProduced
          ⟨Or.inl (isStackVarFlip counter (properties.2.1 allocated)),
            ssaMapOKMore counter _ (counter+2) ⟨ssaMapOKInter counter fresh names properties.2.2.2,by omega⟩⟩
        have moveAllocated := moveProps.2.1 (isStackVarFlip counter (properties.2.1 allocated))
        have retProps := listNextVarRenameProps returns moveMap moveNext renamed retMap retNext
          renameProduced ⟨Or.inl moveAllocated,moveProps.2.2.2⟩
        have bodyProps := ssaCcTransProps body retMap retNext tables compiled leftMap leftNext bodyProduced
          ⟨retProps.2.2.2,retProps.2.1 moveAllocated⟩
        have moveIncrease : moveNext ≤ leftNext := by omega
        have exceptionListProduced : listNextVarRename [exceptionVar] moveMap leftNext =
            ([exceptionOut],exceptionMap,exceptionNext) := by
          simp only [listNextVarRename,exceptionProduced]
        have exceptionProps := listNextVarRenameProps [exceptionVar] moveMap leftNext [exceptionOut]
          exceptionMap exceptionNext exceptionListProduced
          ⟨Or.inl bodyProps.2.1,ssaMapOKMore moveNext moveMap leftNext ⟨moveProps.2.2.2,moveIncrease⟩⟩
        have handlerProps := ssaCcTransProps handlerBody exceptionMap exceptionNext tables compiledException
          rightMap rightNext handlerProduced ⟨exceptionProps.2.2.2,exceptionProps.2.1 bodyProps.2.1⟩
        have leftIncrease : leftNext ≤ rightNext := by omega
        have exceptionBelow : exceptionVar < counter := by
          have original : exceptionVar < next := by
            simp only [everyVarHOL,Bool.and_eq_true,decide_eq_true_eq] at vars
            exact vars.2.2.1
          omega
        have handlerBounds : everyVarHOL (fun key => decide (key < counter)) handlerBody = true := by
          have old : everyVarHOL (fun key => decide (key < next)) handlerBody = true := by
            simp only [everyVarHOL,Bool.and_eq_true] at vars
            exact vars.2.2.2
          apply Flapjack.everyVarMono _ handlerBody _
          refine ⟨?_,old⟩
          intro key bound
          simp only [decide_eq_true_eq] at bound ⊢
          omega
        have cutBounds : ∀ key, sptDomain names key → key < counter := by
          have cutVars : (∀ key ∈ (sptToAList firstNames).map Prod.fst, key < next) ∧
              (∀ key ∈ (sptToAList secondNames).map Prod.fst, key < next) := by
            simp only [everyVarHOL,everyNameHOL,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at vars
            exact vars.2.1.1.2
          intro key member
          rw [sptDomain_sptUnion] at member
          have bound := member.elim
            (fun h => cutVars.1 key ((sptMemMapFstToAList _ key).mpr h))
            (fun h => cutVars.2 key ((sptMemMapFstToAList _ key).mpr h))
          omega
        have returnBounds : ∀ key ∈ returns, key < counter := by
          have retVars : ∀ key ∈ returns, key < next := by
            simp only [everyVarHOL,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at vars
            exact vars.2.1.1.1
          intro key member
          have := retVars key member
          omega
        have bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true := by
          have old : everyVarHOL (fun key => decide (key < next)) body = true := by
            simp only [everyVarHOL,Bool.and_eq_true] at vars
            exact vars.2.1.2
          apply Flapjack.everyVarMono _ body _
          refine ⟨?_,old⟩
          intro key bound
          simp only [decide_eq_true_eq] at bound ⊢
          omega
        have mapped : ∀ key, sptDomain names key → sptDomain fresh key := by
          have subset := cutEnvsDomainSubset firstNames secondNames source.locals (first,second) cut
          intro key member
          rw [sptDomain_sptUnion] at member
          obtain ⟨value,lookup⟩ := (sptMem_iff_lookup key source.locals).mp
            (member.elim (subset.1 key) (subset.2 key))
          exact (newRelated.2 key value lookup).1
        have injection : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
            (sptDomain first b ∨ sptDomain second b) →
            optionLookup fresh a = optionLookup fresh b → a = b := by
          intro a b inA inB equal
          have namedA : sptDomain names a := by
            rw [sptDomain_sptUnion]
            simpa [firstDomain,secondDomain] using inA
          have namedB : sptDomain names b := by
            rw [sptDomain_sptUnion]
            simpa [firstDomain,secondDomain] using inB
          exact listNextVarRenameMoveDistinct ssa (next+2) nameList stackMove fresh counter a b
            ⟨stackProduced,sptAllDistinctMapFstToAList _,(sptMemMapFstToAList _ a).mpr namedA,
              (sptMemMapFstToAList _ b).mpr namedB,equal⟩
        have targetNonempty : ¬ sptDomainEmpty targetNames.1 := by
          change ¬ sptDomainEmpty (Flapjack.WordAlloc.applyNummapKey (optionLookup fresh) firstNames)
          intro empty
          have sourceEmpty : sptDomainEmpty firstNames := by
            intro key present
            have namedTarget : sptDomain
                (Flapjack.WordAlloc.applyNummapKey (optionLookup fresh) firstNames)
                (optionLookup fresh key) := by
              rw [Flapjack.WordAlloc.applyNummapKeyDomain]
              exact ⟨key,present,rfl⟩
            exact empty _ namedTarget
          exact (not_or.mp badCut).1 sourceEmpty
        have targetGood : ¬ (sptDomainEmpty targetNames.1 ∨ ¬ registers.Nodup) :=
          not_or.mpr ⟨targetNonempty,not_not.mpr (returningConventionDistinct _)⟩
        have targetBad : ¬ wordSemBadDestArgs dest convArgs = true := by
          rw [returningDestinationGuard]
          exact bad
        have preparedFrame : Flapjack.WordAlloc.wordStateEqRel source prepared := by
          simpa [prepared,convArgs,renamedArgs] using newFrame
        have preparedRead : WordSemStateFiniteExact.getVars convArgs prepared = some values := by
          simpa [prepared,convArgs,renamedArgs] using argRead
        have preparedCut : wordSemCutEnvs targetNames prepared.locals = some (targetFirst,targetSecond) := by
          simpa [prepared,convArgs,renamedArgs,targetNames] using targetCut
        have fields := preparedFrame
        rcases fields with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
        have targetFound : wordSemFindCode dest
            (wordSemAddRetLoc (some (registers,targetNames,continuation,l1,l2)) values)
            prepared.code prepared.stackSize = some (calleeArgs,callee,size) := by
          simpa [wordSemAddRetLoc,h14,h7] using found
        have firstImage : sptDomain targetFirst =
            (fun key => ∃ name, sptDomain first name ∧ optionLookup fresh name = key) := by
          rw [firstDomain]; exact targetFirstDomain
        have secondImage : sptDomain targetSecond =
            (fun key => ∃ name, sptDomain second name ∧ optionLookup fresh name = key) := by
          rw [secondDomain]; exact targetSecondDomain
        have firstRelation : Flapjack.WordAlloc.strongLocalsRel (optionLookup fresh)
            (sptDomain first) first targetFirst := by rw [firstDomain]; exact firstValues
        have secondRelation : Flapjack.WordAlloc.strongLocalsRel (optionLookup fresh)
            (sptDomain second) second targetSecond := by rw [secondDomain]; exact secondValues
        obtain ⟨rootPermutation,roots,stackValues⟩ := Flapjack.WordAlloc.pushEnvSValEq
          (WordSemStateFiniteExact.decClock source) (WordSemStateFiniteExact.decClock prepared)
          second first targetSecond targetFirst (optionLookup fresh) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) (some (2,exceptionContinuation,handlerL1,handlerL2))
          (wordSemEnvToList targetSecond prepared.permute).2
          ⟨h12.symm,h4.symm,h3.symm,secondImage,secondInjective,firstImage,firstInjective,secondRelation,⟨rfl,rfl⟩⟩
        rcases targetRootRead : wordSemEnvToList targetSecond prepared.permute with ⟨targetRoots,targetPerm⟩
        rcases sourceRootRead : wordSemEnvToList second rootPermutation with ⟨sourceRoots,sourcePerm⟩
        have rootFacts := roots
        simp only [WordSemStateFiniteExact.decClock] at rootFacts
        rw [targetRootRead,sourceRootRead] at rootFacts
        dsimp only at rootFacts
        have permutation : (wordSemEnvToList second rootPermutation).2 =
            (wordSemEnvToList targetSecond prepared.permute).2 := by
          rw [sourceRootRead,targetRootRead]
          exact rootFacts.1
        have entry := Flapjack.WordAlloc.calleeSwap preparedFrame first second targetFirst targetSecond
          (some (exceptionVar,handlerBody,handlerL1,handlerL2)) (some (2,exceptionContinuation,handlerL1,handlerL2)) rfl rootPermutation permutation stackValues calleeArgs size
        let sourceBase := {WordSemStateFiniteExact.decClock source with permute := rootPermutation}
        let targetBase := WordSemStateFiniteExact.decClock prepared
        let sourceEntry := WordSemStateFiniteExact.callEnv calleeArgs size
          (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) sourceBase)
        let targetEntry := WordSemStateFiniteExact.callEnv calleeArgs size
          (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,exceptionContinuation,handlerL1,handlerL2)) targetBase)
        have baseFrame : Flapjack.WordAlloc.wordStateEqRel sourceBase targetBase := by
          simpa [sourceBase,targetBase,WordSemStateFiniteExact.decClock,
            Flapjack.WordAlloc.wordStateEqRel,h13] using preparedFrame
        by_cases zero : source.clock = 0
        · refine ⟨rootPermutation,?_⟩
          have sourceTimeout := Flapjack.WordAlloc.evaluate_call_ret_timeout
            {source with permute := rootPermutation} returns (firstNames,secondNames) body l1 l2
            dest args (some (exceptionVar,handlerBody,handlerL1,handlerL2)) values calleeArgs callee size (first,second)
            (by rw [WordSemStateFiniteExact.getVars_withPermute]; exact read) bad
            (by simpa [wordSemAddRetLoc] using found) badCut cut zero
          have targetTimeout := Flapjack.WordAlloc.evaluate_call_ret_timeout prepared registers targetNames
            continuation l1 l2 dest convArgs (some (2,exceptionContinuation,handlerL1,handlerL2)) values calleeArgs callee size (targetFirst,targetSecond)
            preparedRead targetBad targetFound targetGood preparedCut (by rw [h13]; exact zero)
          have maxEqual : (WordSemStateFiniteExact.callEnv calleeArgs size
                (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) {source with permute := rootPermutation})).stackMax =
              (WordSemStateFiniteExact.callEnv calleeArgs size
                (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,exceptionContinuation,handlerL1,handlerL2)) prepared)).stackMax := by
            simpa only [WordSemStateFiniteExact.decClock,WordSemStateFiniteExact.callEnv,
              WordSemStateFiniteExact.pushEnv] using congrArg WordSemStateFiniteExact.stackMax entry
          rw [compiledWhole]
          change returningPost finalMap finalNext tables _ _
          rw [prefixRun,sourceTimeout,targetTimeout]
          unfold returningPost
          rw [if_neg (by intro impossible; cases impossible)]
          simp only [WordSemStateFiniteExact.flushState]
          refine ⟨trivial,?_,trivial⟩
          exact ⟨h1,rfl,rfl,rfl,h5,maxEqual.symm,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
        · have targetRun := Flapjack.WordAlloc.evaluate_call_ret_eq prepared registers targetNames continuation
            l1 l2 dest convArgs (some (2,exceptionContinuation,handlerL1,handlerL2)) values calleeArgs callee size (targetFirst,targetSecond)
            preparedRead targetBad targetFound targetGood preparedCut (by rw [h13]; exact zero)
          have sourceSuffix : ∀ suffix,
              WordSemStateFiniteExact.evaluate
                (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args (some (exceptionVar,handlerBody,handlerL1,handlerL2)))
                {source with permute := Flapjack.WordAlloc.ppPerm rootPermutation suffix} =
              Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2))
                (WordSemStateFiniteExact.evaluate callee {sourceEntry with permute := suffix}) := by
            intro suffix
            rw [Flapjack.WordAlloc.evaluate_call_ret_eq
              {source with permute := Flapjack.WordAlloc.ppPerm rootPermutation suffix}
              returns (firstNames,secondNames) body l1 l2 dest args (some (exceptionVar,handlerBody,handlerL1,handlerL2)) values calleeArgs callee size
              (first,second) (by rw [WordSemStateFiniteExact.getVars_withPermute]; exact read) bad
              (by simpa [wordSemAddRetLoc] using found) badCut cut zero]
            change Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2))
              (WordSemStateFiniteExact.evaluate callee (WordSemStateFiniteExact.callEnv calleeArgs size
                (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2))
                  {WordSemStateFiniteExact.decClock source with permute := (Flapjack.WordAlloc.ppPerm rootPermutation suffix)}))) = _
            rw [Flapjack.WordAlloc.pushEnv_ppPerm]
            rfl
          let Q := fun result => returningPost finalMap finalNext tables
            (Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) result)
            (Flapjack.WordAlloc.callRetTail registers continuation l1 l2 (targetFirst,targetSecond) (some (2,exceptionContinuation,handlerL1,handlerL2))
              (WordSemStateFiniteExact.evaluate callee targetEntry))
          have outcome := returningHandlerCalleeOutcomes body handlerBody callee sourceBase targetBase fresh counter
            firstNames secondNames first second targetFirst targetSecond calleeArgs size returns l1 l2
            exceptionVar handlerL1 handlerL2 tables retMove moveMap moveNext renamed retMap retNext compiled leftMap leftNext
            exceptionOut exceptionMap exceptionNext compiledException rightMap rightNext prio retCons excCons finalMap finalNext
            exceptionProduced handlerProduced reconcileProduced bodyProps.2.1 handlerProps.2.1 bodyProps.2.2
            handlerProps.2.2 moveIncrease leftIncrease exceptionBelow handlerBounds
            moveProduced renameProduced bodyProduced baseFrame properties.2.2.2 (properties.2.1 allocated)
            firstDomain secondDomain mapped cutBounds returnBounds (not_not.mp (not_or.mp badCut).2) bodyBounds tableValid
            firstRelation injection sourceRoots targetRoots sourcePerm targetPerm sourceRootRead targetRootRead
            rootFacts.2.1 entry stackValues handlerIH bodyIH
          have errorQ : ∀ state, WordSemStateFiniteExact.evaluate callee sourceEntry = (some .error,state) →
              Q (some .error,state) := by
            intro state _
            simp [Q,Flapjack.WordAlloc.callRetTail,returningPost]
          obtain ⟨suffix,post⟩ := Flapjack.WordAlloc.permuteSwapLemma4 callee sourceEntry Q ⟨errorQ,outcome⟩
          refine ⟨Flapjack.WordAlloc.ppPerm rootPermutation suffix,?_⟩
          rw [compiledWhole]
          change returningPost finalMap finalNext tables _ _
          rw [prefixRun,targetRun,sourceSuffix]
          exact post

/-- Complete original returning Call case, with only genuine smaller return and
optional exception continuation IHs in addition to HOL's six premises.
Inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectCallReturning {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (returns : List Nat) (firstNames secondNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation body st ct map na lt)
    (handlerIH : match handler with
      | none => True
      | some (_, handlerBody, _, _) => ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) handlerBody = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation handlerBody st ct map na lt)
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next))
        (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args handler) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args handler)
      source target ssa next tables := by
  cases handler with
  | none =>
    exact ssaCcTransCorrectCallReturningNone source target ssa next returns firstNames
      secondNames body l1 l2 dest args tables bodyIH premises
  | some handler =>
    rcases handler with ⟨exceptionVar, handlerBody, handlerL1, handlerL2⟩
    exact ssaCcTransCorrectCallReturningSome source target ssa next returns firstNames
      secondNames body handlerBody l1 l2 exceptionVar handlerL1 handlerL2 dest args tables
      handlerIH bodyIH premises

end Flapjack.Compiler.Backend.WordAlloc
