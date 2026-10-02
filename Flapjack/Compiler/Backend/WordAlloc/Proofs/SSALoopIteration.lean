import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSACutEnvsDomain
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSetup
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcile
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvLemma
import Flapjack.Compiler.Backend.WordAlloc.Proofs.PermuteSwap

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Private proof infrastructure for the original Loop body-IH entry. It has no
separate HOL declaration: these are the conjuncts derived inline at7158-7203.
The full Loop helper will discharge all these premises from its cut result. -/
private theorem bodyEntryLocals {α : Type} (ssa : Spt Nat) (names : Spt Unit)
    (next : Nat) (source target : Spt α)
    (sourceDomain : sptDomain source = sptDomain names)
    (namesMapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (imagePresent : ∀ key, sptDomain names key → sptDomain target (optionLookup ssa key))
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa) (sptDomain names) source target)
    (bounded : ∀ key, sptDomain names key → key < next) :
    ssaLocalsRel next (sptInter ssa names) source target := by
  constructor
  · intro key register read
    rw [sptLookup_sptInterCases] at read
    cases original : sptLookup key ssa <;> cases named : sptLookup key names <;>
      simp [original,named] at read
    rename_i value marker
    have equal := read
    subst register
    have member : sptDomain names key := (sptMem_iff_lookup key names).mpr ⟨marker,named⟩
    simpa [optionLookup,original,sptMem] using imagePresent key member
  · intro key value read
    have member : sptDomain names key := by
      rw [← sourceDomain]
      exact (sptMem_iff_lookup key source).mpr ⟨value,read⟩
    obtain ⟨register,original⟩ := (sptMem_iff_lookup key ssa).mp (namesMapped key member)
    obtain ⟨marker,named⟩ := (sptMem_iff_lookup key names).mp member
    have mapped : sptLookup key (sptInter ssa names) = some register := by
      simp [sptLookup_sptInterCases,original,named]
    refine ⟨(sptMem_iff_lookup key _).mpr ⟨register,mapped⟩, ?_, fun _ => bounded key member⟩
    simpa [mapped,original,optionLookup] using strong key value ⟨member,read⟩

/-- Internal successful entry-cut derivation used by the full Loop helper.
These obligations occur inline in original7136-7154; no standalone HOL tag. -/
private theorem loopEntryCut {α : Type} (ssa : Spt Nat) (names : Spt Unit)
    (next : Nat) (source target sourceEnv : Spt α)
    (cut : wordSemCutEnv (names,.ln) source = some sourceEnv)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source target)
    (injective : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup ssa x = optionLookup ssa y → x = y)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (bounded : ∀ key, sptDomain names key → key < next) :
    ∃ targetEnv,
      wordSemCutEnv (Flapjack.WordAlloc.applyNummapKey (optionLookup ssa) names,.ln)
        target = some targetEnv ∧
      sptDomain sourceEnv = sptDomain names ∧
      ssaLocalsRel next (sptInter ssa names) sourceEnv targetEnv := by
  have empty : ∀ key, ¬ sptDomain (Spt.ln : Spt Unit) key := by
    intro key
    simp [sptDomain]
  have jointInjective : ∀ x y, (sptDomain names x ∨ sptDomain (Spt.ln : Spt Unit) x) →
      (sptDomain names y ∨ sptDomain (Spt.ln : Spt Unit) y) →
      optionLookup ssa x = optionLookup ssa y → x = y := by
    intro x y hx hy equal
    exact injective x y (hx.resolve_right (empty x)) (hy.resolve_right (empty y)) equal
  have jointStrong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (fun key => sptDomain names key ∨ sptDomain (Spt.ln : Spt Unit) key) source target := by
    intro key value h
    exact strong key value ⟨h.1.resolve_right (empty key),h.2⟩
  obtain ⟨targetEnv,targetCut,image,related,_,sourceDomain⟩ :=
    Flapjack.WordAlloc.cutEnvLemma names .ln source target sourceEnv (optionLookup ssa)
      ⟨jointInjective,cut,jointStrong⟩
  have domain : sptDomain sourceEnv = sptDomain names := by
    funext key
    exact (congrFun sourceDomain key).trans (propext (or_iff_left (empty key)))
  have cutRelated : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) sourceEnv targetEnv := by
    intro key value h
    exact related key value ⟨Or.inl h.1,h.2⟩
  have present : ∀ key, sptDomain names key → sptDomain targetEnv (optionLookup ssa key) := by
    intro key h
    rw [image]
    exact ⟨key,by rw [domain]; exact h,rfl⟩
  refine ⟨targetEnv,?_,domain,bodyEntryLocals ssa names next sourceEnv targetEnv
    domain mapped present cutRelated bounded⟩
  simpa [Flapjack.WordAlloc.applyNummapsKey,Flapjack.WordAlloc.applyNummapKey,sptFromAList] using targetCut

/-- Internal original7107-7122 target-cut failure contradiction. The original
image-domain premise alone supplies the actual cut guard; no source success
or target evaluation is assumed. -/
private theorem targetEntryCutExists {α : Type} (ssa : Spt Nat) (names : Spt Unit)
    (target : Spt α)
    (present : ∀ key, sptDomain names key → sptDomain target (optionLookup ssa key)) :
    ∃ targetEnv,
      wordSemCutEnv (Flapjack.WordAlloc.applyNummapKey (optionLookup ssa) names,.ln)
        target = some targetEnv := by
  have renamedSubset : LoopSemStateFiniteExact.sptSubsetLive
      (Flapjack.WordAlloc.applyNummapKey (optionLookup ssa) names) target := by
    intro key member
    change sptDomain (Flapjack.WordAlloc.applyNummapKey (optionLookup ssa) names) key at member
    rw [Flapjack.WordAlloc.applyNummapKeyDomain] at member
    obtain ⟨original,inside,equal⟩ := member
    subst key
    exact present original inside
  have emptySubset : LoopSemStateFiniteExact.sptSubsetLive (Spt.ln : Spt Unit) target := by
    intro key member
    simp at member
  exact ⟨sptUnion (sptInter target .ln)
    (sptInter target (Flapjack.WordAlloc.applyNummapKey (optionLookup ssa) names)),
    by simp only [wordSemCutEnv,wordSemCutEnvs,wordSemCutNames,renamedSubset,emptySubset,if_pos]; rfl⟩

/-- Original source entry-cut failure branch; permutation changes no locals. -/
private theorem sourceEntryCutError {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F) (names exits : Spt Unit)
    (body : WordLangProgHOL (BitVec width)) (permutation : Nat → Nat → Nat)
    (cut : wordSemCutEnv (names,.ln) source.locals = none) :
    WordSemStateFiniteExact.evaluate (.loop names body exits) {source with permute := permutation} =
      (some .error,{source with permute := permutation}) := by
  have stateCut : WordSemStateFiniteExact.cutState (names,.ln)
      {source with permute := permutation} = none := by
    change (match wordSemCutEnv (names,.ln) source.locals with
      | none => none | some env => some {source with permute := permutation,locals := env}) = none
    rw [cut]
  simp only [WordSemStateFiniteExact.evaluate_def_rebound]
  rw [stateCut]

/-- Original source-body Error branch propagates through the actual Loop. The
body evaluation is a derived internal fact obtained from the body IH. -/
private theorem sourceBodyError {width : Nat} [NeZero width] {C F : Type}
    (source after : WordSemStateFiniteExact width C F) (names exits : Spt Unit)
    (body : WordLangProgHOL (BitVec width)) (env : Spt (WordLocW width))
    (permutation : Nat → Nat → Nat)
    (cut : wordSemCutEnv (names,.ln) source.locals = some env)
    (run : WordSemStateFiniteExact.evaluate body {source with locals := env,permute := permutation} =
      (some .error,after)) :
    WordSemStateFiniteExact.evaluate (.loop names body exits) {source with permute := permutation} =
      (some .error,after) := by
  have stateCut : WordSemStateFiniteExact.cutState (names,.ln)
      {source with permute := permutation} = some {source with locals := env,permute := permutation} := by
    change (match wordSemCutEnv (names,.ln) source.locals with
      | none => none | some env => some {source with permute := permutation,locals := env}) = _
    rw [cut]
  simp only [WordSemStateFiniteExact.evaluate_def_rebound]
  rw [stateCut]
  dsimp only
  rw [run]
  rfl

/-- Actual transformed Loop body with optional reconciliation. This is an
internal evaluation equation: only a NONE body result executes reconciliation,
including the original Skip optimization. -/
private theorem evaluateBodyFinal {width : Nat} [NeZero width] {C F : Type}
    (body moves : WordLangProgHOL (BitVec width))
    (before after : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (run : WordSemStateFiniteExact.evaluate body before = (result,after)) :
    WordSemStateFiniteExact.evaluate (@ite (WordLangProgHOL (BitVec width)) (moves = .skip) (Classical.propDecidable _) body (.seq body moves)) before =
      match (generalizing := false) result with
      | none => WordSemStateFiniteExact.evaluate moves after
      | some value => (some value,after) := by
  classical
  by_cases skip : moves = .skip
  · subst moves
    rw [if_pos rfl]
    cases result <;> simp only [run,WordSemStateFiniteExact.evaluate_def_rebound]
  · rw [if_neg skip]
    simp only [WordSemStateFiniteExact.evaluate_def_rebound]
    rw [run]
    cases result <;> rfl

/-- Original recursive clock measure, including the NONE reconciliation path.
The actual body run and preserved reconciliation frame derive strict decrease. -/
private theorem recursiveClockDecrease {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width))
    (before bodyAfter after : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (run : WordSemStateFiniteExact.evaluate body before = (result,bodyAfter))
    (frame : Flapjack.WordAlloc.wordStateEqRel bodyAfter after)
    (nonzero : after.clock ≠ 0) :
    (WordSemStateFiniteExact.decClock after).clock < before.clock := by
  have bound := (WordSemStateFiniteExact.evaluate_clock body before result bodyAfter run).1
  have clock : after.clock = bodyAfter.clock := frame.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [WordSemStateFiniteExact.decClock]
  omega

/-- Full original body-IH entry assembly (original7136-7205). Cut transport,
locals/frame/map/table facts are proved here; the universal body IH is exactly
the original recursive program hypothesis. No target body execution is assumed. -/
private theorem loopBodyEntry {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (sourceEnv : Spt (WordLocW width))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source.locals target.locals)
    (valid : ssaMapOK next ssa) (allocated : isAllocVar next)
    (vars : everyVarHOL (fun key => decide (key < next)) body = true)
    (entryInjection : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup ssa x = optionLookup ssa y → x = y)
    (exitInjection : ∀ x y, sptDomain exits x → sptDomain exits y →
      optionLookup ssa x = optionLookup ssa y → x = y)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (bounded : ∀ key, sptDomain names key → key < next)
    (tableValid : ltOK tables)
    (bodyIH : ∀ (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
      (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next)) body = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation body source target ssa next tables)
    (cut : wordSemCutEnv (names,.ln) source.locals = some sourceEnv) :
    ∃ targetEnv,
      wordSemCutEnv (Flapjack.WordAlloc.applyNummapKey (optionLookup ssa) names,.ln)
        target.locals = some targetEnv ∧
      sptDomain sourceEnv = sptDomain names ∧
      ssaSimulation body {source with locals := sourceEnv} {target with locals := targetEnv}
        (sptInter ssa names) next ((ssa,names,exits)::tables) := by
  obtain ⟨targetEnv,targetCut,domain,locals⟩ := loopEntryCut ssa names next
    source.locals target.locals sourceEnv cut strong entryInjection mapped bounded
  have updatedFrame : Flapjack.WordAlloc.wordStateEqRel
      {source with locals := sourceEnv} {target with locals := targetEnv} := by
    simpa only [Flapjack.WordAlloc.wordStateEqRel] using frame
  have updatedTables : ltOK ((ssa,names,exits)::tables) := by
    intro table member
    rcases List.mem_cons.mp member with equal | member
    · subst table
      exact ⟨entryInjection,exitInjection⟩
    · exact tableValid table member
  exact ⟨targetEnv,targetCut,domain,
    bodyIH _ _ _ _ _ ⟨updatedFrame,locals,allocated,vars,
      ssaMapOKInter next ssa names valid,updatedTables⟩⟩

/-- Internal exact Loop equation after its actual cut and body run. This
factors the original rebound evaluator, retaining its timeout/recursive/exit
branches rather than replacing them with a simplified evaluator. -/
private theorem loopAfterBody {width : Nat} [NeZero width] {C F : Type}
    (initial before after : WordSemStateFiniteExact width C F)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (result : Option (WordSemResult width))
    (cut : WordSemStateFiniteExact.cutState (names,.ln) initial = some before)
    (run : WordSemStateFiniteExact.evaluate body before = (result,after)) :
    WordSemStateFiniteExact.evaluate (.loop names body exits) initial =
      if wordSemContLoop result then
        if after.clock = 0 then (some .timeOut,WordSemStateFiniteExact.flushState true after)
        else WordSemStateFiniteExact.evaluate (wordSemSTOP (.loop names body exits))
          (WordSemStateFiniteExact.decClock after)
      else match (generalizing := false) result with
        | some (.break 0) => match WordSemStateFiniteExact.cutState (exits,.ln) after with
          | none => (some .error,after)
          | some exited => (none,exited)
        | _ => (wordSemExitLoop result,after) := by
  simp only [WordSemStateFiniteExact.evaluate_def_rebound]
  rw [cut]
  dsimp only
  rw [run]
  rfl

/-- All original terminal body cases, including positive Break/Continue labels,
leave the post-body state intact and apply the original exit-label operation. -/
private theorem loopTerminalRun {width : Nat} [NeZero width] {C F : Type}
    (initial before after : WordSemStateFiniteExact width C F)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (result : Option (WordSemResult width))
    (cut : WordSemStateFiniteExact.cutState (names,.ln) initial = some before)
    (run : WordSemStateFiniteExact.evaluate body before = (result,after))
    (terminal : wordSemContLoop result = false)
    (notExit : result ≠ some (.break 0)) :
    WordSemStateFiniteExact.evaluate (.loop names body exits) initial =
      (wordSemExitLoop result,after) := by
  rw [loopAfterBody initial before after names exits body result cut run]
  simp only [terminal,Bool.false_eq_true,if_false]

/-- Private factoring of the existing SSA simulation's result-sensitive locals
conclusion, with no separately claimed HOL original or altered semantics. -/
private def resultLocalsRel {width : Nat} [NeZero width] {α : Type}
    (next : Nat) (ssa : Spt Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target : Spt α) (result : Option (WordSemResult width)) : Prop :=
  match result with
  | none => ssaLocalsRel next ssa source target
  | some (.break label) => match tables[label]? with
    | none => True
    | some (map,_,exits) => Flapjack.WordAlloc.strongLocalsRel
      (optionLookup map) (sptDomain exits) source target
  | some (.continue label) => match tables[label]? with
    | none => True
    | some (map,names,_) => Flapjack.WordAlloc.strongLocalsRel
      (optionLookup map) (sptDomain names) source target
  | some _ => source = target

/-- Original positive Break/Continue body-result relation shifts past the
current Loop table; every other terminal result retains locals equality. -/
private theorem terminalResultLocals {width : Nat} [NeZero width] {α : Type}
    (nextBody nextOut : Nat) (mapBody mapOut refreshed : Spt Nat) (names exits : Spt Unit)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) (source target : Spt α)
    (result : Option (WordSemResult width))
    (related : resultLocalsRel nextBody mapBody ((refreshed,names,exits)::tables)
      source target result)
    (terminal : wordSemContLoop result = false) (notExit : result ≠ some (.break 0)) :
    resultLocalsRel nextOut mapOut tables source target (wordSemExitLoop result) := by
  cases result with
  | none => simp [wordSemContLoop] at terminal
  | some value =>
    cases value with
    | «break» label =>
      cases label with
      | zero => exact False.elim (notExit rfl)
      | succ label => simpa [resultLocalsRel,wordSemExitLoop] using related
    | «continue» label =>
      cases label with
      | zero => simp [wordSemContLoop] at terminal
      | succ label => simpa [resultLocalsRel,wordSemExitLoop] using related
    | result value values => exact related
    | exception value payload => exact related
    | timeOut => exact related
    | notEnoughSpace => exact related
    | finalFfi event => exact related
    | error => exact related

/-- Original Break-zero exit-cut assembly (original7373-7435). The body
compiler's actual output derives the final counter bound; the scoped body-IH
relation and original exit injection derive the target exit cut and full SSA
locals result. Neither successful target cut nor post-cut relation is assumed. -/
private theorem loopExitCut {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (refreshed mapOut : Spt Nat) (next nextOut : Nat) (names exits : Spt Unit)
    (body output : WordLangProgHOL (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (sourceEnv : Spt (WordLocW width))
    (produced : ssaCcTrans body (sptInter refreshed names) next
      ((refreshed,names,exits)::tables) = (output,mapOut,nextOut))
    (valid : ssaMapOK next refreshed) (allocated : isAllocVar next)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed)
      (sptDomain exits) source.locals target.locals)
    (injective : ∀ x y, sptDomain exits x → sptDomain exits y →
      optionLookup refreshed x = optionLookup refreshed y → x = y)
    (mapped : ∀ key, sptDomain exits key → sptDomain refreshed key)
    (bounded : ∀ key, sptDomain exits key → key < next)
    (cut : wordSemCutEnv (exits,.ln) source.locals = some sourceEnv) :
    ∃ targetEnv,
      wordSemCutEnv (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits,.ln)
        target.locals = some targetEnv ∧
      Flapjack.WordAlloc.wordStateEqRel {source with locals := sourceEnv}
        {target with locals := targetEnv} ∧
      ssaLocalsRel nextOut (sptInter refreshed exits) sourceEnv targetEnv := by
  have counter := (ssaCcTransProps body (sptInter refreshed names) next _ output mapOut nextOut
    produced ⟨ssaMapOKInter next refreshed names valid,allocated⟩).1
  obtain ⟨targetEnv,targetCut,_,related⟩ := loopEntryCut refreshed exits nextOut
    source.locals target.locals sourceEnv cut strong injective mapped
    (fun key inside => Nat.lt_of_lt_of_le (bounded key inside) counter)
  exact ⟨targetEnv,targetCut,by simpa only [Flapjack.WordAlloc.wordStateEqRel] using frame,related⟩

/-- Actual source recursive cut supplies the live source domain. This is the
inline guard argument in original7290-7320 and7510-7530. -/
private theorem recursiveImagePresent {α : Type} (ssa : Spt Nat) (names : Spt Unit)
    (source target env : Spt α)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source target)
    (cut : wordSemCutEnv (names,.ln) source = some env) :
    ∀ key, sptDomain names key → sptDomain target (optionLookup ssa key) := by
  have subset : ∀ key, sptDomain names key → sptDomain source key := by
    cases cuts : wordSemCutEnvs (names,.ln) source with
    | none => simp [wordSemCutEnv,cuts] at cut
    | some pair => exact (cutEnvsDomainSubset names .ln source pair cuts).1
  intro key inside
  obtain ⟨value,read⟩ := (sptMem_iff_lookup key source).mp (subset key inside)
  exact (sptMem_iff_lookup _ target).mpr ⟨value,strong key value ⟨inside,read⟩⟩

/-- Original recursive source-cut failure gives Error at the outer Loop. It is
an actual source execution fact used by the allowed Error disjunct, not a
hypothesis about the target result. -/
private theorem sourceRecursiveCutError {width : Nat} [NeZero width] {C F : Type}
    (initial before after : WordSemStateFiniteExact width C F)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (result : Option (WordSemResult width))
    (cut : WordSemStateFiniteExact.cutState (names,.ln) initial = some before)
    (run : WordSemStateFiniteExact.evaluate body before = (result,after))
    (continuing : wordSemContLoop result = true) (nonzero : after.clock ≠ 0)
    (recursiveCut : wordSemCutEnv (names,.ln) after.locals = none) :
    WordSemStateFiniteExact.evaluate (.loop names body exits) initial =
      (some .error,WordSemStateFiniteExact.decClock after) := by
  rw [loopAfterBody initial before after names exits body result cut run]
  simp only [continuing,if_true,nonzero,if_false,wordSemSTOP]
  have failed : WordSemStateFiniteExact.cutState (names,.ln)
      (WordSemStateFiniteExact.decClock after) = none := by
    change (match wordSemCutEnv (names,.ln) after.locals with
      | none => none | some env => some {(WordSemStateFiniteExact.decClock after) with locals := env}) = none
    rw [recursiveCut]
  simp only [WordSemStateFiniteExact.evaluate_def_rebound,failed]

/-- Original permutation stitching for the recursive NONE/Continue-zero cases
(original7350-7365,7532-7540). The recursive run is an internal clock-IH fact;
the body swap supplies a single source permutation for the outer Loop. -/
private theorem stitchRecursiveRun {width : Nat} [NeZero width] {C F : Type}
    (source after final : WordSemStateFiniteExact width C F)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (env : Spt (WordLocW width)) (bodyResult finalResult : Option (WordSemResult width))
    (recursivePermutation : Nat → Nat → Nat)
    (cut : wordSemCutEnv (names,.ln) source.locals = some env)
    (bodyRun : WordSemStateFiniteExact.evaluate body {source with locals := env} = (bodyResult,after))
    (notError : bodyResult ≠ some .error)
    (continuing : wordSemContLoop bodyResult = true) (nonzero : after.clock ≠ 0)
    (recursiveRun : WordSemStateFiniteExact.evaluate (.loop names body exits)
      {(WordSemStateFiniteExact.decClock after) with permute := recursivePermutation} =
        (finalResult,final)) :
    ∃ permutation,
      WordSemStateFiniteExact.evaluate (.loop names body exits) {source with permute := permutation} =
        (finalResult,final) := by
  have swap := WordSemStateFiniteExact.permute_swap_lemma body {source with locals := env}
    recursivePermutation
  rw [bodyRun] at swap
  obtain ⟨permutation,swappedRun⟩ := swap notError
  have stateCut : WordSemStateFiniteExact.cutState (names,.ln)
      {source with permute := permutation} = some {source with locals := env,permute := permutation} := by
    change (match wordSemCutEnv (names,.ln) source.locals with
      | none => none | some env => some {source with permute := permutation,locals := env}) = _
    rw [cut]
  refine ⟨permutation,?_⟩
  rw [loopAfterBody _ _ _ names exits body bodyResult stateCut swappedRun]
  simp only [continuing,if_true,nonzero,if_false,wordSemSTOP]
  exact recursiveRun

/-- Extract the original body-IH existential into actual compiled-body runs.
The compiler production equality is the original derived compile result;
all target evaluation and post-state facts are conclusions. -/
private theorem bodySimulationRun {width : Nat} [NeZero width] {C F : Type}
    (body output : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F) (ssa mapOut : Spt Nat)
    (next nextOut : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (produced : ssaCcTrans body ssa next tables = (output,mapOut,nextOut))
    (simulation : ssaSimulation body source target ssa next tables) :
    ∃ permutation,
      let sourceRun := WordSemStateFiniteExact.evaluate body {source with permute := permutation}
      let targetRun := WordSemStateFiniteExact.evaluate output target
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        resultLocalsRel nextOut mapOut tables sourceRun.2.locals targetRun.2.locals sourceRun.1 := by
  classical
  obtain ⟨permutation,related⟩ := simulation
  refine ⟨permutation,?_⟩
  dsimp only at related ⊢
  by_cases error : (WordSemStateFiniteExact.evaluate body {source with permute := permutation}).1 = some .error
  · exact Or.inl error
  · right
    simp only [error,if_false,produced] at related
    refine ⟨related.1,related.2.1,?_⟩
    generalize resultEq : (WordSemStateFiniteExact.evaluate body {source with permute := permutation}).1 = result at related ⊢
    cases result with
    | none => exact related.2.2
    | some value => cases value <;> exact related.2.2

/-- Internal same-clock decrement preserves the original full frame. -/
private theorem frameDecClock {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    Flapjack.WordAlloc.wordStateEqRel (WordSemStateFiniteExact.decClock source)
      (WordSemStateFiniteExact.decClock target) := by
  simp_all only [Flapjack.WordAlloc.wordStateEqRel,WordSemStateFiniteExact.decClock,and_true]

/-- Original clock-zero branch: both flushes retain the complete frame and
produce equal empty locals for the TimeOut result. -/
private theorem frameTimeoutFlush {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    Flapjack.WordAlloc.wordStateEqRel (WordSemStateFiniteExact.flushState true source)
      (WordSemStateFiniteExact.flushState true target) ∧
      (WordSemStateFiniteExact.flushState true source).locals =
        (WordSemStateFiniteExact.flushState true target).locals := by
  simp_all only [Flapjack.WordAlloc.wordStateEqRel,WordSemStateFiniteExact.flushState,and_true]

/-- Internal full-frame composition through the actual reconciliation run. -/
private theorem frameTrans {width : Nat} [NeZero width] {C F : Type}
    (source middle target : WordSemStateFiniteExact width C F)
    (first : Flapjack.WordAlloc.wordStateEqRel source middle)
    (second : Flapjack.WordAlloc.wordStateEqRel middle target) :
    Flapjack.WordAlloc.wordStateEqRel source target := by
  simp_all only [Flapjack.WordAlloc.wordStateEqRel,and_true]

/-- The production-shaped Skip constructor match implements the original
HOL equality test against Skip, for the evaluator equation used by Loop. -/
private theorem evaluateBodyFinalNative {width : Nat} [NeZero width] {C F : Type}
    (body moves : WordLangProgHOL (BitVec width))
    (before after : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (run : WordSemStateFiniteExact.evaluate body before = (result,after)) :
    WordSemStateFiniteExact.evaluate (match moves with | .skip => body | _ => .seq body moves) before =
      match (generalizing := false) result with
      | none => WordSemStateFiniteExact.evaluate moves after
      | some value => (some value,after) := by
  have original := evaluateBodyFinal body moves before after result run
  cases moves <;> simpa using original

/-- The original NONE body case executes actual reconciliation and derives
its strong entry relation and complete frame. This is the full derived step
needed before the recursive clock IH, with no target post-state assumption. -/
private theorem bodyNoneReconcile {width : Nat} [NeZero width] {C F : Type}
    (source before after : WordSemStateFiniteExact width C F)
    (body : WordLangProgHOL (BitVec width)) (mapOut refreshed : Spt Nat)
    (nextOut : Nat) (names : Spt Unit)
    (run : WordSemStateFiniteExact.evaluate body before = (none,after))
    (frame : Flapjack.WordAlloc.wordStateEqRel source after)
    (locals : ssaLocalsRel nextOut mapOut source.locals after.locals)
    (injection : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup refreshed x = optionLookup refreshed y → x = y) :
    ∃ reconciled,
      WordSemStateFiniteExact.evaluate
        (match ssaReconcile mapOut refreshed names with
          | .skip => body | moves => .seq body moves) before = (none,reconciled) ∧
      Flapjack.WordAlloc.wordStateEqRel source reconciled ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed)
        (sptDomain names) source.locals reconciled.locals := by
  obtain ⟨reconciled,reconcileRun,reconcileFrame,strong⟩ :=
    evaluateSSAReconcile nextOut mapOut refreshed names source.locals after ⟨locals,injection⟩
  refine ⟨reconciled,?_,frameTrans source after reconciled frame reconcileFrame,strong⟩
  generalize movesEq : ssaReconcile (width := width) mapOut refreshed names = moves at reconcileRun ⊢
  have native := evaluateBodyFinalNative body moves before after none run
  cases moves <;> simpa using native.trans reconcileRun

/-- Private packaging of the original helper's static premises for clock
induction. This is proof factoring, not an independently ported HOL carrier. -/
private structure LoopContext (width : Nat) [NeZero width] (C F : Type) where
  refreshed : Spt Nat
  next : Nat
  names : Spt Unit
  exits : Spt Unit
  body : WordLangProgHOL (BitVec width)
  output : WordLangProgHOL (BitVec width)
  mapOut : Spt Nat
  nextOut : Nat
  tables : List (Spt Nat × Spt Unit × Spt Unit)
  valid : ssaMapOK next refreshed
  allocated : isAllocVar next
  vars : everyVarHOL (fun key => decide (key < next)) body = true
  entryInjection : ∀ x y, sptDomain names x → sptDomain names y →
    optionLookup refreshed x = optionLookup refreshed y → x = y
  exitInjection : ∀ x y, sptDomain exits x → sptDomain exits y →
    optionLookup refreshed x = optionLookup refreshed y → x = y
  namesMapped : ∀ key, sptDomain names key → sptDomain refreshed key
  exitsMapped : ∀ key, sptDomain exits key → sptDomain refreshed key
  namesBound : ∀ key, sptDomain names key → key < next
  exitsBound : ∀ key, sptDomain exits key → key < next
  tableValid : ltOK tables
  produced : ssaCcTrans body (sptInter refreshed names) next
    ((refreshed,names,exits)::tables) = (output,mapOut,nextOut)
  bodyIH : ∀ (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
    (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
    Flapjack.WordAlloc.wordStateEqRel source target ∧
    ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
    everyVarHOL (fun key => decide (key < next)) body = true ∧
    ssaMapOK next ssa ∧ ltOK tables → ssaSimulation body source target ssa next tables

/-- Private clock-induction conclusion, spelling out the original source
permutation/Error disjunction and complete result-sensitive state relation. -/
private def loopPost {width : Nat} [NeZero width] {C F : Type}
    (ctx : LoopContext width C F) (source target : WordSemStateFiniteExact width C F)
    (targetResult : Option (WordSemResult width)) : Prop :=
  ∃ permutation,
    let run := WordSemStateFiniteExact.evaluate (.loop ctx.names ctx.body ctx.exits)
      {source with permute := permutation}
    run.1 = some .error ∨ run.1 = targetResult ∧
      Flapjack.WordAlloc.wordStateEqRel run.2 target ∧
      resultLocalsRel ctx.nextOut (sptInter ctx.refreshed ctx.exits) ctx.tables
        run.2.locals target.locals run.1

/-- Private spelling of the compiler's actual transformed Loop body. -/
private def loopBody {width : Nat} [NeZero width] {C F : Type}
    (ctx : LoopContext width C F) : WordLangProgHOL (BitVec width) :=
  match ssaReconcile ctx.mapOut ctx.refreshed ctx.names with
  | .skip => ctx.output
  | moves => .seq ctx.output moves

private theorem postOfRun {width : Nat} [NeZero width] {C F : Type}
    (ctx : LoopContext width C F) (source after target : WordSemStateFiniteExact width C F)
    (result targetResult : Option (WordSemResult width)) (permutation : Nat → Nat → Nat)
    (run : WordSemStateFiniteExact.evaluate (.loop ctx.names ctx.body ctx.exits)
      {source with permute := permutation} = (result,after))
    (related : result = some .error ∨ result = targetResult ∧
      Flapjack.WordAlloc.wordStateEqRel after target ∧
      resultLocalsRel ctx.nextOut (sptInter ctx.refreshed ctx.exits) ctx.tables
        after.locals target.locals result) : loopPost ctx source target targetResult := by
  refine ⟨permutation,?_⟩
  dsimp only
  rw [run]
  exact related

/-- Internal actual state cut equation, with all nonlocals fields retained. -/
private theorem cutStateWithLocals {width : Nat} [NeZero width] {C F : Type}
    (names : Spt Unit) (state : WordSemStateFiniteExact width C F) (env : Spt (WordLocW width))
    (cut : wordSemCutEnv (names,.ln) state.locals = some env) :
    WordSemStateFiniteExact.cutState (names,.ln) state = some {state with locals := env} := by
  unfold WordSemStateFiniteExact.cutState
  rw [cut]

private theorem bodyFinalSome {width : Nat} [NeZero width] {C F : Type}
    (ctx : LoopContext width C F) (before after : WordSemStateFiniteExact width C F)
    (result : WordSemResult width)
    (run : WordSemStateFiniteExact.evaluate ctx.output before = (some result,after)) :
    WordSemStateFiniteExact.evaluate (loopBody ctx) before = (some result,after) := by
  dsimp only [loopBody]
  generalize movesEq : ssaReconcile (width := width) ctx.mapOut ctx.refreshed ctx.names = moves
  have native := evaluateBodyFinalNative ctx.output moves before after (some result) run
  cases moves <;> simpa using native

/-- Complete derived original terminal-case assembly: actual source and target
Loop runs, popped-label locals relation and frame, under the original body-IH
postconditions. The full induction derives those internal facts. -/
private theorem loopTerminalCase {width : Nat} [NeZero width] {C F : Type}
    (ctx : LoopContext width C F)
    (source target sourceAfter targetAfter targetFinal : WordSemStateFiniteExact width C F)
    (sourceEnv targetEnv : Spt (WordLocW width))
    (bodyResult : WordSemResult width) (targetResult : Option (WordSemResult width))
    (permutation : Nat → Nat → Nat)
    (sourceCut : wordSemCutEnv (ctx.names,.ln) source.locals = some sourceEnv)
    (targetCut : wordSemCutEnv
      (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names,.ln)
      target.locals = some targetEnv)
    (sourceRun : WordSemStateFiniteExact.evaluate ctx.body
      {source with locals := sourceEnv,permute := permutation} = (some bodyResult,sourceAfter))
    (targetRun : WordSemStateFiniteExact.evaluate ctx.output {target with locals := targetEnv} =
      (some bodyResult,targetAfter))
    (frame : Flapjack.WordAlloc.wordStateEqRel sourceAfter targetAfter)
    (locals : resultLocalsRel (width := width) ctx.nextOut ctx.mapOut
      ((ctx.refreshed,ctx.names,ctx.exits)::ctx.tables) sourceAfter.locals targetAfter.locals (some bodyResult))
    (terminal : wordSemContLoop (some bodyResult) = false)
    (notExit : some bodyResult ≠ some (.break 0))
    (loopRun : WordSemStateFiniteExact.evaluate
      (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
        (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
      target = (targetResult,targetFinal)) : loopPost ctx source targetFinal targetResult := by
  have sourceStateCut := cutStateWithLocals ctx.names {source with permute := permutation} sourceEnv sourceCut
  have targetStateCut := cutStateWithLocals _ target targetEnv targetCut
  have sourceLoop := loopTerminalRun {source with permute := permutation}
    {source with locals := sourceEnv,permute := permutation} sourceAfter ctx.names ctx.exits ctx.body
    (some bodyResult) sourceStateCut sourceRun terminal notExit
  have targetLoop := loopTerminalRun target {target with locals := targetEnv} targetAfter
    (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
    (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits) (loopBody ctx)
    (some bodyResult) targetStateCut (bodyFinalSome ctx _ _ bodyResult targetRun) terminal notExit
  obtain ⟨resultEqual,stateEqual⟩ := Prod.mk.inj (targetLoop.symm.trans loopRun)
  subst targetResult targetFinal
  apply postOfRun ctx source sourceAfter targetAfter _ _ permutation sourceLoop
  exact Or.inr ⟨rfl,frame,terminalResultLocals ctx.nextOut ctx.nextOut ctx.mapOut
    (sptInter ctx.refreshed ctx.exits) ctx.refreshed ctx.names ctx.exits ctx.tables _ _
    (some bodyResult) locals terminal notExit⟩

private theorem loopBreakZeroRun {width : Nat} [NeZero width] {C F : Type}
    (initial before after : WordSemStateFiniteExact width C F)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (exitState : Option (WordSemStateFiniteExact width C F))
    (cut : WordSemStateFiniteExact.cutState (names,.ln) initial = some before)
    (run : WordSemStateFiniteExact.evaluate body before = (some (.break 0),after))
    (exitCut : WordSemStateFiniteExact.cutState (exits,.ln) after = exitState) :
    WordSemStateFiniteExact.evaluate (.loop names body exits) initial =
      match (generalizing := false) exitState with | none => (some .error,after) | some exited => (none,exited) := by
  rw [loopAfterBody initial before after names exits body (some (.break 0)) cut run]
  simp only [wordSemContLoop,Bool.false_eq_true,if_false,exitCut]

/-- Full derived Break-zero simulation assembly, including a failed source exit
cut and successful source/target cuts. The original body-IH exit relation and
compiler properties derive the complete final SSA relation. -/
private theorem loopBreakZeroCase {width : Nat} [NeZero width] {C F : Type}
    (ctx : LoopContext width C F)
    (source target sourceAfter targetAfter targetFinal : WordSemStateFiniteExact width C F)
    (sourceEnv targetEnv : Spt (WordLocW width))
    (targetResult : Option (WordSemResult width)) (permutation : Nat → Nat → Nat)
    (sourceCut : wordSemCutEnv (ctx.names,.ln) source.locals = some sourceEnv)
    (targetCut : wordSemCutEnv
      (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names,.ln)
      target.locals = some targetEnv)
    (sourceRun : WordSemStateFiniteExact.evaluate ctx.body
      {source with locals := sourceEnv,permute := permutation} = (some (.break 0),sourceAfter))
    (targetRun : WordSemStateFiniteExact.evaluate ctx.output {target with locals := targetEnv} =
      (some (.break 0),targetAfter))
    (frame : Flapjack.WordAlloc.wordStateEqRel sourceAfter targetAfter)
    (locals : resultLocalsRel (width := width) ctx.nextOut ctx.mapOut
      ((ctx.refreshed,ctx.names,ctx.exits)::ctx.tables) sourceAfter.locals targetAfter.locals (some (.break 0)))
    (loopRun : WordSemStateFiniteExact.evaluate
      (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
        (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
      target = (targetResult,targetFinal)) : loopPost ctx source targetFinal targetResult := by
  have sourceStateCut := cutStateWithLocals ctx.names {source with permute := permutation} sourceEnv sourceCut
  have targetStateCut := cutStateWithLocals _ target targetEnv targetCut
  have finalBodyRun := bodyFinalSome ctx _ _ (.break 0) targetRun
  cases exited : wordSemCutEnv (ctx.exits,.ln) sourceAfter.locals with
  | none =>
    have failed : WordSemStateFiniteExact.cutState (ctx.exits,.ln) sourceAfter = none := by
      unfold WordSemStateFiniteExact.cutState
      rw [exited]
    have sourceLoop := loopBreakZeroRun _ _ _ ctx.names ctx.exits ctx.body none sourceStateCut sourceRun failed
    exact postOfRun ctx source sourceAfter targetFinal _ targetResult permutation sourceLoop (Or.inl rfl)
  | some env =>
    have strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
        (sptDomain ctx.exits) sourceAfter.locals targetAfter.locals := by
      simpa [resultLocalsRel] using locals
    obtain ⟨targetExitEnv,targetExitCut,finalFrame,finalLocals⟩ :=
      loopExitCut sourceAfter targetAfter ctx.refreshed ctx.mapOut ctx.next ctx.nextOut
        ctx.names ctx.exits ctx.body ctx.output ctx.tables env ctx.produced ctx.valid ctx.allocated
        frame strong ctx.exitInjection ctx.exitsMapped ctx.exitsBound exited
    have sourceExitCut := cutStateWithLocals ctx.exits sourceAfter env exited
    have targetExitStateCut := cutStateWithLocals _ targetAfter targetExitEnv targetExitCut
    have sourceLoop := loopBreakZeroRun _ _ _ ctx.names ctx.exits ctx.body _ sourceStateCut sourceRun sourceExitCut
    have targetLoop := loopBreakZeroRun target {target with locals := targetEnv} targetAfter
      (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
      (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits) (loopBody ctx)
      _ targetStateCut finalBodyRun targetExitStateCut
    obtain ⟨resultEqual,stateEqual⟩ := Prod.mk.inj (targetLoop.symm.trans loopRun)
    subst targetResult targetFinal
    exact postOfRun ctx source {sourceAfter with locals := env} {targetAfter with locals := targetExitEnv}
      none none permutation sourceLoop (Or.inr ⟨rfl,finalFrame,finalLocals⟩)

/-- Full original recursive case assembly, shared by NONE after reconciliation
and Continue-zero without reconciliation. Actual target/body runs derive the
strict induction measure; source recursive cut and oracle stitching discharge
all next-state obligations. The clock IH is internal to the full theorem. -/
private theorem loopRecursiveCase {width : Nat} [NeZero width] {C F : Type}
    (ctx : LoopContext width C F)
    (source target sourceAfter targetAfter targetFinal : WordSemStateFiniteExact width C F)
    (sourceEnv targetEnv : Spt (WordLocW width))
    (bodyResult targetResult : Option (WordSemResult width)) (permutation : Nat → Nat → Nat)
    (sourceCut : wordSemCutEnv (ctx.names,.ln) source.locals = some sourceEnv)
    (targetCut : wordSemCutEnv
      (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names,.ln)
      target.locals = some targetEnv)
    (sourceRun : WordSemStateFiniteExact.evaluate ctx.body
      {source with locals := sourceEnv,permute := permutation} = (bodyResult,sourceAfter))
    (targetRun : WordSemStateFiniteExact.evaluate (loopBody ctx) {target with locals := targetEnv} =
      (bodyResult,targetAfter))
    (frame : Flapjack.WordAlloc.wordStateEqRel sourceAfter targetAfter)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
      (sptDomain ctx.names) sourceAfter.locals targetAfter.locals)
    (continuing : wordSemContLoop bodyResult = true)
    (loopRun : WordSemStateFiniteExact.evaluate
      (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
        (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
      target = (targetResult,targetFinal))

    (ih : ∀ (nextSource nextTarget : WordSemStateFiniteExact width C F),
      nextTarget.clock < target.clock →
      Flapjack.WordAlloc.wordStateEqRel nextSource nextTarget ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
        (sptDomain ctx.names) nextSource.locals nextTarget.locals ∧
      (∀ key, sptDomain ctx.names key → sptDomain nextTarget.locals (optionLookup ctx.refreshed key)) →
      ∀ nextResult nextFinal,
        WordSemStateFiniteExact.evaluate
          (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
            (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
          nextTarget = (nextResult,nextFinal) → loopPost ctx nextSource nextFinal nextResult) :
    loopPost ctx source targetFinal targetResult := by
  have sourceStateCut := cutStateWithLocals ctx.names {source with permute := permutation} sourceEnv sourceCut
  have targetStateCut := cutStateWithLocals _ target targetEnv targetCut
  have sourceLoop := loopAfterBody {source with permute := permutation}
    {source with locals := sourceEnv,permute := permutation} sourceAfter ctx.names ctx.exits ctx.body
    bodyResult sourceStateCut sourceRun
  have targetLoop := loopAfterBody target {target with locals := targetEnv} targetAfter
    (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
    (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits) (loopBody ctx)
    bodyResult targetStateCut targetRun
  have clock : targetAfter.clock = sourceAfter.clock := frame.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases zero : targetAfter.clock = 0
  · have sourceZero : sourceAfter.clock = 0 := clock.symm.trans zero
    have targetActual : WordSemStateFiniteExact.evaluate
        (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
          (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
        target = (some .timeOut,WordSemStateFiniteExact.flushState true targetAfter) := by
      simpa only [continuing,zero,if_true] using targetLoop
    obtain ⟨resultEqual,stateEqual⟩ := Prod.mk.inj (targetActual.symm.trans loopRun)
    subst targetResult targetFinal
    have sourceActual : WordSemStateFiniteExact.evaluate (.loop ctx.names ctx.body ctx.exits)
        {source with permute := permutation} = (some .timeOut,WordSemStateFiniteExact.flushState true sourceAfter) := by
      simpa only [continuing,sourceZero,if_true] using sourceLoop
    have finalRelations := frameTimeoutFlush sourceAfter targetAfter frame
    exact postOfRun ctx source _ _ _ _ permutation sourceActual (Or.inr ⟨rfl,finalRelations.1,finalRelations.2⟩)
  · have sourceNonzero : sourceAfter.clock ≠ 0 := fun equal => zero (clock.trans equal)
    cases recursiveCut : wordSemCutEnv (ctx.names,.ln) sourceAfter.locals with
    | none =>
      have failed := sourceRecursiveCutError {source with permute := permutation}
        {source with locals := sourceEnv,permute := permutation} sourceAfter ctx.names ctx.exits ctx.body
        bodyResult sourceStateCut sourceRun continuing sourceNonzero recursiveCut
      exact postOfRun ctx source _ targetFinal _ targetResult permutation failed (Or.inl rfl)
    | some recursiveEnv =>
      have images := recursiveImagePresent ctx.refreshed ctx.names sourceAfter.locals targetAfter.locals
        recursiveEnv strong recursiveCut
      have strict : (WordSemStateFiniteExact.decClock targetAfter).clock < target.clock := by
        have bound := (WordSemStateFiniteExact.evaluate_clock (loopBody ctx)
          {target with locals := targetEnv} bodyResult targetAfter targetRun).1
        simp only [WordSemStateFiniteExact.decClock]
        change targetAfter.clock ≤ target.clock at bound
        omega
      have recursiveTargetRun : WordSemStateFiniteExact.evaluate
          (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
            (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
          (WordSemStateFiniteExact.decClock targetAfter) = (targetResult,targetFinal) := by
        have actual : WordSemStateFiniteExact.evaluate
            (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
              (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits)) target =
            WordSemStateFiniteExact.evaluate
              (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
                (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
              (WordSemStateFiniteExact.decClock targetAfter) := by
          simpa only [continuing,if_true,zero,if_false,wordSemSTOP] using targetLoop
        exact actual.symm.trans loopRun
      obtain ⟨recursivePermutation,post⟩ := ih (WordSemStateFiniteExact.decClock sourceAfter)
        (WordSemStateFiniteExact.decClock targetAfter) strict
        ⟨frameDecClock sourceAfter targetAfter frame,strong,images⟩ targetResult targetFinal recursiveTargetRun
      dsimp only at post
      cases recursiveSourceRun : WordSemStateFiniteExact.evaluate (.loop ctx.names ctx.body ctx.exits)
          {(WordSemStateFiniteExact.decClock sourceAfter) with permute := recursivePermutation} with
      | mk recursiveResult recursiveAfter =>
        rw [recursiveSourceRun] at post
        have noError : bodyResult ≠ some .error := by
          intro error
          rw [error] at continuing
          simp [wordSemContLoop] at continuing
        obtain ⟨outerPermutation,outerRun⟩ := stitchRecursiveRun {source with permute := permutation}
          sourceAfter recursiveAfter ctx.names ctx.exits ctx.body sourceEnv bodyResult recursiveResult
          recursivePermutation sourceCut sourceRun noError continuing sourceNonzero recursiveSourceRun
        exact postOfRun ctx source recursiveAfter targetFinal recursiveResult targetResult outerPermutation outerRun post

/-- Private factoring of precisely the original helper's state-dependent input
premises; all remaining original premises are stored in LoopContext. -/
private def loopInput {width : Nat} [NeZero width] {C F : Type}
    (ctx : LoopContext width C F) (source target : WordSemStateFiniteExact width C F) : Prop :=
  Flapjack.WordAlloc.wordStateEqRel source target ∧
  Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed) (sptDomain ctx.names)
    source.locals target.locals ∧
  (∀ key, sptDomain ctx.names key → sptDomain target.locals (optionLookup ctx.refreshed key))

/-- Original full helper proof assembled by strong induction on the actual
compiled Loop's clock. This private packaging will be exposed by the complete
source-shaped theorem, without adding target/post-state assumptions. -/
private theorem loopContextCorrect {width : Nat} [NeZero width] {C F : Type}
    (ctx : LoopContext width C F) (source target targetFinal : WordSemStateFiniteExact width C F)
    (targetResult : Option (WordSemResult width)) (input : loopInput ctx source target)
    (targetRun : WordSemStateFiniteExact.evaluate
      (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
        (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
      target = (targetResult,targetFinal)) : loopPost ctx source targetFinal targetResult := by
  have solve : ∀ clock, ∀ (source target : WordSemStateFiniteExact width C F),
      target.clock = clock → loopInput ctx source target → ∀ targetResult targetFinal,
      WordSemStateFiniteExact.evaluate
        (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
          (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
        target = (targetResult,targetFinal) → loopPost ctx source targetFinal targetResult := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock ih =>
      intro source target clockEq input targetResult targetFinal targetRun
      obtain ⟨frame,strong,images⟩ := input
      have clockIH : ∀ (nextSource nextTarget : WordSemStateFiniteExact width C F),
          nextTarget.clock < target.clock → loopInput ctx nextSource nextTarget → ∀ nextResult nextFinal,
          WordSemStateFiniteExact.evaluate
            (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names)
              (loopBody ctx) (Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits))
            nextTarget = (nextResult,nextFinal) → loopPost ctx nextSource nextFinal nextResult := by
        intro nextSource nextTarget strict nextInput nextResult nextFinal nextRun
        exact ih nextTarget.clock (by rwa [← clockEq]) nextSource nextTarget rfl nextInput nextResult nextFinal nextRun
      obtain ⟨initialTargetEnv,initialTargetCut⟩ := targetEntryCutExists ctx.refreshed ctx.names target.locals images
      cases sourceCut : wordSemCutEnv (ctx.names,.ln) source.locals with
      | none =>
        have failed := sourceEntryCutError source ctx.names ctx.exits ctx.body target.permute sourceCut
        exact postOfRun ctx source _ targetFinal _ targetResult target.permute failed (Or.inl rfl)
      | some sourceEnv =>
        obtain ⟨targetEnv,targetCut,_,simulation⟩ := loopBodyEntry source target ctx.refreshed ctx.next
          ctx.names ctx.exits ctx.body ctx.tables sourceEnv frame strong ctx.valid ctx.allocated ctx.vars
          ctx.entryInjection ctx.exitInjection ctx.namesMapped ctx.namesBound ctx.tableValid ctx.bodyIH sourceCut
        have sameEnv := Option.some.inj (initialTargetCut.symm.trans targetCut)
        subst targetEnv
        obtain ⟨permutation,bodyPost⟩ := bodySimulationRun ctx.body ctx.output
          {source with locals := sourceEnv} {target with locals := initialTargetEnv}
          (sptInter ctx.refreshed ctx.names) ctx.mapOut ctx.next ctx.nextOut
          ((ctx.refreshed,ctx.names,ctx.exits)::ctx.tables) ctx.produced simulation
        dsimp only at bodyPost
        cases sourceBody : WordSemStateFiniteExact.evaluate ctx.body
            {source with locals := sourceEnv,permute := permutation} with
        | mk sourceResult sourceAfter =>
          cases targetBody : WordSemStateFiniteExact.evaluate ctx.output {target with locals := initialTargetEnv} with
          | mk targetBodyResult targetAfter =>
            rw [sourceBody,targetBody] at bodyPost
            dsimp only at bodyPost
            rcases bodyPost with error | ⟨resultEqual,bodyFrame,bodyLocals⟩
            · subst sourceResult
              have failed := sourceBodyError source sourceAfter ctx.names ctx.exits ctx.body sourceEnv
                permutation sourceCut sourceBody
              exact postOfRun ctx source sourceAfter targetFinal _ targetResult permutation failed (Or.inl rfl)
            · subst targetBodyResult
              cases sourceResult with
              | none =>
                obtain ⟨reconciled,finalBodyRun,finalFrame,entryLocals⟩ := bodyNoneReconcile sourceAfter
                  {target with locals := initialTargetEnv} targetAfter ctx.output ctx.mapOut ctx.refreshed
                  ctx.nextOut ctx.names targetBody bodyFrame bodyLocals ctx.entryInjection
                exact loopRecursiveCase ctx source target sourceAfter reconciled targetFinal sourceEnv initialTargetEnv
                  none targetResult permutation sourceCut targetCut sourceBody finalBodyRun finalFrame entryLocals rfl
                  targetRun clockIH
              | some value =>
                by_cases continueZero : value = .continue 0
                · subst value
                  have entryLocals : Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
                      (sptDomain ctx.names) sourceAfter.locals targetAfter.locals := by
                    simpa [resultLocalsRel] using bodyLocals
                  exact loopRecursiveCase ctx source target sourceAfter targetAfter targetFinal sourceEnv initialTargetEnv
                    (some (.continue 0)) targetResult permutation sourceCut targetCut sourceBody
                    (bodyFinalSome ctx _ _ (.continue 0) targetBody) bodyFrame entryLocals rfl targetRun clockIH
                · by_cases breakZero : value = .break 0
                  · subst value
                    exact loopBreakZeroCase ctx source target sourceAfter targetAfter targetFinal sourceEnv initialTargetEnv
                      targetResult permutation sourceCut targetCut sourceBody targetBody bodyFrame bodyLocals targetRun
                  · have terminal : wordSemContLoop (some value) = false := by
                      cases value <;> try rfl
                      rename_i label
                      have nonzero : label ≠ 0 := fun equal => continueZero (by rw [equal])
                      simp [wordSemContLoop,nonzero]
                    have notExit : some value ≠ some (.break 0) := fun equal => breakZero (Option.some.inj equal)
                    exact loopTerminalCase ctx source target sourceAfter targetAfter targetFinal sourceEnv initialTargetEnv
                      value targetResult permutation sourceCut targetCut sourceBody targetBody bodyFrame bodyLocals
                      terminal notExit targetRun
  exact solve target.clock source target rfl input targetResult targetFinal targetRun

namespace LoopIterationWitnesses

/-- Canonical roundtrip of the imported native state finite maps. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopIterationWitnesses

/-- Complete Loop iteration simulation with the original universal body-IH,
actual target evaluation premise, existential source permutation, Error
alternative, frame and all result-sensitive locals conclusions. The original
EVERY bounds are retained over toAList keys. The constructor test for Skip is
HOL's reconciliation if/else, as used by the actual compiler. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_Loop_helper"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransLoopHelper {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (refreshed : Spt Nat) (next : Nat) (names exits : Spt Unit)
    (body output : WordLangProgHOL (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) (mapOut : Spt Nat) (nextOut : Nat)
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed) (sptDomain names)
        source.locals target.locals ∧
      (∀ key, sptDomain names key → sptDomain target.locals (optionLookup refreshed key)) ∧
      ssaMapOK next refreshed ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next)) body = true ∧
      (∀ x y, sptDomain names x → sptDomain names y →
        optionLookup refreshed x = optionLookup refreshed y → x = y) ∧
      (∀ x y, sptDomain exits x → sptDomain exits y →
        optionLookup refreshed x = optionLookup refreshed y → x = y) ∧
      (∀ key, sptDomain names key → sptDomain refreshed key) ∧
      (∀ key, sptDomain exits key → sptDomain refreshed key) ∧
      (∀ key ∈ (sptToAList names).map Prod.fst, key < next) ∧
      (∀ key ∈ (sptToAList exits).map Prod.fst, key < next) ∧
      ltOK tables ∧
      ssaCcTrans body (sptInter refreshed names) next ((refreshed,names,exits)::tables) =
        (output,mapOut,nextOut) ∧
      (∀ (st ct : WordSemStateFiniteExact width C F) (ssa : Spt Nat)
        (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
        Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na ssa st.locals ct.locals ∧
        isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
        ssaMapOK na ssa ∧ ltOK lt → ssaSimulation body st ct ssa na lt)) :
    let moves := ssaReconcile (width := width) mapOut refreshed names
    let finalBody := match moves with | .skip => output | moves => .seq output moves
    ∀ result finalState,
      WordSemStateFiniteExact.evaluate
        (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names)
          finalBody (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits))
        target = (result,finalState) →
      ∃ permutation,
        let run := WordSemStateFiniteExact.evaluate (.loop names body exits)
          {source with permute := permutation}
        run.1 = some .error ∨ run.1 = result ∧
          Flapjack.WordAlloc.wordStateEqRel run.2 finalState ∧
          match run.1 with
          | none => ssaLocalsRel nextOut (sptInter refreshed exits) run.2.locals finalState.locals
          | some (.break label) =>
            match tables[label]? with
            | none => True
            | some (ssa,_,exitNames) => Flapjack.WordAlloc.strongLocalsRel
                (optionLookup ssa) (sptDomain exitNames) run.2.locals finalState.locals
          | some (.continue label) =>
            match tables[label]? with
            | none => True
            | some (ssa,entryNames,_) => Flapjack.WordAlloc.strongLocalsRel
                (optionLookup ssa) (sptDomain entryNames) run.2.locals finalState.locals
          | some _ => run.2.locals = finalState.locals := by
  obtain ⟨frame,strong,images,valid,allocated,vars,entryInjection,exitInjection,
    namesMapped,exitsMapped,namesBound,exitsBound,tableValid,produced,bodyIH⟩ := premises
  let ctx : LoopContext width C F :=
    { refreshed, next, names, exits, body, output, mapOut, nextOut, tables,
      valid, allocated, vars, entryInjection, exitInjection, namesMapped, exitsMapped,
      namesBound := fun key member => namesBound key ((sptMemMapFstToAList names key).mpr member),
      exitsBound := fun key member => exitsBound key ((sptMemMapFstToAList exits key).mpr member),
      tableValid, produced, bodyIH }
  dsimp only
  intro result finalState targetRun
  exact loopContextCorrect ctx source target finalState result ⟨frame,strong,images⟩ targetRun

end Flapjack.Compiler.Backend.WordAlloc
