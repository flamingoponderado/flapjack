import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompileCodeInfo
import Flapjack.Compiler.Backend.Semantics.StackSem.Semantics
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClockIoEventsMono
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompileSemantics

namespace Flapjack.Compiler.Backend.StackRawCall.CompileSemantics
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Association-list map lookup used by the original whole-program proof.
Flapjack infrastructure; no separate HOL declaration. -/
private theorem lookupMap {α β : Type} (key : Nat) (f : α → β)
    (code : List (Nat × α)) :
    sptAListLookup key (code.map fun entry => (entry.1, f entry.2)) =
      (sptAListLookup key code).map f := by
  induction code with
  | nil => rfl
  | cons entry code ih =>
      obtain ⟨name, body⟩ := entry
      by_cases equal : key = name <;> simp [sptAListLookup, equal, ih]

/-- Derive the actual initial relation from the original distinct-key/code
premises. Target code and each independent frame witness are constructed;
no initial or final simulation relation is assumed. Flapjack proof support
for the original compile_semantics proof, without a separate HOL declaration. -/
theorem initialRelation {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code) :
    stateRel (collectInfo code .ln) source
      {source with code := sptFromAList (compile code)} := by
  refine ⟨sptFromAList (compile code), ?_, rfl, ?_, ?_⟩
  · rw [sourceCode]; exact domainFromAListCompile code
  · rw [sourceCode]; exact stateOkCollectInfo code distinct
  · intro key body found
    refine ⟨collectInfo code .ln, ?_, ?_⟩
    · rw [sourceCode]; exact stateOkCollectInfo code distinct
    · rw [sourceCode, sptLookup_sptFromAList] at found
      rw [sptLookup_sptFromAList]
      unfold compile
      rw [lookupMap, found]
      rfl

/-- The full simulation theorem constructs an entry-call target execution
at an additional clock and preserves the complete FFI state. The only run
premise is the source run; all target witnesses come from comp_correct.
Flapjack proof support without a separately named HOL original. -/
theorem entrySimulation {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {source with clock := clock}) =
      (result, post)) (nonError : result ≠ some .error) :
    ∃ extra targetPost, StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {source with code := sptFromAList (compile code), clock := clock + extra}) =
      (result, targetPost) ∧ targetPost.ffi = post.ffi := by
  have relation := initialRelation code {source with clock := clock} distinct sourceCode
  obtain ⟨extra, targetPost, space, postRelation, targetRun, _⟩ :=
    (FullCompCorrect.compCorrect (.call none (.inl start) none)
      {source with clock := clock}
      {source with clock := clock, code := sptFromAList (compile code)}
      (collectInfo code .ln) result post ⟨run, nonError, relation⟩).2
  refine ⟨extra, {targetPost with stackSpace := space}, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · obtain ⟨_, _, equality, _⟩ := postRelation
    subst targetPost
    rfl

/-- Checked codec of the actual imported owning state, used by the map
representation qualifier. Flapjack infrastructure with no HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

open StackSemEvaluate Compiler.Backend.StackProps
open StackAlloc.CompileSemanticsSupport

/-- Full original observational rawcall pass theorem. All four original
premises and the complete Fail/termination/divergence behaviour are retained.
The proof derives the target runs from full comp_correct, uses native clock
stability and event monotonicity, and compares the actual cofinal event chains.
The shared semanticsAux_shift lemma is Flapjack proof infrastructure; its
simulation premise is discharged here, never added to this theorem's premises.
The evaluator inherits the reviewed real-carrier limit (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileSemantics {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start : Nat) (distinct : (code.map Prod.fst).Nodup)
    (_useStack : source.useStack = true) (sourceCode : source.code = sptFromAList code)
    (nonFail : semantics start source ≠ .fail) :
    semantics start {source with code := sptFromAList (compile code)} =
      semantics start source := by
  have good : ∀ clock, ¬ Bad (evaluate
      ((.call none (.inl start) none : HolProg width), {source with clock := clock})).1 := by
    intro clock bad
    apply nonFail
    rw [semantics_eq_aux]
    unfold semanticsAux
    exact if_pos ⟨clock, bad⟩
  rw [semantics_eq_aux, semantics_eq_aux]
  apply semanticsAux_shift
  · exact good
  · intro clock
    rcases run : evaluate
      ((.call none (.inl start) none : HolProg width), {source with clock := clock}) with
      ⟨result, post⟩
    have nonError : result ≠ some .error := by
      rintro rfl
      exact good clock (by rw [run]; simp [Bad])
    obtain ⟨extra, targetPost, targetRun, ffi⟩ :=
      entrySimulation code source start clock result post distinct sourceCode run nonError
    exact ⟨extra, by rw [targetRun], by rw [targetRun]; exact ffi⟩
  · intro clock extra nonTimeout
    have boost := evaluateAddClock extra _
      ({source with code := sptFromAList (compile code), clock := clock}) _ _
      ⟨rfl, nonTimeout⟩
    exact ⟨by rw [boost]; rfl, by rw [boost]; rfl⟩
  · intro clock extra
    exact EvaluateAddClockIoEventsMono.evaluateAddClockIoEventsMono extra _
      {source with clock := clock}
  · intro clock extra
    exact EvaluateAddClockIoEventsMono.evaluateAddClockIoEventsMono extra _
      {source with code := sptFromAList (compile code), clock := clock}

end Flapjack.Compiler.Backend.StackRawCall.CompileSemantics
