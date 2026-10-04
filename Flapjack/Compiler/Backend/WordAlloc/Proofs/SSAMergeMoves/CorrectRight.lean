import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveFrame
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.MoveHead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StateRelation

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack induction infrastructure for the empty merge list. The faithful
Move evaluator leaves the entire state fixed, including permutation. -/
theorem mergeRightEmptyEvaluation {width : Nat} [NeZero width] {C F : Type}
    (priority : Nat) (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.move priority []) state = (none, state) := by
  simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
    WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert]

/-- Flapjack induction infrastructure: updating a fresh register leaves every
old binding below the original counter unchanged. No HOL port tag is claimed. -/
theorem mergeRightOldLocalsStep {α : Type} (start fresh : Nat)
    (value : α) (before after : Spt α) (bound : start ≤ fresh)
    (preserved : ∀ key payload, key < start →
      sptLookup key before = some payload → sptLookup key after = some payload) :
    ∀ key payload, key < start → sptLookup key before = some payload →
      sptLookup key (sptInsert fresh value after) = some payload := by
  intro key payload below found
  have different : key ≠ fresh := by omega
  rw [sptLookup_sptInsert_ne _ _ _ _ different]
  exact preserved key payload below found

/-- Flapjack induction infrastructure: the complete state relation ignores
locals, so a fresh locals write preserves all its conjuncts. This helper has
no separate HOL original and is not a correctness case port. -/
theorem mergeRightStateStep {width : Nat} [NeZero width] {C F : Type}
    (before after : WordSemStateFiniteExact width C F)
    (locals : Spt (WordLocW width))
    (related : Flapjack.WordAlloc.wordStateEqRel before after) :
    Flapjack.WordAlloc.wordStateEqRel before { after with locals := locals } := by
  exact related

/-- Flapjack induction infrastructure for the unequal-register merge branch.
The source locals stay fixed while the selected name is remapped to the fresh
counter. This is not a separate HOL declaration or a tagged correctness case. -/
theorem mergeRightLocalsStep {α : Type} (next name old : Nat) (value : α)
    (ssa : Spt Nat) (source target : Spt α)
    (valid : ssaMapOK next ssa)
    (related : ssaLocalsRel next ssa source target)
    (mapped : sptLookup name ssa = some old)
    (present : sptLookup old target = some value) :
    ssaLocalsRel (next + 4) (sptInsert name next ssa) source
      (sptInsert next value target) := by
  rcases related with ⟨domains, values⟩
  refine ⟨?_, ?_⟩
  · intro key register lookup
    by_cases equal : key = name
    · subst key
      rw [sptLookup_sptInsert_same] at lookup
      cases lookup
      exact (sptMem_iff_lookup next _).mpr ⟨value, sptLookup_sptInsert_same _ _ _⟩
    · rw [sptLookup_sptInsert_ne _ _ _ _ equal] at lookup
      rcases (sptMem_iff_lookup register target).mp (domains key register lookup) with
        ⟨payload, found⟩
      have different : register ≠ next := by
        have bound := (valid key register lookup).2
        omega
      exact (sptMem_iff_lookup register _).mpr
        ⟨payload, by rw [sptLookup_sptInsert_ne _ _ _ _ different]; exact found⟩
  · intro key payload found
    rcases values key payload found with ⟨domain, matchingLookup, bound⟩
    rcases (sptMem_iff_lookup key ssa).mp domain with ⟨register, lookup⟩
    refine ⟨?_, ?_, fun allocated => by have := bound allocated; omega⟩
    · by_cases equal : key = name
      · subst key
        exact (sptMem_iff_lookup name _).mpr ⟨next, sptLookup_sptInsert_same _ _ _⟩
      · exact (sptMem_iff_lookup key _).mpr
          ⟨register, by rw [sptLookup_sptInsert_ne _ _ _ _ equal]; exact lookup⟩
    · by_cases equal : key = name
      · subst key
        simp only [mapped, Option.getD_some] at matchingLookup
        have same : value = payload := Option.some.inj (present.symm.trans matchingLookup)
        simp only [sptLookup_sptInsert_same, Option.getD_some, same]
      · have different : register ≠ next := by
          have bound := (valid key register lookup).2
          omega
        simp only [lookup, Option.getD_some] at matchingLookup
        rw [sptLookup_sptInsert_ne _ _ _ _ equal]
        simp only [lookup, Option.getD_some]
        rw [sptLookup_sptInsert_ne _ _ _ _ different]
        exact matchingLookup

/-- Flapjack induction packaging for the complete five-conjunct empty case.
This is infrastructure, not a separately tagged HOL case or final port. -/
theorem mergeRightEmptyCorrect {width : Nat} [NeZero width]
    {C₁ F₁ C₂ F₂ : Type} (next : Nat) (left right : Spt Nat)
    (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂) (priority : Nat)
    (related : ssaLocalsRel next right source.locals target.locals) :
    let merged := mergeMoves [] left right next
    let evaluated := WordSemStateFiniteExact.evaluate (.move priority merged.2.1) target
    evaluated.1 = none ∧
      (∀ key, key ∉ ([] : List Nat) →
        sptLookup key merged.2.2.2.2 = sptLookup key right) ∧
      (∀ key value, key < next → sptLookup key target.locals = some value →
        sptLookup key evaluated.2.locals = some value) ∧
      ssaLocalsRel merged.2.2.1 merged.2.2.2.2 source.locals evaluated.2.locals ∧
      Flapjack.WordAlloc.wordStateEqRel target evaluated.2 := by
  simp only [mergeMoves, mergeRightEmptyEvaluation]
  exact ⟨True.intro, fun _ _ => True.intro, fun _ _ _ found => found, related,
    by simp [Flapjack.WordAlloc.wordStateEqRel]⟩

namespace CorrectRightWitnesses

/-- Flapjack canonical carrier roundtrip for the translated state map fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CorrectRightWitnesses

/-- Full right-side native merge correctness. Original inferred state types
share the word dimension only; code and FFI types remain independent. Every
original premise and all five conclusions are retained. The evaluator inherits
its documented rational-cut FP boundary, although this Move branch only reads
and writes locals. Guarded SOME lookups make the THE fallback irrelevant. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem mergeMovesCorrectR {width : Nat} [NeZero width]
    {C₁ F₁ C₂ F₂ : Type} (names : List Nat) (next : Nat)
    (left right : Spt Nat) (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂) (priority : Nat)
    (allocated : isAllocVar next) (distinct : names.Nodup)
    (valid : ssaMapOK next right) :
    let merged := mergeMoves names left right next
    ssaLocalsRel next right source.locals target.locals →
    let evaluated := WordSemStateFiniteExact.evaluate (.move priority merged.2.1) target
    evaluated.1 = none ∧
      (∀ key, key ∉ names → sptLookup key merged.2.2.2.2 = sptLookup key right) ∧
      (∀ key value, key < next → sptLookup key target.locals = some value →
        sptLookup key evaluated.2.locals = some value) ∧
      ssaLocalsRel merged.2.2.1 merged.2.2.2.2 source.locals evaluated.2.locals ∧
      Flapjack.WordAlloc.wordStateEqRel target evaluated.2 := by
  induction names with
  | nil =>
    dsimp only
    intro related
    exact mergeRightEmptyCorrect next left right source target priority related
  | cons name names ih =>
    have absent : name ∉ names := (List.nodup_cons.mp distinct).1
    have tail := ih distinct.tail
    dsimp only at tail ⊢
    intro related
    have tailResult := tail related
    generalize hm : mergeMoves names left right next = merged at tailResult
    rcases merged with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
    simp only at tailResult
    generalize he : WordSemStateFiniteExact.evaluate (.move priority rightMoves) target = evaluated at tailResult
    rcases evaluated with ⟨result, after⟩
    simp only at tailResult
    rcases tailResult with ⟨resultNone, unchanged, preserved, localsRelated, stateRelated⟩
    subst result
    simp only [mergeMoves, hm]
    cases hl : sptLookup name leftTree with
    | none =>
      simp only [he]
      exact ⟨True.intro, fun key outside => unchanged key (fun member => outside (List.mem_cons_of_mem name member)),
        preserved, localsRelated, stateRelated⟩
    | some leftRegister =>
      cases hr : sptLookup name rightTree with
      | none =>
        simp only [he]
        exact ⟨True.intro, fun key outside => unchanged key (fun member => outside (List.mem_cons_of_mem name member)),
          preserved, localsRelated, stateRelated⟩
      | some rightRegister =>
        simp only
        split
        · simp only [he]
          exact ⟨True.intro, fun key outside => unchanged key (fun member => outside (List.mem_cons_of_mem name member)),
            preserved, localsRelated, stateRelated⟩
        · have frame := mergeMovesFrame names next left right allocated
          have bounds := mergeMovesFst names next left right
          rw [hm] at frame bounds
          simp only at frame bounds
          have rightValid := frame.2.2.2 valid
          have originalLookup : sptLookup name right = some rightRegister :=
            (unchanged name absent).symm.trans hr
          have registerBound := (valid name rightRegister originalLookup).2
          have sourcePresent := related.1 name rightRegister originalLookup
          have sourceNotWritten : rightRegister ∉ rightMoves.map Prod.fst := by
            intro member
            have bound := (bounds.2.2 rightRegister member).2
            omega
          have destinationNotWritten : counter ∉ rightMoves.map Prod.fst := by
            intro member
            have bound := (bounds.2.2 counter member).1
            omega
          have head := movEvalHead priority rightMoves target after counter rightRegister
            he sourcePresent sourceNotWritten destinationNotWritten
          simp only [head]
          refine ⟨True.intro, ?_, ?_, ?_, ?_⟩
          · intro key outside
            have different : key ≠ name := by
              intro equal; subst key; exact outside (List.mem_cons_self)
            rw [sptLookup_sptInsert_ne _ _ _ _ different]
            exact unchanged key (fun member => outside (List.mem_cons_of_mem name member))
          · exact mergeRightOldLocalsStep next counter _ target.locals after.locals bounds.1 preserved
          · rcases (sptMem_iff_lookup rightRegister target.locals).mp sourcePresent with ⟨value, found⟩
            have afterFound := preserved rightRegister value registerBound found
            simpa only [found, Option.getD_some] using
              mergeRightLocalsStep counter name rightRegister value rightTree source.locals after.locals
                rightValid localsRelated hr afterFound
          · exact mergeRightStateStep target after _ stateRelated

end Flapjack.Compiler.Backend.WordAlloc
