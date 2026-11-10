module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateCodeGrowth
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic

@[expose] public section

/-! Safe extensions of proof-side closure code maps. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

/-- Labels installed by an oracle entry. -/
def oracleCodeNames {C : Type} (entry : C × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))) : Set Nat :=
  { key | key ∈ entry.2.2.map Prod.fst }

/-- The domain of a closure code map. -/
def codeDomain (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Set Nat :=
  { key | code.lookup key ≠ none }

/-- The target differs only in its larger code map, whose labels precede
future oracle labels. This candidate uses the finite-support carrier and
remains untagged pending HOL correspondence review. -/
def CodeExtension {C F : Type} (source target : State C F) : Prop :=
  target = { source with code := target.code } ∧ source.code.submap target.code ∧
    oracleMonotonic oracleCodeNames (· < ·) (codeDomain target.code) source.compileOracle

/-- Updating corresponding code maps with identical entries preserves the
lookup submap relation, including duplicate keys. -/
theorem codeSubmap_updateList (source target : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (entries : List (Nat × Nat × ClosLang.Exp)) (submap : source.submap target) :
    (source.updateListEq entries).submap (target.updateListEq entries) := by
  intro key entry found
  simp only [HolFiniteMapExact.lookup_updateListEq] at found ⊢
  have aux : ∀ (xs : List (Nat × Nat × ClosLang.Exp)) (left right : Nat → Option (Nat × ClosLang.Exp)),
      (∀ k v, left k = some v → right k = some v) →
      ∀ k v, FUPDATE_LIST_HOL left xs k = some v → FUPDATE_LIST_HOL right xs k = some v := by
    intro xs
    induction xs with
    | nil => intro left right related k v h; exact related k v h
    | cons head tail ih =>
      intro left right related k v h
      rw [FUPDATE_LIST_HOL_cons] at h ⊢
      apply ih _ _ ?_ k v h
      intro k v equal
      by_cases same : k = head.1
      · simpa [FUPDATE_HOL, same] using equal
      · simpa [FUPDATE_HOL, same] using related k v (by simpa [FUPDATE_HOL, same] using equal)
  exact aux entries source.lookup target.lookup submap key entry found

/-- Every label in a code map after a list update came from the old code
map or from the list of newly installed entries. -/
theorem codeDomain_updateList_subset (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (entries : List (Nat × Nat × ClosLang.Exp)) (key : Nat)
    (member : key ∈ codeDomain (code.updateListEq entries)) :
    key ∈ codeDomain code ∨ key ∈ entries.map Prod.fst := by
  by_cases added : key ∈ entries.map Prod.fst
  · exact Or.inr added
  · left
    simp only [codeDomain, Set.mem_ofPred_eq] at member ⊢
    have same := FLOOKUP_FUPDATE_LIST_HOL_not_mem code.lookup entries key added
    change FUPDATE_LIST_HOL code.lookup entries key = code.lookup key at same
    rw [HolFiniteMapExact.lookup_updateListEq, same] at member
    exact member

/-- Advancing the oracle after adding its current entries preserves its
ordering invariant over the enlarged code domain. -/
theorem oracleMonotonic_after_install {C : Type} (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (oracle : CompileOracle C) (entries : List (Nat × Nat × ClosLang.Exp))
    (entryEq : (oracle 0).2.2 = entries)
    (ordered : oracleMonotonic oracleCodeNames (· < ·) (codeDomain code) oracle) :
    oracleMonotonic oracleCodeNames (· < ·) (codeDomain (code.updateListEq entries)) (holShiftSeq 1 oracle) := by
  constructor
  · intro i j x y lt xmem ymem
    apply ordered.1 (i + 1) (j + 1) x y (by omega)
    · simpa [holShiftSeq, Nat.add_comm] using xmem
    · simpa [holShiftSeq, Nat.add_comm] using ymem
  · intro i x y xmem ymem
    rcases codeDomain_updateList_subset code entries x xmem with old | fresh
    · apply ordered.2 (i + 1) x y old
      simpa [holShiftSeq, Nat.add_comm] using ymem
    · apply ordered.1 0 (i + 1) x y (by omega)
      · simpa [oracleCodeNames, entryEq] using fresh
      · simpa [holShiftSeq, Nat.add_comm] using ymem

/-- Successful code lookup is preserved when the code map is extended. -/
theorem findCode_of_codeSubmap {α : Type} (source target : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (location : Nat) (args : List α) (result : List α × ClosLang.Exp)
    (submap : source.submap target) (found : findCode location args source = some result) :
    findCode location args target = some result := by
  unfold findCode at found ⊢
  cases lookup : source.lookup location with
  | none => simp [lookup] at found
  | some entry =>
    have nextLookup := submap _ _ lookup
    simpa [lookup, nextLookup] using found

/-- A non-type-error installation has the same result in a safe code
extension and preserves the extension relation. -/
theorem doInstall_codeExtension {C F : Type} (values : List Value) (source target next : State C F)
    (result : Result (List ClosLang.Exp) Value)
    (run : doInstall values source = (result, next)) (noType : result ≠ .err (.abort .typeError))
    (related : CodeExtension source target) :
    ∃ targetNext, doInstall values target = (result, targetNext) ∧ CodeExtension next targetNext := by
  classical
  obtain ⟨same, submap, ordered⟩ := related
  have clockEq : target.clock = source.clock := by rw [same]
  have compilerEq : target.compile = source.compile := by rw [same]
  have oracleEq : target.compileOracle = source.compileOracle := by rw [same]
  obtain ⟨byteValue, wordValue, bytes, words, config, expressions, auxiliary, nextConfig,
    valuesEq, bytesRun, wordsRun, oracleRun, compileRun, fresh, nodup, nextConfigEq, nonempty, nextEq, resultEq⟩ :=
      doInstall_nonType_parts values source next result run noType
  have targetFresh : ∀ key ∈ auxiliary.map Prod.fst, target.code.lookup key = none := by
    intro key member
    cases targetLookup : target.code.lookup key with
    | none => rfl
    | some entry =>
      have targetMember : key ∈ codeDomain target.code := by simp [codeDomain, targetLookup]
      have oracleMember : key ∈ oracleCodeNames (source.compileOracle 0) := by
        simpa [oracleCodeNames, oracleRun] using member
      have impossible := ordered.2 0 key key targetMember oracleMember
      omega
  let targetNext := { target with code := target.code.updateListEq auxiliary, compileOracle := holShiftSeq 1 target.compileOracle, clock := target.clock - 1 }
  refine ⟨targetNext, ?_, ?_⟩
  · have targetOracle : target.compileOracle 0 = (config, expressions, auxiliary) := by rw [oracleEq, oracleRun]
    have targetCompile : target.compile config (expressions, auxiliary) = some (bytes, words, nextConfig) := by
      rw [compilerEq, compileRun]
    have targetConfig : (holShiftSeq 1 target.compileOracle 0).1 = nextConfig := by simpa [oracleEq] using nextConfigEq
    have targetFreshEntries : ∀ key arity body, (key, arity, body) ∈ auxiliary → target.code.lookup key = none := by
      intro key arity body member
      apply targetFresh key
      exact List.mem_map.mpr ⟨(key, arity, body), member, rfl⟩
    rw [resultEq, valuesEq]
    by_cases zero : source.clock = 0
    · have targetZero : target.clock = 0 := by simpa [clockEq] using zero
      simp [doInstall, bytesRun, wordsRun, targetOracle, nodup, targetCompile, targetConfig,
        nonempty, zero, targetZero, targetNext]
      exact targetFreshEntries
    · have targetNonzero : target.clock ≠ 0 := by simpa [clockEq] using zero
      simp [doInstall, bytesRun, wordsRun, targetOracle, nodup, targetCompile, targetConfig,
        nonempty, zero, targetNonzero, targetNext]
      exact targetFreshEntries
  · rw [nextEq]
    refine ⟨?_, codeSubmap_updateList source.code target.code auxiliary submap, ?_⟩
    · dsimp only [targetNext]
      rw [same]
    · simpa [targetNext, oracleEq] using
        oracleMonotonic_after_install target.code source.compileOracle auxiliary (by simp [oracleRun]) ordered

/-- Equal clock updates preserve a code extension. -/
theorem codeExtension_withClock {C F : Type} (source target : State C F) (clock : Nat)
    (related : CodeExtension source target) :
    CodeExtension { source with clock := clock } { target with clock := clock } := by
  obtain ⟨same, submap, ordered⟩ := related
  refine ⟨?_, submap, ordered⟩
  rw [same]

/-- Equal reference-map updates preserve a code extension. -/
theorem codeExtension_withRefs {C F : Type} (source target : State C F)
    (refs : HolFiniteMapExact Nat (Ref Value)) (related : CodeExtension source target) :
    CodeExtension { source with refs := refs } { target with refs := refs } := by
  obtain ⟨same, submap, ordered⟩ := related
  refine ⟨?_, submap, ordered⟩
  rw [same]

/-- Decrementing related clocks preserves a code extension. -/
theorem codeExtension_decClock {C F : Type} (source target : State C F) (amount : Nat)
    (related : CodeExtension source target) : CodeExtension (decClock amount source) (decClock amount target) := by
  have sameClock : target.clock = source.clock := by rw [related.1]
  simpa [decClock, sameClock] using codeExtension_withClock source target (source.clock - amount) related

end Flapjack.Compiler.Backend.ClosSem
