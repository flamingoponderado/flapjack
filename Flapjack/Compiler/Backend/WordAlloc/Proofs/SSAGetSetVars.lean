import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MoveStoreConsts

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack infrastructure exposing the original list-insert append equation.
It is a generic native-tree lemma, not a separate CakeML declaration port. -/
theorem ssaAlistInsertAppend {α : Type} (names tailNames : List Nat)
    (values suffix : List α) (target : Spt α) (lengths : names.length = values.length) :
    LoopSemStateFiniteExact.sptAlistInsert (names ++ tailNames) (values ++ suffix) target =
      LoopSemStateFiniteExact.sptAlistInsert names values
        (LoopSemStateFiniteExact.sptAlistInsert tailNames suffix target) := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at lengths
  | cons name names ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
          simp only [List.cons_append, LoopSemStateFiniteExact.sptAlistInsert]
          rw [ih values lengths]



/-- Flapjack infrastructure for duplicate-free simultaneous tree writes.
There is no independent CakeML declaration being claimed by this lemma. -/
theorem ssaAlistInsertLookupMember {α : Type} (names : List Nat) (values : List α)
    (target : Spt α) (distinct : names.Nodup) (lengths : names.length = values.length) :
    ∀ key value, (key, value) ∈ names.zip values →
      sptLookup key (LoopSemStateFiniteExact.sptAlistInsert names values target) = some value := by
  induction names generalizing values with
  | nil => simp
  | cons name names ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
          have hd := List.nodup_cons.mp distinct
          have hl : names.length = values.length := by simpa using lengths
          intro key payload member
          simp only [List.zip_cons_cons, List.mem_cons] at member
          simp only [LoopSemStateFiniteExact.sptAlistInsert]
          rcases member with equal | member
          · cases equal
            exact sptLookup_sptInsert_same _ _ _
          · have different : key ≠ name := by
              intro equal
              apply hd.1
              exact equal ▸ (List.of_mem_zip member).1
            rw [sptLookup_sptInsert_ne _ _ _ _ different]
            exact ih values hd.2 hl key payload member

/-- Flapjack infrastructure connecting successful individual reads to the
actual WordSem list read. It assumes lookup facts, not a read result. -/
theorem ssaGetVarsOfZip {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (values : List (WordLocW width))
    (state : WordSemStateFiniteExact width C F) (lengths : names.length = values.length)
    (lookups : ∀ key value, (key, value) ∈ names.zip values →
      sptLookup key state.locals = some value) :
    WordSemStateFiniteExact.getVars names state = some values := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at lengths
  | cons name names ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
          have hl : names.length = values.length := by simpa using lengths
          have head := lookups name value (by simp)
          have tail := ih values hl (by
            intro key payload member
            exact lookups key payload (by simp [member]))
          simp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
            head, tail]

namespace GetSetVarsWitnesses

/-- Checked canonical state carrier roundtrip for the named map fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end GetSetVarsWitnesses

/-- Full original generalized list-insert/read statement with its four
conjunctive premises and arbitrary replacement locals. Fresh original types
confirm that names are natural lists and values/locals share the state word
dimension. Native list insertion preserves original prefix priority. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_list_insert_eq_gen"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem getVarsListInsertEqGen {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) (names : List Nat)
    (values : List (WordLocW width)) (locals : Spt (WordLocW width))
    (beforeNames : List Nat) (beforeValues : List (WordLocW width))
    (h : names.length = values.length ∧ names.Nodup ∧
      beforeNames.length = beforeValues.length ∧
      (∀ key ∈ names, key ∉ beforeNames)) :
    WordSemStateFiniteExact.getVars names
      { state with locals := (LoopSemStateFiniteExact.sptAlistInsert
          (beforeNames ++ names) (beforeValues ++ values) locals) } = some values := by
  apply ssaGetVarsOfZip names values _ h.1
  intro key value member
  change sptLookup key (LoopSemStateFiniteExact.sptAlistInsert
    (beforeNames ++ names) (beforeValues ++ values) locals) = some value
  rw [ssaAlistInsertAppend beforeNames names beforeValues values locals h.2.2.1]
  rw [Flapjack.WordAlloc.sptLookup_sptAlistInsert_notMem _ _ _ key
    (h.2.2.2 key (List.of_mem_zip member).1)]
  exact ssaAlistInsertLookupMember names values locals h.2.1 h.1 key value member



/-- Full original set/read statement with both original premises, the real
native WordSem read/write operations, and generic state code/FFI carriers.
Fresh literal original proof and inferred types were checked before tagging. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_set_vars_eq"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem getVarsSetVarsEq {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (values : List (WordLocW width))
    (state : WordSemStateFiniteExact width C F)
    (h : names.Nodup ∧ values.length = names.length) :
    WordSemStateFiniteExact.getVars names (WordSemStateFiniteExact.setVars names values state) =
      some values := by
  have result := getVarsListInsertEqGen state names values state.locals [] []
    ⟨h.2.symm, h.1, rfl, by simp⟩
  simpa only [List.nil_append, WordSemStateFiniteExact.setVars] using result

end Flapjack.Compiler.Backend.WordAlloc
