module

public import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MoveStoreConsts

@[expose] public section

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

/-- Exact HOL `get_var_ignore` (`word_allocProofScript.sml:5215-5226`): a
read is unchanged by `set_vars` when the variable is absent from the names
written, with the original conjunction as one premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_var_ignore"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem getVarIgnore {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (cst : WordSemStateFiniteExact width C F) (y : WordLocW width)
    (ls : List Nat) (a : List (WordLocW width))
    (h : WordSemStateFiniteExact.getVar x cst = some y ∧ x ∉ ls ∧
      ls.length = a.length) :
    WordSemStateFiniteExact.getVar x (WordSemStateFiniteExact.setVars ls a cst) = some y := by
  induction ls generalizing a with
  | nil =>
      cases a with
      | nil =>
          simpa [WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.getVar,
            LoopSemStateFiniteExact.sptAlistInsert] using h.1
      | cons v vs => simp at h
  | cons n ns ih =>
      cases a with
      | nil => simp at h
      | cons v vs =>
          have hx : x ≠ n := by
            intro hx
            exact h.2.1 (hx ▸ List.mem_cons_self)
          have hlen : ns.length = vs.length := by simpa using h.2.2
          have ihv := ih vs ⟨h.1, (fun hm => h.2.1 (List.mem_cons_of_mem n hm)), hlen⟩
          simp only [WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.getVar,
            LoopSemStateFiniteExact.sptAlistInsert]
          rw [sptLookup_sptInsert_ne n x v _ hx]
          simpa [WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.getVar] using ihv

/-- Exact HOL `get_var_set_vars_notin` (`word_allocProofScript.sml:6310-6319`):
writing names that exclude the read variable leaves the read unchanged. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_var_set_vars_notin"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem getVarSetVarsNotin {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (ls : List Nat) (vs : List (WordLocW width))
    (st : WordSemStateFiniteExact width C F)
    (h : v ∉ ls ∧ ls.length = vs.length) :
    WordSemStateFiniteExact.getVar v (WordSemStateFiniteExact.setVars ls vs st) =
      WordSemStateFiniteExact.getVar v st := by
  induction ls generalizing vs with
  | nil =>
      simp [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert]
  | cons n ns ih =>
      cases vs with
      | nil =>
          simp [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert]
      | cons w ws =>
          have hv : v ≠ n := by
            intro hv
            exact h.1 (hv ▸ List.mem_cons_self)
          have hlen : ns.length = ws.length := by simpa using h.2
          have ihv := ih ws ⟨(fun hm => h.1 (List.mem_cons_of_mem n hm)), hlen⟩
          simp only [WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.getVar,
            LoopSemStateFiniteExact.sptAlistInsert]
          rw [sptLookup_sptInsert_ne n v w _ hv]
          simpa [WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.getVar] using ihv

/-- Exact HOL `get_vars_NOT_MEM` (`word_allocProofScript.sml:6425-6430`):
inserting a variable that is not read leaves a multi-read unchanged. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_NOT_MEM"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem getVarsNotMem {width : Nat} [NeZero width] {C F : Type}
    (h : Nat) (xs : List Nat) (cs : WordSemStateFiniteExact width C F)
    (h' : WordLocW width) (ys : Spt (WordLocW width))
    (hnot : h ∉ xs) :
    WordSemStateFiniteExact.getVars xs { cs with locals := sptInsert h h' ys } =
      WordSemStateFiniteExact.getVars xs { cs with locals := ys } := by
  induction xs with
  | nil => rfl
  | cons n ns ih =>
      have hn : n ≠ h := by
        intro hn
        exact hnot (hn ▸ List.mem_cons_self)
      have hlook :
          WordSemStateFiniteExact.getVar n { cs with locals := sptInsert h h' ys } =
            WordSemStateFiniteExact.getVar n { cs with locals := ys } := by
        simp only [WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne h n h' ys hn]
      have ihv := ih (fun hm => hnot (List.mem_cons_of_mem n hm))
      simp only [WordSemStateFiniteExact.getVars, hlook, ihv]

/-- Flapjack infrastructure for `get_vars_eq_alist_insert`: a lookup at a name
written by the association-list insert does not depend on the initial tree.
HOL discharges the same step with `lookup_insert` in its proof. -/
private theorem sptLookup_sptAlistInsert_rest_irrelevant {α : Type} (ns : List Nat)
    (vs : List α) (rest other : Spt α) (lengths : ns.length = vs.length) :
    ∀ x, x ∈ ns →
      sptLookup x (LoopSemStateFiniteExact.sptAlistInsert ns vs other) =
        sptLookup x (LoopSemStateFiniteExact.sptAlistInsert ns vs rest) := by
  induction ns generalizing vs with
  | nil =>
      intro x hx
      simp at hx
  | cons m ms ih =>
      cases vs with
      | nil =>
          simp at lengths
      | cons w ws =>
          have hlen : ms.length = ws.length := by simpa using lengths
          intro x hx
          simp only [LoopSemStateFiniteExact.sptAlistInsert]
          by_cases hxm : x = m
          · subst x
            rw [sptLookup_sptInsert_same, sptLookup_sptInsert_same]
          · rw [sptLookup_sptInsert_ne m x w _ hxm,
              sptLookup_sptInsert_ne m x w _ hxm]
            exact ih ws hlen x (by
              rcases List.mem_cons.mp hx with h | h
              · exact absurd h hxm
              · exact h)

/-- Exact HOL `get_vars_eq_alist_insert` (`word_allocProofScript.sml:6432-6445`):
when every read agrees with the association-list insert, the multi-read returns
the inserted values, with the original three-way conjunction as one premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_eq_alist_insert"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem getVarsEqAlistInsert {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) (rest : Spt (WordLocW width))
    (regs : List Nat) (l : List (WordLocW width))
    (h : regs.Nodup ∧ regs.length = l.length ∧
      ∀ x, x ∈ regs → sptLookup x st.locals =
        sptLookup x (LoopSemStateFiniteExact.sptAlistInsert regs l rest)) :
    WordSemStateFiniteExact.getVars regs st = some l := by
  induction regs generalizing l rest with
  | nil =>
      cases l with
      | nil => simp [WordSemStateFiniteExact.getVars]
      | cons v vs => simp at h
  | cons r rs ih =>
      cases l with
      | nil => simp at h
      | cons v vs =>
          have hnodup := List.nodup_cons.mp h.1
          have hlen : rs.length = vs.length := by simpa using h.2.1
          have hr : sptLookup r st.locals = some v := by
            have h1 := h.2.2 r (by simp)
            rw [h1]
            simp only [LoopSemStateFiniteExact.sptAlistInsert]
            exact sptLookup_sptInsert_same r v _
          have hrec : ∀ x, x ∈ rs → sptLookup x st.locals =
              sptLookup x (LoopSemStateFiniteExact.sptAlistInsert rs vs
                (sptInsert r v rest)) := by
            intro x hx
            have hxr : x ≠ r := by
              intro hxr
              exact hnodup.1 (hxr ▸ hx)
            have h1 := h.2.2 x (List.mem_cons_of_mem r hx)
            rw [h1]
            simp only [LoopSemStateFiniteExact.sptAlistInsert]
            rw [sptLookup_sptInsert_ne r x v _ hxr]
            exact (sptLookup_sptAlistInsert_rest_irrelevant rs vs rest
              (sptInsert r v rest) hlen x hx).symm
          have ihv := ih (sptInsert r v rest) vs ⟨hnodup.2, hlen, hrec⟩
          simp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, hr]
          rw [ihv]

end Flapjack.Compiler.Backend.WordAlloc
