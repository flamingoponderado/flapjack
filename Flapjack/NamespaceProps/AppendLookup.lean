module

public import Flapjack.NamespaceProps.Append

@[expose] public section

/-! Successful lookups in appended namespaces. -/
namespace Flapjack.NamespaceHOL

/-- Flapjack infrastructure: a failed single-module lookup also fails the whole
long lookup at that module. -/
private theorem nsLookup_long_none_of_mod_none {M N V : Type} [DecidableEq M] [DecidableEq N]
    (e : Namespace M N V) (mn : M) (rest : Ident M N)
    (h : nsLookupMod e [mn] = none) : nsLookup e (.long mn rest) = none := by
  cases e with
  | bind values modules =>
    cases found : modules.lookup mn with
    | none => simp [nsLookup, found]
    | some nested => simp [nsLookupMod, found] at h

/-- Flapjack infrastructure: a failed single-module lookup fails every module
path that starts with that module. -/
private theorem nsLookupMod_cons_none {M N V : Type} [DecidableEq M]
    (e : Namespace M N V) (mn : M) (rest : List M)
    (h : nsLookupMod e [mn] = none) : nsLookupMod e (mn :: rest) = none := by
  cases e with
  | bind values modules =>
    cases found : modules.lookup mn with
    | none => simp [nsLookupMod, found]
    | some nested => simp [nsLookupMod, found] at h

/-- A successful lookup in an appended namespace comes either from the first
namespace or from the second after every nonempty prefix of the identifier's
module path misses in the first. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_nsAppend_some"]
theorem nsLookup_nsAppend_some {M N V : Type} [DecidableEq M] [DecidableEq N]
    (e1 : Namespace M N V) (id : Ident M N) (e2 : Namespace M N V) (v : V) :
    nsLookup (nsAppend e1 e2) id = some v ↔
      nsLookup e1 id = some v ∨
      (nsLookup e1 id = none ∧ nsLookup e2 id = some v ∧
        ∀ p1 p2, p1 ≠ [] → idToMods id = p1 ++ p2 → nsLookupMod e1 p1 = none) := by
  induction id with
  | short name =>
    cases e1 with
    | bind values1 modules1 =>
      cases e2 with
      | bind values2 modules2 =>
        have vacuous : ∀ p1 p2 : List M, p1 ≠ [] → ([] : List M) = p1 ++ p2 →
            nsLookupMod (.bind values1 modules1) p1 = none := by
          intro p1 p2 ne same
          cases p1 with
          | nil => exact absurd rfl ne
          | cons head tail => simp at same
        simp only [nsAppend, nsLookup, List.lookup_append, idToMods]
        cases h : values1.lookup name with
        | some w =>
          constructor
          · intro found
            exact Or.inl found
          · intro disj
            rcases disj with same | ⟨noneEq, _⟩
            · exact same
            · simp at noneEq
        | none =>
          constructor
          · intro found
            exact Or.inr ⟨rfl, found, vacuous⟩
          · intro disj
            rcases disj with same | ⟨_, found, _⟩
            · simp at same
            · exact found
  | long mn rest ih =>
    rw [nsLookup_append_long, idToMods]
    cases modFound : nsLookupMod e1 [mn] with
    | some module =>
      have notAll : ¬ (∀ p1 p2 : List M, p1 ≠ [] → mn :: idToMods rest = p1 ++ p2 →
          nsLookupMod e1 p1 = none) := by
        intro all
        have instantiated := all [mn] (idToMods rest) (by simp) (by rfl)
        rw [modFound] at instantiated
        simp at instantiated
      constructor
      · intro found
        exact Or.inl found
      · intro disj
        rcases disj with same | ⟨_, _, all⟩
        · exact same
        · exact absurd all notAll
    | none =>
      have firstNone : nsLookup e1 (.long mn rest) = none :=
        nsLookup_long_none_of_mod_none e1 mn rest modFound
      have allNone : ∀ p1 p2 : List M, p1 ≠ [] → mn :: idToMods rest = p1 ++ p2 →
          nsLookupMod e1 p1 = none := by
        intro p1 p2 ne same
        cases p1 with
        | nil => exact absurd rfl ne
        | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at same
          rw [← same.1]
          exact nsLookupMod_cons_none e1 mn tail modFound
      constructor
      · intro found
        exact Or.inr ⟨firstNone, found, allNone⟩
      · intro disj
        rcases disj with same | ⟨_, found, _⟩
        · rw [firstNone] at same
          simp at same
        · exact found

/-- A failed lookup in an appended namespace requires the first namespace to
miss and either the second to miss or a prefix of the module path to shadow the
first namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_nsAppend_none"]
theorem nsLookup_nsAppend_none {M N V : Type} [DecidableEq M] [DecidableEq N]
    (e1 : Namespace M N V) (id : Ident M N) (e2 : Namespace M N V) :
    nsLookup (nsAppend e1 e2) id = none ↔
      nsLookup e1 id = none ∧
      (nsLookup e2 id = none ∨
        ∃ (p1 p2 : List M) (e3 : Namespace M N V), p1 ≠ [] ∧ idToMods id = p1 ++ p2 ∧
          nsLookupMod e1 p1 = some e3) := by
  induction id with
  | short name =>
    cases e1 with
    | bind values1 modules1 =>
      cases e2 with
      | bind values2 modules2 =>
        have impossible : ∀ p1 p2 : List M, p1 ≠ [] → ([] : List M) = p1 ++ p2 → False := by
          intro p1 p2 ne same
          cases p1 with
          | nil => exact absurd rfl ne
          | cons head tail => simp at same
        simp only [nsAppend, nsLookup, List.lookup_append, idToMods, Option.or_eq_none_iff]
        constructor
        · intro h2
          exact ⟨h2.1, Or.inl h2.2⟩
        · intro h2
          obtain ⟨first, second | ⟨p1, p2, e3, ne, same, _⟩⟩ := h2
          · exact ⟨first, second⟩
          · exact absurd same (impossible p1 p2 ne)
  | long mn rest ih =>
    rw [nsLookup_append_long, idToMods]
    cases modFound : nsLookupMod e1 [mn] with
    | some module =>
      constructor
      · intro found
        exact ⟨found, Or.inr ⟨[mn], idToMods rest, module, by simp, rfl, modFound⟩⟩
      · intro h2
        exact h2.1
    | none =>
      have firstNone : nsLookup e1 (.long mn rest) = none :=
        nsLookup_long_none_of_mod_none e1 mn rest modFound
      have noSome : ¬ ∃ (p1 p2 : List M) (e3 : Namespace M N V), p1 ≠ [] ∧
          mn :: idToMods rest = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3 := by
        rintro ⟨p1, p2, e3, ne, same, someFound⟩
        cases p1 with
        | nil => exact absurd rfl ne
        | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at same
          rw [← same.1] at someFound
          rw [nsLookupMod_cons_none e1 mn tail modFound] at someFound
          simp at someFound
      constructor
      · intro found
        exact ⟨firstNone, Or.inl found⟩
      · intro h2
        rcases h2.2 with same | bad
        · exact same
        · exact absurd bad noSome

/-- A failed module lookup in an appended namespace requires the first
namespace to miss and either the second to miss or a prefix of the path to
shadow the first namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookupMod_nsAppend_none"]
theorem nsLookupMod_nsAppend_none {M N V : Type} [DecidableEq M]
    (e1 e2 : Namespace M N V) (path : List M) :
    nsLookupMod (nsAppend e1 e2) path = none ↔
      nsLookupMod e1 path = none ∧
      (nsLookupMod e2 path = none ∨
        ∃ (p1 p2 : List M) (e3 : Namespace M N V), p1 ≠ [] ∧ path = p1 ++ p2 ∧
          nsLookupMod e1 p1 = some e3) := by
  cases path with
  | nil =>
    simp only [nsLookupMod]
    constructor
    · intro h
      simp at h
    · intro h
      simp at h
  | cons mn rest =>
    rw [nsLookupMod_append_cons]
    cases modFound : nsLookupMod e1 [mn] with
    | some module =>
      constructor
      · intro found
        exact ⟨found, Or.inr ⟨[mn], rest, module, by simp, rfl, modFound⟩⟩
      · intro h2
        exact h2.1
    | none =>
      have firstNone : nsLookupMod e1 (mn :: rest) = none :=
        nsLookupMod_cons_none e1 mn rest modFound
      have noSome : ¬ ∃ (p1 p2 : List M) (e3 : Namespace M N V), p1 ≠ [] ∧
          mn :: rest = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3 := by
        rintro ⟨p1, p2, e3, ne, same, someFound⟩
        cases p1 with
        | nil => exact absurd rfl ne
        | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at same
          rw [← same.1] at someFound
          rw [nsLookupMod_cons_none e1 mn tail modFound] at someFound
          simp at someFound
      constructor
      · intro found
        exact ⟨firstNone, Or.inl found⟩
      · intro h2
        rcases h2.2 with same | bad
        · exact same
        · exact absurd bad noSome

/-- A successful module lookup in an appended namespace at the empty path is the
append itself; otherwise it comes from the first namespace or from the second
after every nonempty prefix misses in the first. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookupMod_nsAppend_some"]
theorem nsLookupMod_nsAppend_some {M N V : Type} [DecidableEq M]
    (e1 e2 : Namespace M N V) (path : List M) (x : Namespace M N V) :
    (nsLookupMod (nsAppend e1 e2) path = some x ↔
      if path = [] then x = nsAppend e1 e2 else
        nsLookupMod e1 path = some x ∨
        (nsLookupMod e2 path = some x ∧
          ∀ p1 p2, p1 ≠ [] → path = p1 ++ p2 → nsLookupMod e1 p1 = none)) := by
  cases path with
  | nil => simp [nsLookupMod, eq_comm]
  | cons mn rest =>
    rw [nsLookupMod_append_cons]
    simp only [List.cons_ne_nil, if_false]
    cases modFound : nsLookupMod e1 [mn] with
    | some module =>
      have notAll : ¬ ∀ p1 p2 : List M, p1 ≠ [] → mn :: rest = p1 ++ p2 →
          nsLookupMod e1 p1 = none := by
        intro all
        have instantiated := all [mn] rest (by simp) (by rfl)
        rw [modFound] at instantiated
        simp at instantiated
      constructor
      · intro found
        exact Or.inl found
      · intro disj
        rcases disj with same | ⟨_, all⟩
        · exact same
        · exact absurd all notAll
    | none =>
      have firstNone : nsLookupMod e1 (mn :: rest) = none :=
        nsLookupMod_cons_none e1 mn rest modFound
      have allNone : ∀ p1 p2 : List M, p1 ≠ [] → mn :: rest = p1 ++ p2 →
          nsLookupMod e1 p1 = none := by
        intro p1 p2 ne same
        cases p1 with
        | nil => exact absurd rfl ne
        | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at same
          rw [← same.1]
          exact nsLookupMod_cons_none e1 mn tail modFound
      constructor
      · intro found
        exact Or.inr ⟨found, allNone⟩
      · intro disj
        rcases disj with same | ⟨found, _⟩
        · rw [firstNone] at same
          simp at same
        · exact found

/-- A predicate holding throughout an appended namespace holds in the first
namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll_nsAppend_left"]
theorem nsAll_nsAppend_left {M N V : Type} [DecidableEq M] [DecidableEq N]
    (P : Ident M N → V → Prop) (n1 n2 : Namespace M N V)
    (all : nsAll P (nsAppend n1 n2)) : nsAll P n1 := by
  intro id value found
  exact all id value ((nsLookup_nsAppend_some n1 id n2 value).mpr (Or.inl found))

/-- Appending a sub-related namespace to a self-related one keeps the
sub-relation. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsSub_nsAppend2"]
theorem nsSub_nsAppend2 {M N V : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → V → Prop) (e1 : Namespace M N V) (e2 : Namespace M N V)
    (e2' : Namespace M N V) (premise : nsSub R e1 e1 ∧ nsSub R e2 e2') :
    nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := by
  obtain ⟨firstSub, secondSub⟩ := premise
  constructor
  · intro id value found
    rcases (nsLookup_nsAppend_some e1 id e2 value).mp found with
      first | ⟨firstNone, secondFound, prefixNone⟩
    · obtain ⟨w, wFound, rel⟩ := firstSub.1 id value first
      exact ⟨w, (nsLookup_nsAppend_some e1 id e2' w).mpr (Or.inl wFound), rel⟩
    · obtain ⟨w, wFound, rel⟩ := secondSub.1 id value secondFound
      exact ⟨w, (nsLookup_nsAppend_some e1 id e2' w).mpr
        (Or.inr ⟨firstNone, wFound, prefixNone⟩), rel⟩
  · intro path absent
    obtain ⟨firstNone, secondNone | ⟨p1, p2, e3, ne, same, someFound⟩⟩ :=
      (nsLookupMod_nsAppend_none e1 e2' path).mp absent
    · exact (nsLookupMod_nsAppend_none e1 e2 path).mpr
        ⟨firstNone, Or.inl (secondSub.2 path secondNone)⟩
    · exact (nsLookupMod_nsAppend_none e1 e2 path).mpr
        ⟨firstNone, Or.inr ⟨p1, p2, e3, ne, same, someFound⟩⟩

end Flapjack.NamespaceHOL
