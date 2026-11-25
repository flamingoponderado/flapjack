module

public import Flapjack.NamespaceProps
public import Flapjack.NamespaceProps.AlistLookup
public import Flapjack.NamespaceProps.AppendLookup
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Image

@[expose] public section

/-! Original namespace-domain characterizations. -/
namespace Flapjack.NamespaceHOL

/-- The value domain of a bound namespace inserts the short name. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDom_nsBind"]
theorem nsDom_nsBind {M N V : Type} [DecidableEq M] [DecidableEq N]
    (x : N) (y : V) (n : Namespace M N V) :
    nsDom (nsBind x y n) = Set.insert (.short x) (nsDom n) := by
  funext id
  apply propext
  change (∃ v, nsLookup (nsBind x y n) id = some v) ↔
    (id = .short x ∨ ∃ v, nsLookup n id = some v)
  cases id with
  | short name =>
    by_cases same : name = x
    · subst x
      rw [nsLookup_nsBind.1]
      simp
    · have ne : (Ident.short name : Ident M N) ≠ .short x := by simpa using same
      rw [nsLookup_nsBind.2 _ x y n ne]
      simp [ne]
  | long mn rest =>
    have ne : (Ident.long mn rest : Ident M N) ≠ .short x := by simp
    rw [nsLookup_nsBind.2 _ x y n ne]
    simp [ne]

/-- Binding does not change the module domain. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDomMod_nsBind"]
theorem nsDomMod_nsBind {M N V : Type} [DecidableEq M]
    (x : N) (y : V) (n : Namespace M N V) :
    nsDomMod (nsBind x y n) = nsDomMod n := by
  funext path
  apply propext
  change (∃ v, nsLookupMod (nsBind x y n) path = some v) ↔
    (∃ v, nsLookupMod n path = some v)
  cases n with | bind vs ms =>
  cases path with
  | nil => simp [nsBind, nsLookupMod]
  | cons mn rest => simp [nsBind, nsLookupMod]

/-- Membership in the value domain is exactly a successful lookup. HOL states the
membership as `x ∈ nsDom n`; the Lean set carrier is the membership predicate. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_nsDom"]
theorem nsLookup_nsDom {M N V : Type} [DecidableEq M] [DecidableEq N]
    (x : Ident M N) (n : Namespace M N V) :
    nsDom n x ↔ ∃ v, nsLookup n x = some v :=
  Iff.rfl

/-- An association-list namespace has only the empty module path in its module domain. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDomMod_alist_to_ns"]
theorem nsDomMod_alistToNs {M N V : Type} [DecidableEq M] (l : Alist N V) :
    nsDomMod (alistToNs l) = ({[]} : Set (List M)) := by
  funext path
  apply propext
  change (∃ v, nsLookupMod (alistToNs l) path = some v) ↔ path = []
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn rest => simp [alistToNs, nsLookupMod]

/-- Flapjack infrastructure: a successful first-match lookup puts the found
pair in the list. -/
private theorem mem_of_lookup {K V : Type} [BEq K] [LawfulBEq K]
    {l : List (K × V)} {k : K} {v : V} (found : l.lookup k = some v) : (k, v) ∈ l := by
  obtain ⟨l₁, l₂, same, _⟩ :=
    (List.lookup_eq_some_iff (l := l) (k := k) (b := v)).mp found
  rw [same]
  simp

/-- Flapjack infrastructure: a listed key has some first-match lookup result. -/
private theorem exists_lookup_of_mem {K V : Type} [BEq K] [LawfulBEq K]
    {l : List (K × V)} {p : K × V} (mem : p ∈ l) : ∃ v, l.lookup p.1 = some v := by
  induction l with
  | nil => cases mem
  | cons q l ih =>
    rw [List.mem_cons] at mem
    rcases mem with same | mem
    · subst same
      refine ⟨p.2, ?_⟩
      rw [List.lookup_cons]
      simp
    · obtain ⟨v, found⟩ := ih mem
      by_cases head : p.1 == q.1
      · exact ⟨q.2, by simp [List.lookup, head]⟩
      · exact ⟨v, by simp [List.lookup, head, found]⟩

/-- Membership in an association-list namespace domain is exactly the short
name of a listed entry. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDom_alist_to_ns"]
theorem nsDom_alistToNs {M N V : Type} [DecidableEq M] [DecidableEq N] (l : Alist N V) :
    nsDom (alistToNs l) =
      Set.image (fun p : N × V => (.short p.1 : Ident M N)) {p | p ∈ l} := by
  funext id
  apply propext
  change (∃ v, nsLookup (alistToNs l) id = some v) ↔
    ∃ p, p ∈ l ∧ (.short p.1 : Ident M N) = id
  constructor
  · rintro ⟨v, found⟩
    obtain ⟨x', same, lookupFound⟩ := (nsLookup_alistToNs_some l id v).mp found
    exact ⟨(x', v), mem_of_lookup lookupFound, same.symm⟩
  · rintro ⟨p, mem, same⟩
    obtain ⟨v, lookupFound⟩ := exists_lookup_of_mem mem
    exact ⟨v, (nsLookup_alistToNs_some l id v).mpr ⟨p.1, same.symm, lookupFound⟩⟩

/-- A namespace whose module domain is only the empty path appends without
adding module paths. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDomMod_nsAppend_flat"]
theorem nsDomMod_nsAppend_flat {M N V : Type} [DecidableEq M]
    (n1 n2 : Namespace M N V) (flat : nsDomMod n1 = ({[]} : Set (List M))) :
    nsDomMod (nsAppend n1 n2) = nsDomMod n2 := by
  funext path
  apply propext
  change (∃ v, nsLookupMod (nsAppend n1 n2) path = some v) ↔
    (∃ v, nsLookupMod n2 path = some v)
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn rest =>
    have n1None : nsLookupMod n1 [mn] = none := by
      cases found : nsLookupMod n1 [mn] with
      | none => rfl
      | some env =>
        have member : nsDomMod n1 [mn] := ⟨env, found⟩
        rw [flat] at member
        change ([mn] : List M) = [] at member
        simp at member
    rw [nsLookupMod_append_cons, n1None]

/-- A namespace whose module domain is only the empty path appends its value
domain without shadowing. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDom_nsAppend_flat"]
theorem nsDom_nsAppend_flat {M N V : Type} [DecidableEq M] [DecidableEq N]
    (n1 n2 : Namespace M N V) (flat : nsDomMod n1 = ({[]} : Set (List M))) :
    nsDom (nsAppend n1 n2) = (nsDom n1 ∪ nsDom n2 : Set (Ident M N)) := by
  funext id
  apply propext
  change (∃ v, nsLookup (nsAppend n1 n2) id = some v) ↔
    ((∃ v, nsLookup n1 id = some v) ∨ ∃ v, nsLookup n2 id = some v)
  constructor
  · rintro ⟨v, found⟩
    rcases (nsLookup_nsAppend_some n1 id n2 v).mp found with first | ⟨_, second, _⟩
    · exact Or.inl ⟨v, first⟩
    · exact Or.inr ⟨v, second⟩
  · rintro (⟨v, found⟩ | ⟨v, found⟩)
    · exact ⟨v, (nsLookup_nsAppend_some n1 id n2 v).mpr (Or.inl found)⟩
    · cases h : nsLookup n1 id with
      | some w => exact ⟨w, (nsLookup_nsAppend_some n1 id n2 w).mpr (Or.inl h)⟩
      | none =>
        refine ⟨v, (nsLookup_nsAppend_some n1 id n2 v).mpr (Or.inr ⟨h, found, ?_⟩)⟩
        intro p1 p2 ne same
        cases modFound : nsLookupMod n1 p1 with
        | none => rfl
        | some env =>
          have member : nsDomMod n1 p1 := ⟨env, modFound⟩
          rw [flat] at member
          exact absurd member ne

end Flapjack.NamespaceHOL
