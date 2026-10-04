import Flapjack.Compiler.Backend.WordToStack.Proofs.ALookupMap
import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeInsertWf
import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeAccessors

namespace Flapjack.WordToStackProofs
open Flapjack Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
attribute [local instance] Classical.propDecidable

/-- Logical HOL inhabitedness for the existing option THE. No NONE default
is introduced; successful read premises discharge all observed value THE uses. -/
local instance wordLocNonempty {width : Nat} [NeZero width] : Nonempty (WordLocW width) :=
  ⟨.word 0⟩

/-- Canonical roundtrip for the actual imported WordSem state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width C F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Flapjack factoring: zipping two maps over one list preserves their shared
source positions. No separate HOL declaration is claimed for this helper. -/
private theorem zipMaps {α β γ : Type} (ls : List α) (f : α → β) (g : α → γ) :
    (ls.map f).zip (ls.map g) = ls.map (fun p => (f p, g p)) := by
  induction ls with
  | nil => rfl
  | cons p ls ih => simp [ih]

/-- Flapjack factoring: propositional numeric key equality agrees with the
existing computable numeric lookup. No HOL declaration is claimed here. -/
theorem numericLookupEq {α : Type} (ls : List (Nat × α)) (q : Nat) :
    holAlookup ls q = keyLookup ls q := by
  classical
  induction ls with
  | nil => rfl
  | cons p ls ih =>
      rcases p with ⟨a,b⟩
      by_cases he : a = q
      · simp [holAlookup, keyLookup, he]
      · simpa [holAlookup, keyLookup, he] using ih

/-- Flapjack factoring of the existing native lookup_alist_insert_any result
and paired map identity; it retains first occurrence and native truncation. -/
private theorem lookupInsertMaps {α β : Type} (ls : List α) (key : α → Nat)
    (value : α → β) (tree : Spt β) (q : Nat) :
    sptLookup q (LoopSemStateFiniteExact.sptAlistInsert (ls.map key) (ls.map value) tree) =
      match keyLookup (ls.map (fun p => (key p, value p))) q with
      | none => sptLookup q tree
      | some v => some v := by
  rw [lookup_alist_insert_any, zipMaps, numericLookupEq]
  rfl

/-- Flapjack factoring: the existing generic identity/mapping ports give a
lookup in a list tabulated by an arbitrary value function, even with duplicates. -/
private theorem tabulatedLookup {α β : Type} (ls : List α) (value : α → β) (q : α) :
    keyLookup (ls.map (fun p => (p, value p))) q =
      if q ∈ ls then some (value q) else none := by
  classical
  have h := alookupMapAny (fun p : α × α => (p.1, value p.1)) id
    (fun p _ => value p) (ls.map (fun p => (p,p))) q q
    (by intro p r _ _ he; exact he)
    (by intro p r hm; obtain ⟨a, _, he⟩ := List.mem_map.mp hm; cases he; rfl) rfl
  simp only [List.map_map, Function.comp_def] at h
  rw [alookupIdTabulate] at h
  by_cases hm : q ∈ ls <;> simpa [hm] using h

/-- Flapjack factoring: a successful first-match association lookup supplies
its actual key/payload member, with no uniqueness premise. -/
private theorem lookupMem {α : Type} (ls : List (Nat × α)) (q : Nat) (v : α)
    (h : keyLookup ls q = some v) : (q,v) ∈ ls := by
  classical
  induction ls with
  | nil => simp [keyLookup, holAlookup] at h
  | cons p ls ih =>
      rcases p with ⟨a,b⟩
      by_cases he : a = q
      · subst a
        simp [keyLookup, holAlookup] at h
        subst b
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih (by simpa [keyLookup, holAlookup, he] using h))

/-- Flapjack factoring: absent first-match lookup means the queried key is
absent from the source key list, with duplicates permitted. -/
private theorem lookupNone {α : Type} (ls : List (Nat × α)) (q : Nat)
    (h : keyLookup ls q = none) : q ∉ ls.map Prod.fst := by
  classical
  induction ls with
  | nil => simp
  | cons p ls ih =>
      rcases p with ⟨a,b⟩
      by_cases he : a = q
      · simp [keyLookup, holAlookup, he] at h
      · have ht : q ∉ ls.map Prod.fst := ih (by simpa [keyLookup, holAlookup, he] using h)
        simpa [Ne.symm he] using ht

/-- Flapjack factoring: THE is injective on the SOME-filtered list plus one
SOME query. The NONE default contributes nothing to this domain. -/
private theorem filteredTheInj (ls : List (Option Nat)) (q : Nat) :
    ∀ p r, (p = some q ∨ p ∈ ls.filter Option.isSome) →
      (r = some q ∨ r ∈ ls.filter Option.isSome) → holThe p = holThe r → p = r := by
  intro p r hp hr he
  have hpSome : p.isSome = true := hp.elim (fun he => he ▸ rfl)
    (fun hm => (List.mem_filter.mp hm).2)
  have hrSome : r.isSome = true := hr.elim (fun he => he ▸ rfl)
    (fun hm => (List.mem_filter.mp hm).2)
  cases p <;> cases r <;> simp_all [holThe]

/-- Full original `alist_insert_get_vars`: equality of whole native local trees
for selected parallel-move writes versus the complete move. All six original
premises are retained, including the two distinctness guards (the observation
proof does not need to strengthen either guard). Missing selected destinations
must be self moves by the original coverage premise; read success proves their
writes preserve the existing value. No desired lookup/post-state is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem alistInsertGetVars {width : Nat} [NeZero width] {C F : Type}
    (moves : List (Nat × Nat)) (s : WordSemStateFiniteExact width C F)
    (x : List (WordLocW width)) (ls : List (Option Nat))
    (_hd : (moves.map Prod.fst).Nodup)
    (hread : WordSemStateFiniteExact.getVars (moves.map Prod.snd) s = some x)
    (_hselected : (ls.filter Option.isSome).Nodup)
    (hw : sptWf s.locals = true)
    (hsubset : ∀ q, some q ∈ ls → q ∈ moves.map Prod.fst)
    (hcover : ∀ q r, (q,r) ∈ moves ∧ q ≠ r → some q ∈ ls) :
    LoopSemStateFiniteExact.sptAlistInsert
      ((ls.filter Option.isSome).map holThe)
      ((ls.filter Option.isSome).map (fun p =>
        holThe (getVar (holThe (keyLookup moves (holThe p))) s))) s.locals =
      LoopSemStateFiniteExact.sptAlistInsert (moves.map Prod.fst) x s.locals := by
  classical
  have hr := NativeWordAccessors.getVarsEq (moves.map Prod.snd) s x hread
  have hx : x = moves.map (fun p => holThe (getVar p.2 s)) := by
    simpa [List.map_map, Function.comp_def, getVar] using hr.2
  rw [hx]
  apply (sptEqThm _ _ ⟨wfAlistInsert _ _ _ hw, wfAlistInsert _ _ _ hw⟩).mpr
  intro q
  let selected := ls.filter Option.isSome
  let g := fun n => holThe (getVar n s)
  have hleft := alookupMapInjFst selected
    (fun p => (holThe p, g (holThe (keyLookup moves (holThe p))))) (some q) q
    (filteredTheInj ls q) rfl
  rw [tabulatedLookup] at hleft
  have hright := alookupMapAny (fun p : Nat × Nat => (p.1, g p.2)) id
    (fun _ => g) moves q q (by intro p r _ _ he; exact he)
    (by intro p r _; rfl) rfl
  rw [lookupInsertMaps, lookupInsertMaps]
  dsimp only [selected, g] at hleft hright
  rw [hleft, hright]
  cases ha : keyLookup moves q with
  | none =>
      have hn : some q ∉ ls := by
        intro hm
        exact lookupNone moves q ha (hsubset q hm)
      simp [hn]
  | some r =>
      have hm := lookupMem moves q r ha
      by_cases hs : some q ∈ ls
      · simp [hs, ha, holThe]
      · have he : q = r := by
          by_cases he : q = r
          · exact he
          · exact False.elim (hs (hcover q r ⟨hm,he⟩))
        subst r
        have hsome : (getVar q s).isSome = true := by
          exact hr.1 _ (List.mem_map.mpr ⟨q, List.mem_map.mpr ⟨(q,q),hm,rfl⟩, rfl⟩)
        cases hv : getVar q s with
        | none => simp [hv] at hsome
        | some v =>
            simp only [getVar] at hv
            simp [hs, holThe, getVar, hv]

end Flapjack.WordToStackProofs
