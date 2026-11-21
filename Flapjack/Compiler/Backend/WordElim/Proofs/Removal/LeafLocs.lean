module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Removal.Frame
public import Flapjack.Misc.SptreeLookup

@[expose] public section

/-!
# `word_removal_lemma`: locations after a leaf statement

Flapjack infrastructure for the leaf cases of `word_removal_lemma`
(`word_elimProofScript.sml:988-1290`): a leaf statement that does not fail
adds no location to the state, and the locations of its result are locations of
the initial state.  HOL proves these facts per case with `domain_get_locals_lookup`,
`get_locals_insert`, `get_store_update`, `get_memory_update`,
`const_writes_eq_Loc` and `get_memory_write_bytearray_lemma`.
-/

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack Flapjack.WordSemStateFiniteExact

section LeafLocs
variable {width : Nat} [NeZero width] {C F : Type}

/-- All locations of `s` satisfy `R`. Flapjack infrastructure. -/
def LocsIn (R : Nat → Prop) (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ n, sptMem n (findLocState s) → R n

theorem locsIn_self (s : WordSemStateFiniteExact width C F) :
    LocsIn (fun n => sptMem n (findLocState s)) s := fun _ h => h

theorem LocsWithin.locsIn {R : Nat → Prop} {s1 s : WordSemStateFiniteExact width C F}
    (h1 : LocsWithin s1 s) (h : LocsIn R s) : LocsIn R s1 := fun n hn => h n (h1 n hn)

theorem locsIn_setVar {R : Nat → Prop} (s : WordSemStateFiniteExact width C F) (k : Nat)
    (v : WordLocW width) (hs : LocsIn R s) (hv : ∀ n o, v = .loc n o → R n) :
    LocsIn R (s.setVar k v) := by
  intro n hn
  rw [sptMem_findLocState] at hn
  rcases hn with hl | hrest
  · rcases getLocals_insert k v s.locals hl with hl' | hl'
    · exact hs n ((sptMem_findLocState s n).mpr (Or.inl hl'))
    · cases v with
      | word w => simp at hl'
      | loc b o =>
        simp only [destWordLoc_loc, Set.mem_singleton_iff] at hl'
        subst hl'
        exact hv _ o rfl
  · exact hs n ((sptMem_findLocState s n).mpr (Or.inr hrest))

theorem locsIn_setVars {R : Nat → Prop} :
    ∀ (ks : List Nat) (vs : List (WordLocW width)) (s : WordSemStateFiniteExact width C F),
      LocsIn R s → (∀ v ∈ vs, ∀ n o, v = .loc n o → R n) → LocsIn R (s.setVars ks vs)
  | [], _, s, hs, _ => by simpa [setVars, LoopSemStateFiniteExact.sptAlistInsert] using hs
  | _ :: _, [], s, hs, _ => by simpa [setVars, LoopSemStateFiniteExact.sptAlistInsert] using hs
  | k :: ks, v :: vs, s, hs, hv => by
    have ih := locsIn_setVars ks vs s hs (fun w hw => hv w (List.mem_cons_of_mem _ hw))
    have := locsIn_setVar (s.setVars ks vs) k v ih (hv v List.mem_cons_self)
    simpa [setVars, setVar, LoopSemStateFiniteExact.sptAlistInsert] using this

theorem locsWithin_unsetVar (s : WordSemStateFiniteExact width C F) (k : Nat) :
    LocsWithin (s.unsetVar k) s := by
  intro n hn
  rw [sptMem_findLocState] at hn ⊢
  rcases hn with h | h
  · left
    obtain ⟨key, o, hk⟩ := (domainGetLocalsLookup n _).mp h
    simp only [unsetVar, sptLookup_sptDelete] at hk
    split at hk
    · cases hk
    · exact (domainGetLocalsLookup n _).mpr ⟨key, o, hk⟩
  · exact Or.inr h

theorem locOf_getVar (s : WordSemStateFiniteExact width C F) (x : Nat) {v : WordLocW width}
    (h : s.getVar x = some v) : LocOf s v :=
  wordExp_locOf s (.var x) (by simpa [wordExp] using h)

theorem locOf_getVars (s : WordSemStateFiniteExact width C F) (xs : List Nat)
    {vs : List (WordLocW width)} (h : WordSemStateFiniteExact.getVars xs s = some vs) :
    ∀ v ∈ vs, LocOf s v := by
  rintro v hv n o rfl
  exact (sptMem_findLocState s n).mpr (Or.inl (getVars_get_locals xs s vs n o ⟨h, hv⟩))

theorem locsWithin_setStore (s : WordSemStateFiniteExact width C F) (k : WordStoreHOL)
    (v : WordLocW width) (hv : LocOf s v) : LocsWithin (setStore k v s) s := by
  intro n hn
  rw [sptMem_findLocState] at hn
  rcases hn with h | h | h | h
  · exact (sptMem_findLocState s n).mpr (Or.inl h)
  · rcases get_store_update s.store k v h with h' | h'
    · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inl h'))
    · cases v with
      | word w => simp at h'
      | loc b o =>
        simp only [destWordLoc_loc, Set.mem_singleton_iff] at h'
        subst h'
        exact hv _ o rfl
  · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inr (Or.inl h)))
  · exact (sptMem_findLocState s n).mpr (Or.inr (Or.inr (Or.inr h)))

theorem locsWithin_constWrites (s : WordSemStateFiniteExact width C F) (a off : BitVec width)
    (words : List (Bool × BitVec width)) :
    LocsWithin { s with memory := wordSemConstWrites a off words s.memory } s := by
  intro n hn
  rw [sptMem_findLocState] at hn ⊢
  rcases hn with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    obtain ⟨k, n1, hd, hk⟩ := (domain_get_memory _ _ n).mp h
    exact (domain_get_memory _ _ n).mpr ⟨k, n1, hd, wordSemConstWrites_eq_Loc _ _ _ _ k _ _ hk⟩

theorem locsWithin_writeBytearray (s : WordSemStateFiniteExact width C F) (c : BitVec width)
    (r : List (BitVec 8)) :
    LocsWithin { s with memory := writeBytearrayExact c r s.memory s.mdomain s.be } s := by
  intro n hn
  rw [sptMem_findLocState] at hn ⊢
  rcases hn with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (get_memory_write_bytearray_lemma s.memory s.mdomain
      (getMemory s.memory s.mdomain) c r s.be (fun _ h => h) h)))

theorem locsWithin_cutEnv_locals (s : WordSemStateFiniteExact width C F)
    (names : WordLangCutsetsHOL) {env : Spt (WordLocW width)}
    (h : wordSemCutEnv names s.locals = some env) :
    ∀ n, sptMem n (getLocals env) → sptMem n (getLocals s.locals) := by
  unfold wordSemCutEnv wordSemCutEnvs wordSemCutNames at h
  by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive names.1 s.locals <;>
    by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive names.2 s.locals <;>
    simp only [h1, h2, if_true, if_false, Option.some.injEq, reduceCtorEq] at h
  subst h
  intro n hn
  rcases (sptMem_sptUnion _ _ n).mp (getLocals_union_subset _ _ hn) with h | h
  · exact getLocals_inter_subset _ _ h
  · exact getLocals_inter_subset _ _ h

end LeafLocs

end Flapjack.Compiler.Backend.WordElim
