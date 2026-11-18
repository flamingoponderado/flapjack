module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# Shared script-level lemmas of `word_allocProofScript.sml`

Counterpart of the `[local]` list and product lemmas that
`cakeml/compiler/backend/proofs/word_allocProofScript.sml` shares between its
allocation and SSA sections (`:51-54`, `:815-818`, `:830-833`, `:853-860`,
`:6212-6255`). HOL's `LET`/`$!`/`S` combinators, `LASTN`, `pair_CASE`/`##`,
`EL` and `ALOOKUP` are the reviewed `Prod.casesOn`/`Prod.map`,
`wordSemLastN`, `holEl` and `holAlookup` renderings.
-/

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Exact HOL `LET_FORALL_ELIM'` (`word_allocProofScript.sml:51-54`):
    `LET f v ⇔ $! (S ($==> ∘ $= v) f)`, i.e. the `let` of `v` satisfies `f`
    exactly when every value equal to `v` does. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "LET_FORALL_ELIM'"]
theorem letForallElim {α : Type} (f : α → Prop) (v : α) :
    f v ↔ ∀ x, x = v → f x := by
  constructor
  · intro hf x hx
    rw [hx]
    exact hf
  · intro h
    exact h v rfl

/-- Exact HOL `LASTN_LENGTH2` (`word_allocProofScript.sml:815-818`): taking
    the last `LENGTH xs + 1` elements of `x :: xs` keeps the whole list. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "LASTN_LENGTH2"]
theorem lastNLength2 {α : Type} (xs : List α) (x : α) :
    wordSemLastN (xs.length + 1) (x :: xs) = x :: xs := by
  unfold wordSemLastN
  have hlen : (x :: xs).reverse.length ≤ xs.length + 1 := by
    simp
  rw [List.take_of_length_le hlen]
  simp

/-- Exact HOL `PAIR_CASE_PAIR_MAP` (`word_allocProofScript.sml:830-833`): the
    product map followed by `pair_CASE` applies both functions to the pair. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "PAIR_CASE_PAIR_MAP"]
theorem pairCasePairMap {α β γ δ ε : Type} (f : δ → β) (g : ε → γ) (e : δ × ε)
    (h : β → γ → α) :
    Prod.casesOn (motive := fun _ => α) (Prod.map f g e) h =
      Prod.casesOn (motive := fun _ => α) e (fun x y => h (f x) (g y)) := by
  cases e
  rfl

/-- Exact HOL `MEM_ZIP_weak` (`word_allocProofScript.sml:853-860`): a pair
    member of a zipped list has both components in the respective lists. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "MEM_ZIP_weak"]
theorem memZipWeak {α β : Type} (l1 : List α) (l2 : List β) (x1 : α) (x2 : β)
    (h : l1.length = l2.length ∧ (x1, x2) ∈ l1.zip l2) :
    x1 ∈ l1 ∧ x2 ∈ l2 :=
  List.of_mem_zip h.2

/-- Exact HOL `PAIR_ZIP_MEM` (`word_allocProofScript.sml:6212-6219`), the
    script's second copy of the zipped-pair membership fact. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "PAIR_ZIP_MEM"]
theorem pairZipMem {α β : Type} (c : List α) (d : List β) (a : α) (b : β)
    (h : c.length = d.length ∧ (a, b) ∈ c.zip d) :
    a ∈ c ∧ b ∈ d :=
  List.of_mem_zip h.2

/-- Every association list entry returned by `holAlookup` is a member of the
    list. Flapjack infrastructure for `ALOOKUP_ZIP_MEM`; it has no separate
    HOL original (HOL uses `ALOOKUP_MEM`). -/
private theorem mem_of_holAlookup {α β : Type} [DecidableEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), holAlookup l k = some v → (k, v) ∈ l
  | [], _, _, h => by simp [holAlookup] at h
  | (x, y) :: t, k, v, h => by
      simp only [holAlookup] at h
      split at h
      · rename_i hxy
        have hv : y = v := by injection h
        subst hv
        rw [← hxy]
        exact List.mem_cons_self
      · rename_i hxy
        exact List.mem_cons_of_mem _ (mem_of_holAlookup t k v h)

/-- Exact HOL `ALOOKUP_ZIP_MEM` (`word_allocProofScript.sml:6222-6230`): a
    successful lookup in a zipped association list yields members of both
    lists. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ALOOKUP_ZIP_MEM"]
theorem alookupZipMem {α β : Type} [DecidableEq α] (a : List α) (b : List β)
    (x : α) (y : β)
    (h : a.length = b.length ∧ holAlookup (a.zip b) x = some y) :
    x ∈ a ∧ y ∈ b :=
  List.of_mem_zip (mem_of_holAlookup (α := α) (β := β) (a.zip b) x y h.2)

/-- Exact HOL `ALOOKUP_ALL_DISTINCT_REMAP`
    (`word_allocProofScript.sml:6232-6255`): under a distinct mapping of the
    keys, a lookup at the image of the original key returns the same value.
    HOL's `EL` is the reviewed `holEl`, whose out-of-bounds value needs an
    inhabited key type. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ALOOKUP_ALL_DISTINCT_REMAP"
  (total_function_inhabitants := [α])]
theorem alookupAllDistinctRemap {α β γ : Type} [Nonempty α] [DecidableEq α]
    [DecidableEq γ] (ls : List α) (x : List β) (f : α → γ) (y : β) (n : Nat)
    (h : ls.length = x.length ∧ (ls.map f).Nodup ∧ n < ls.length ∧
      holAlookup (ls.zip x) (holEl n ls) = some y) :
    holAlookup ((ls.map f).zip x) (f (holEl n ls)) = some y := by
  induction ls generalizing x n with
  | nil => simp at h
  | cons a as ih =>
      cases x with
      | nil => simp at h
      | cons b bs =>
          have hn : f a ∉ as.map f ∧ (as.map f).Nodup := by
            simpa using h.2.1
          have hl : as.length = bs.length := by simpa using h.1
          cases n with
          | zero =>
              have hlook0 : holAlookup ((a :: as).zip (b :: bs)) a = some y :=
                h.2.2.2
              have hb : b = y := by
                simpa [holAlookup] using hlook0
              subst hb
              have hgoal :
                  holAlookup ((List.map f (a :: as)).zip (b :: bs)) (f a) = some b := by
                simp [holAlookup]
              exact hgoal
          | succ k =>
              have hk : k < as.length := by simpa using h.2.2.1
              have hmem : holEl k as ∈ as := by
                rw [holEl_eq_getElem k as hk]
                exact List.getElem_mem hk
              have hne : a ≠ holEl k as := by
                intro he
                exact hn.1 (he ▸ List.mem_map.mpr ⟨holEl k as, hmem, rfl⟩)
              have hfe : f a ≠ f (holEl k as) := by
                intro he
                exact hn.1 (he ▸ List.mem_map.mpr ⟨holEl k as, hmem, rfl⟩)
              have hlook : holAlookup ((a :: as).zip (b :: bs)) (holEl k as) = some y :=
                h.2.2.2
              simp only [List.zip_cons_cons, holAlookup, if_neg hne] at hlook
              have ihk := ih bs k ⟨hl, hn.2, hk, hlook⟩
              have hgoal :
                  holAlookup ((List.map f as).zip bs) (f (holEl k as)) = some y := ihk
              have hstep :
                  holAlookup ((List.map f (a :: as)).zip (b :: bs)) (f (holEl k as)) =
                    some y := by
                simp only [List.map_cons, List.zip_cons_cons, holAlookup, if_neg hfe]
                exact hgoal
              exact hstep

end Flapjack.Compiler.Backend.WordAlloc
