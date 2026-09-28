import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

/-!
# crep_to_loopProof small generic `[local]` helpers

Counterparts of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`OPT_MMAP_APPEND` (3278), `case_le` (3289), `UNCURRY_eq_case` (3307),
`PAIR_MAP_EQ_UNCURRY` (4314) and `ALOOKUP_EQ_EL` (3847) (bead
`flapjack-pxn.18.5.6.33.10`).  HOL `OPT_MMAP` is `List.mapM` (as for the tagged
`OPT_MMAP_CONG`), `OPTION_BIND` is `Option.bind`, `UNCURRY` is
`Function.uncurry`, `##` is `Prod.map`, `ALOOKUP` is `holAlookup`, and `EL n xs`
under the premise `n < LENGTH xs` is the bounds-checked `xs[n]`.  All free
variables of these `[local]` theorems are universally quantified.
-/

namespace Flapjack

/-- Exact HOL `OPT_MMAP_APPEND` (`crep_to_loopProofScript.sml:3278-3280`, `[local]`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "OPT_MMAP_APPEND"]
theorem OPT_MMAP_APPEND {α β : Type} (f : α → Option β) (xs ys : List α) :
    (xs ++ ys).mapM f =
      (xs.mapM f).bind (fun xsv => (ys.mapM f).bind (fun ysv => some (xsv ++ ysv))) := by
  induction xs with
  | nil => cases hys : ys.mapM f <;> simp [hys]
  | cons x xs ih =>
      simp only [List.cons_append, List.mapM_cons, ih]
      cases f x <;> cases xs.mapM f <;> cases ys.mapM f <;> simp

/-- Exact HOL `case_le` (`crep_to_loopProofScript.sml:3289-3290`, `[local]`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "case_le"]
theorem case_le {α : Type} (dest : Option α) :
    (match dest with | none => 1 | some _ => 0) ≤ (1 : Nat) := by
  cases dest <;> simp

/-- Exact HOL `UNCURRY_eq_case` (`crep_to_loopProofScript.sml:3307-3308`, `[local]`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "UNCURRY_eq_case"]
theorem UNCURRY_eq_case {α β γ : Type} (f : α → β → γ) (x : α × β) :
    Function.uncurry f x = (match x with | (a, b) => f a b) := by
  cases x; rfl

/-- Exact HOL `PAIR_MAP_EQ_UNCURRY` (`crep_to_loopProofScript.sml:4314-4315`, `[local]`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "PAIR_MAP_EQ_UNCURRY"]
theorem PAIR_MAP_EQ_UNCURRY {α β γ δ : Type} (f : α → γ) (g : β → δ) :
    Prod.map f g = (fun p => match p with | (x, y) => (f x, g y)) := by
  funext p; cases p; rfl

/-- Exact HOL `ALOOKUP_EQ_EL` (`crep_to_loopProofScript.sml:3847-3852`, `[local]`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ALOOKUP_EQ_EL"]
theorem ALOOKUP_EQ_EL {α β : Type} [DecidableEq α] (n : Nat) (xs : List (α × β)) (nm : α)
    (y : β) :
    ∀ (hn : n < xs.length), (xs[n]'hn).1 = nm → (xs.map Prod.fst).Nodup →
      y = (xs[n]'hn).2 → holAlookup xs nm = some y := by
  induction xs generalizing n with
  | nil => intro hn; simp at hn
  | cons p ps ih =>
    intro hn h1 hd h2
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hd
    cases n with
    | zero =>
      simp only [List.getElem_cons_zero] at h1 h2
      subst h1 h2; simp [holAlookup]
    | succ n =>
      simp only [List.getElem_cons_succ] at h1 h2
      have hne : a ≠ nm := by
        intro hanm
        apply hd.1
        rw [hanm, ← h1]
        exact List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩
      simp only [holAlookup, if_neg hne]
      exact ih n (by simpa using hn) h1 hd.2 h2

end Flapjack
