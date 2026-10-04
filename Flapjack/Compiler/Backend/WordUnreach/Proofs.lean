import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock
import Flapjack.Misc.Option

/-!
# word_unreachProof: correctness of `remove_unreach`

Ports of `cakeml/compiler/backend/proofs/word_unreachProofScript.sml`: list and `num_map`
facts about `merge_moves` and the local `copy_vars`, the semantic equations for `Skip`,
`Seq` and `Move`, and the preservation of non-`Error` results by `SimpSeq`,
`Seq_assoc_right` and `remove_unreach`. HOL `ALOOKUP` is the untagged library rendering
`sptAListLookup`, `THE` the tagged `holThe`, `EVERY` bounded membership, `ALL_DISTINCT`
`List.Nodup`, `FILTER` `List.filter`, and `lookup`/`insert` the `Spt` operations.
-/

namespace Flapjack.Compiler.Backend.WordUnreach

open Flapjack

/-- Exact HOL `copy_vars_def` (`word_unreachProofScript.sml:40-44`), a definition local to
the proof script; HOL `THE` is the tagged `holThe`. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "copy_vars_def"]
noncomputable def copyVars {α : Type} [Nonempty α] :
    List (Nat × Nat) → Spt α → Spt α → Spt α
  | [], _, to => to
  | (l, r) :: rest, src, to => sptInsert l (holThe (sptLookup r src)) (copyVars rest src to)

/-- Exact HOL `copy_vars_append` (`word_unreachProofScript.sml:46-52`). -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "copy_vars_append"]
theorem copyVarsAppend {α : Type} [Nonempty α] :
    ∀ (xs ys : List (Nat × Nat)) (src to : Spt α),
      copyVars (xs ++ ys) src to = copyVars xs src (copyVars ys src to)
  | [], _, _, _ => rfl
  | (l, r) :: xs, ys, src, to => by
      simp only [List.cons_append, copyVars, copyVarsAppend xs ys src to]

/-- Exact HOL `ALL_DISTINCT_merge_moves` (`word_unreachProofScript.sml:33-38`); `l1` and
`l2` are free in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "ALL_DISTINCT_merge_moves"]
theorem allDistinctMergeMoves (l1 l2 : List (Nat × Nat)) :
    ((mergeMoves l1 l2).map Prod.fst).Nodup := by
  have h := anubAllDistinctKeys (l2.map (fun (x, y) =>
    match sptAListLookup y l1 with
    | none => (x, y)
    | some v => (x, v)) ++ l1) ([] : List Nat) List.nodup_nil
  rw [List.append_nil] at h
  exact h

/-- Exact HOL `copy_vars_MEM_acc` (`word_unreachProofScript.sml:78-99`); `s` and `t` are
free in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "copy_vars_MEM_acc"]
theorem copyVarsMemAcc {α : Type} [Nonempty α] (s t : Spt α) :
    ∀ (xs : List (Nat × Nat)) (acc : List Nat) (n : Nat) (w : α),
      n ∈ acc →
      sptInsert n w (copyVars (anub xs acc) s t) =
        sptInsert n w (copyVars (anub xs (acc.filter fun x => decide (n ≠ x))) s t)
  | [], acc, n, w, _ => by simp [anub, copyVars]
  | (k, v) :: xs, acc, n, w, hn => by
      by_cases hnk : n = k
      · subst hnk
        have hf : ¬ n ∈ acc.filter (fun x => decide (n ≠ x)) := by simp
        simp only [anub, if_pos hn, if_neg hf, copyVars, sptInsert_insert_shadow]
        have e : (n :: acc.filter fun x => decide (n ≠ x)).filter (fun x => decide (n ≠ x)) =
            acc.filter fun x => decide (n ≠ x) := by
          simp [List.filter_filter]
        have h1 := copyVarsMemAcc s t xs acc n w hn
        have h2 := copyVarsMemAcc s t xs (n :: acc.filter fun x => decide (n ≠ x)) n w
          List.mem_cons_self
        rw [e] at h2
        rw [h1, h2]
      · by_cases hk : k ∈ acc
        · have hkf : k ∈ acc.filter (fun x => decide (n ≠ x)) := by
            simp [List.mem_filter, hk, hnk]
          simp only [anub, if_pos hk, if_pos hkf]
          exact copyVarsMemAcc s t xs acc n w hn
        · have hkf : ¬ k ∈ acc.filter (fun x => decide (n ≠ x)) := by
            simp [List.mem_filter, hk]
          simp only [anub, if_neg hk, if_neg hkf, copyVars]
          rw [sptInsert_swap n k _ _ _ hnk, sptInsert_swap n k _ _ _ hnk]
          congr 1
          rw [copyVarsMemAcc s t xs (k :: acc) n w (List.mem_cons_of_mem _ hn)]
          have e : (k :: acc).filter (fun x => decide (n ≠ x)) =
              k :: acc.filter (fun x => decide (n ≠ x)) := by
            simp [hnk]
          rw [e]

/-- Exact HOL `copy_vars_anub` (`word_unreachProofScript.sml:101-106`); `xs` is free in
HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "copy_vars_anub"]
theorem copyVarsAnub {α : Type} [Nonempty α] (xs : List (Nat × Nat)) :
    (copyVars (anub xs []) : Spt α → Spt α → Spt α) = copyVars xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      obtain ⟨k, v⟩ := p
      funext s t
      simp only [anub, List.not_mem_nil, if_false, copyVars]
      rw [copyVarsMemAcc s t xs [k] k _ List.mem_cons_self]
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, List.filter_nil]
      rw [ih]

/-- Exact HOL `lookup_copy_vars_ignore` (`word_unreachProofScript.sml:108-116`). -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "lookup_copy_vars_ignore"]
theorem lookupCopyVarsIgnore {α : Type} [Nonempty α] :
    ∀ (l1 : List (Nat × Nat)) (h1 : Nat) (x y : Spt α),
      sptAListLookup h1 l1 = none → sptLookup h1 (copyVars l1 x y) = sptLookup h1 y
  | [], _, _, _, _ => rfl
  | (l, r) :: l1, h1, x, y, h => by
      simp only [sptAListLookup] at h
      by_cases hl : h1 = l
      · rw [if_pos hl] at h; cases h
      · rw [if_neg hl] at h
        simp only [copyVars]
        rw [sptLookup_sptInsert_ne _ _ _ _ hl]
        exact lookupCopyVarsIgnore l1 h1 x y h

/-- Exact HOL `lookup_copy_vars` (`word_unreachProofScript.sml:118-128`). -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "lookup_copy_vars"]
theorem lookupCopyVars {α : Type} [Nonempty α] :
    ∀ (l1 : List (Nat × Nat)) (h1 y : Nat) (s t : Spt α) (z : α),
      sptAListLookup h1 l1 = some y ∧ sptLookup h1 (copyVars l1 s t) = some z →
      holThe (sptLookup y s) = z
  | [], _, _, _, _, _, ⟨h, _⟩ => by cases h
  | (l, r) :: l1, h1, y, s, t, z, ⟨h, hz⟩ => by
      simp only [sptAListLookup] at h
      simp only [copyVars] at hz
      by_cases hl : h1 = l
      · subst hl
        rw [if_pos rfl] at h
        cases h
        rw [sptLookup_sptInsert_same] at hz
        exact Option.some.inj hz
      · rw [if_neg hl] at h
        rw [sptLookup_sptInsert_ne _ _ _ _ hl] at hz
        exact lookupCopyVars l1 h1 y s t z ⟨h, hz⟩

/-- Exact HOL `IMP_EVERY_MAP_SND_anub` (`word_unreachProofScript.sml:142-148`). -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "IMP_EVERY_MAP_SND_anub"]
theorem impEveryMapSndAnub {α β : Type} [DecidableEq α] :
    ∀ (xs : List (α × β)) (acc : List α) (p : β → Prop),
      (∀ x ∈ xs.map Prod.snd, p x) → ∀ x ∈ (anub xs acc).map Prod.snd, p x
  | [], _, _, _ => by simp [anub]
  | (k, v) :: xs, acc, p, h => by
      have hv : p v := h v (by simp)
      have hxs : ∀ x ∈ xs.map Prod.snd, p x := fun x hx => h x (by simp at hx ⊢; exact Or.inr hx)
      unfold anub
      by_cases hk : k ∈ acc
      · rw [if_pos hk]; exact impEveryMapSndAnub xs acc p hxs
      · rw [if_neg hk]
        intro x hx
        simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hv
        · exact impEveryMapSndAnub xs (k :: acc) p hxs x hx

/-! ### Semantic equations -/

namespace WordUnreachProofWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordUnreachProofWitnesses

section Semantics

open WordSemStateFiniteExact

variable {width : Nat} [NeZero width] {C F : Type}

private instance wordLocWNonemptyUnreach : Nonempty (WordLocW width) := ⟨.word 0⟩

private theorem evSkip (s : WordSemStateFiniteExact width C F) : evaluate .skip s = (none, s) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).1 s

private theorem evMove (s : WordSemStateFiniteExact width C F) (pri : Nat)
    (moves : List (Nat × Nat)) :
    evaluate (.move pri moves) s =
      (if (moves.map Prod.fst).Nodup then
        match WordSemStateFiniteExact.getVars (moves.map Prod.snd) s with
        | none => (some .error, s)
        | some vs => (none, WordSemStateFiniteExact.setVars (moves.map Prod.fst) vs s)
      else (some .error, s)) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.1 s pri moves

/-- `Seq` evaluates its first part and continues only on `NONE` (Flapjack infrastructure,
from `evaluate_def` and `fix_clock_evaluate`). -/
private theorem evSeq (s : WordSemStateFiniteExact width C F) (c1 c2 : WordLangProgHOL (BitVec width)) :
    evaluate (.seq c1 c2) s =
      match evaluate c1 s with
      | (none, s1) => evaluate c2 s1
      | r => r := by
  rw [(evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1 s c2 c1]
  rcases evaluate c1 s with ⟨r, t⟩
  cases r <;> rfl

/-- Exact HOL `evaluate_Skip_Seq` (`word_unreachProofScript.sml:14-18`); `p` and `s` are free
in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Skip_Seq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateSkipSeq {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) : evaluate (.seq .skip p) s = evaluate p s := by
  rw [evSeq, evSkip]

/-- Exact HOL `evaluate_Seq_Skip` (`word_unreachProofScript.sml:20-25`). -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Seq_Skip"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateSeqSkip {width : Nat} [NeZero width] {C F : Type} :
    ∀ (p1 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      evaluate (.seq p1 .skip) s = evaluate p1 s := by
  intro p1 s
  rw [evSeq]
  rcases evaluate p1 s with ⟨r, t⟩
  cases r
  · exact evSkip t
  · rfl

/-- Exact HOL `evaluate_Seq_assoc` (`word_unreachProofScript.sml:27-31`); `p1`, `p2`, `p3`
and `s` are free in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Seq_assoc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateSeqAssoc {width : Nat} [NeZero width] {C F : Type}
    (p1 p2 p3 : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.seq p1 (.seq p2 p3)) s = evaluate (.seq (.seq p1 p2) p3) s := by
  rw [evSeq, evSeq s (.seq p1 p2) p3, evSeq s p1 p2]
  rcases evaluate p1 s with ⟨r1, t1⟩
  cases r1 with
  | none =>
      simp only
      rw [evSeq]
  | some r => rfl

private theorem alistInsert_copyVars (s : WordSemStateFiniteExact width C F) :
    ∀ (moves : List (Nat × Nat)) (x : List (WordLocW width)) (t : Spt (WordLocW width)),
      WordSemStateFiniteExact.getVars (moves.map Prod.snd) s = some x →
      LoopSemStateFiniteExact.sptAlistInsert (moves.map Prod.fst) x t =
        copyVars moves s.locals t
  | [], x, t, h => by
      simp only [List.map_nil, WordSemStateFiniteExact.getVars, Option.some.injEq] at h
      subst h; rfl
  | (l, r) :: moves, x, t, h => by
      simp only [List.map_cons, WordSemStateFiniteExact.getVars] at h
      cases hv : WordSemStateFiniteExact.getVar r s with
      | none => rw [hv] at h; cases h
      | some w =>
          rw [hv] at h
          cases hvs : WordSemStateFiniteExact.getVars (moves.map Prod.snd) s with
          | none => rw [hvs] at h; cases h
          | some ws =>
              rw [hvs] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [List.map_cons, LoopSemStateFiniteExact.sptAlistInsert, copyVars]
              rw [alistInsert_copyVars s moves ws t hvs]
              simp only [WordSemStateFiniteExact.getVar] at hv
              rw [hv]; rfl

/-- Exact HOL `evaluate_Move` (`word_unreachProofScript.sml:54-76`); `pri`, `moves` and `s` are
free in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Move"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateMove {width : Nat} [NeZero width] {C F : Type}
    (pri : Nat) (moves : List (Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.move pri moves) s =
      (if (moves.map Prod.fst).Nodup then
        match WordSemStateFiniteExact.getVars (moves.map Prod.snd) s with
        | none => (some .error, s)
        | some _ => (none, { s with locals := copyVars moves s.locals s.locals })
      else (some .error, s)) := by
  rw [evMove]
  split
  · cases hv : WordSemStateFiniteExact.getVars (moves.map Prod.snd) s with
    | none => rfl
    | some l =>
        simp only [WordSemStateFiniteExact.setVars]
        rw [alistInsert_copyVars s moves l s.locals hv]
  · rfl

/-- Exact HOL `get_vars_IS_SOME_lookup` (`word_unreachProofScript.sml:130-140`). -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "get_vars_IS_SOME_lookup"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarsIsSomeLookup {width : Nat} [NeZero width] {C F : Type} :
    ∀ (xs : List Nat) (s : WordSemStateFiniteExact width C F),
      (∃ ws, WordSemStateFiniteExact.getVars xs s = some ws) ↔ ∀ x ∈ xs, (sptLookup x s.locals).isSome = true
  | [], s => by simp [WordSemStateFiniteExact.getVars]
  | x :: xs, s => by
      have ih := getVarsIsSomeLookup xs s
      simp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, List.mem_cons, forall_eq_or_imp]
      cases hx : sptLookup x s.locals with
      | none => simp
      | some w =>
          simp only [Option.isSome_some, true_and]
          rw [← ih]
          cases WordSemStateFiniteExact.getVars xs s <;> simp

/-- One move of `merge_moves`'s rewriting map (Flapjack infrastructure). -/
private def mmStep (l1 : List (Nat × Nat)) (p : Nat × Nat) : Nat × Nat :=
  match sptAListLookup p.2 l1 with
  | none => p
  | some v => (p.1, v)

private theorem mergeMoves_eq (l1 l2 : List (Nat × Nat)) :
    mergeMoves l1 l2 = anub (l2.map (mmStep l1) ++ l1) [] := by
  unfold mergeMoves mmStep
  congr 2

private theorem alookup_mem : ∀ (l : List (Nat × Nat)) (k v : Nat),
    sptAListLookup k l = some v → v ∈ l.map Prod.snd
  | [], _, _, h => by cases h
  | (a, b) :: l, k, v, h => by
      simp only [sptAListLookup] at h
      by_cases hk : k = a
      · rw [if_pos hk] at h; cases h; simp
      · rw [if_neg hk] at h
        exact List.mem_cons_of_mem _ (alookup_mem l k v h)

private theorem copyVars_step {V : Type} [Nonempty V] (src : Spt V) (l1 : List (Nat × Nat)) :
    ∀ (l2 : List (Nat × Nat)) (to : Spt V),
      (∀ y ∈ l2.map Prod.snd, (sptLookup y (copyVars l1 src src)).isSome = true) →
      copyVars (l2.map (mmStep l1)) src to = copyVars l2 (copyVars l1 src src) to
  | [], _, _ => rfl
  | (x, y) :: l2, to, h => by
      have hy := h y (by simp)
      have hrest : ∀ y ∈ l2.map Prod.snd, (sptLookup y (copyVars l1 src src)).isSome = true :=
        fun y hy => h y (by simp at hy ⊢; exact Or.inr hy)
      simp only [List.map_cons, copyVars, copyVars_step src l1 l2 to hrest, mmStep]
      cases hl : sptAListLookup y l1 with
      | none =>
          simp only
          rw [lookupCopyVarsIgnore l1 y src src hl]
      | some v =>
          simp only
          obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hy
          rw [lookupCopyVars l1 y v src src z ⟨hl, hz⟩, hz]
          rfl

/-- Exact HOL `merge_moves_Skip` (`word_unreachProofScript.sml:150-199`); `n1`, `n2` and `m`
are free in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "merge_moves_Skip"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem mergeMovesSkip {width : Nat} [NeZero width] {C F : Type}
    (n1 n2 m : Nat) :
    ∀ (l1 l2 : List (Nat × Nat)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F),
      evaluate (.seq (.move n1 l1) (.move n2 l2)) s = (res, s1) ∧ res ≠ some .error →
      evaluate (.move m (mergeMoves l1 l2)) s = (res, s1) := by
  intro l1 l2 s res s1 ⟨h, hne⟩
  rw [evSeq, evaluateMove] at h
  by_cases hd1 : (l1.map Prod.fst).Nodup
  case neg => rw [if_neg hd1] at h; simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hne
  rw [if_pos hd1] at h
  cases hg1 : WordSemStateFiniteExact.getVars (l1.map Prod.snd) s with
  | none => rw [hg1] at h; simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hne
  | some x1 =>
  rw [hg1] at h
  simp only at h
  rw [evaluateMove] at h
  by_cases hd2 : (l2.map Prod.fst).Nodup
  case neg => rw [if_neg hd2] at h; simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hne
  rw [if_pos hd2] at h
  cases hg2 : WordSemStateFiniteExact.getVars (l2.map Prod.snd)
      { s with locals := copyVars l1 s.locals s.locals } with
  | none => rw [hg2] at h; simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hne
  | some x2 =>
  rw [hg2] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hs1 := (getVarsIsSomeLookup _ s).mp ⟨x1, hg1⟩
  have hs2 := (getVarsIsSomeLookup _ _).mp ⟨x2, hg2⟩
  have hsm : ∀ x ∈ (mergeMoves l1 l2).map Prod.snd, (sptLookup x s.locals).isSome = true := by
    rw [mergeMoves_eq]
    refine impEveryMapSndAnub _ _ _ (fun x hx => ?_)
    rw [List.map_append, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.map_map] at hx
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hx
      simp only [Function.comp, mmStep]
      cases hl : sptAListLookup b l1 with
      | none =>
          have := hs2 b (List.mem_map.mpr ⟨(a, b), hab, rfl⟩)
          simp only at this
          rwa [lookupCopyVarsIgnore l1 b s.locals s.locals hl] at this
      | some v => exact hs1 v (alookup_mem l1 b v hl)
    · exact hs1 x hx
  obtain ⟨ws, hws⟩ := (getVarsIsSomeLookup _ s).mpr hsm
  rw [evaluateMove, if_pos (allDistinctMergeMoves l1 l2), hws]
  simp only [Prod.mk.injEq, true_and]
  rw [mergeMoves_eq, copyVarsAnub, copyVarsAppend,
    copyVars_step s.locals l1 l2 _ (fun y hy => hs2 y hy)]

/-- Exact HOL `merge_moves_thm` (`word_unreachProofScript.sml:201-216`); `n1`, `n2` and `m`
are free in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "merge_moves_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem mergeMovesThm {width : Nat} [NeZero width] {C F : Type}
    (n1 n2 m : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)) (l1 l2 : List (Nat × Nat))
      (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
      (s1 : WordSemStateFiniteExact width C F),
      evaluate (.seq (.move n1 l1) (.seq (.move n2 l2) p)) s = (res, s1) ∧ res ≠ some .error →
      evaluate (.seq (.move m (mergeMoves l1 l2)) p) s = (res, s1) := by
  intro p l1 l2 s res s1 ⟨h, hne⟩
  rw [evaluateSeqAssoc, evSeq] at h
  rw [evSeq]
  rcases h2 : evaluate (.seq (.move n1 l1) (.move n2 l2)) s with ⟨r2, t2⟩
  rw [h2] at h
  cases r2 with
  | none =>
      have hm := mergeMovesSkip n1 n2 m l1 l2 s none t2 ⟨h2, by simp⟩
      rw [hm]
      exact h
  | some r =>
      simp only at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      have hm := mergeMovesSkip n1 n2 m l1 l2 s (some r) t2 ⟨h2, hne⟩
      rw [hm]

private theorem evRaise (s : WordSemStateFiniteExact width C F) (n : Nat) :
    (evaluate (.raise n) s).1.isSome = true := by
  rw [(evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s n]
  split
  · rfl
  · split <;> rfl

private theorem evReturn (s : WordSemStateFiniteExact width C F) (n : Nat) (ms : List Nat) :
    (evaluate (.return n ms) s).1.isSome = true := by
  rw [(evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.1 s n ms]
  split <;> rfl

private theorem evBreak (s : WordSemStateFiniteExact width C F) (k : Nat) :
    (evaluate (.break k) s).1.isSome = true := by
  rw [(evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s k]; rfl

private theorem evContinue (s : WordSemStateFiniteExact width C F) (k : Nat) :
    (evaluate (.continue k) s).1.isSome = true := by
  rw [(evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s k]; rfl

/-- A first part that does not fall through decides the `Seq` (Flapjack infrastructure). -/
private theorem seq_of_isSome (p1 p2 : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hs : (evaluate p1 s).1.isSome = true) :
    evaluate (.seq p1 p2) s = evaluate p1 s := by
  rw [evSeq]
  rcases hp : evaluate p1 s with ⟨r, t⟩
  rw [hp] at hs
  cases r
  · cases hs
  · rfl

/-- `dest_Seq_Move` succeeds exactly on a `Move` or a `Seq` headed by one (Flapjack
infrastructure). -/
private theorem destSeqMove_some (p : WordLangProgHOL (BitVec width)) (n : Nat)
    (l : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (h : destSeqMove p = some (n, l, rest)) :
    (p = .move n l ∧ rest = .skip) ∨ p = .seq (.move n l) rest := by
  unfold destSeqMove at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inr rfl
  · cases h

/-- Exact HOL `evaluate_SimpSeq` (`word_unreachProofScript.sml:218-242`); `p1`, `p2`, `s`,
`res` and `s1` are free in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_SimpSeq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateSimpSeq {width : Nat} [NeZero width] {C F : Type}
    (p1 p2 : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width C F) :
    evaluate (.seq p1 p2) s = (res, s1) ∧ res ≠ some .error →
    evaluate (simpSeq p1 p2) s = (res, s1) := by
  intro ⟨h, hne⟩
  unfold simpSeq
  by_cases h2 : p2 = .skip
  · rw [if_pos h2]
    subst h2
    rw [evaluateSeqSkip] at h
    exact h
  rw [if_neg h2]
  cases p1 with
  | skip => rw [evaluateSkipSeq] at h; exact h
  | raise n => rw [seq_of_isSome _ _ _ (evRaise s n)] at h; exact h
  | «return» n ms => rw [seq_of_isSome _ _ _ (evReturn s n ms)] at h; exact h
  | «break» k => rw [seq_of_isSome _ _ _ (evBreak s k)] at h; exact h
  | «continue» k => rw [seq_of_isSome _ _ _ (evContinue s k)] at h; exact h
  | move n1 l1 =>
      simp only
      cases hd : destSeqMove p2 with
      | none => exact h
      | some t =>
          obtain ⟨n2, l2, rest⟩ := t
          simp only
          rcases destSeqMove_some p2 n2 l2 rest hd with ⟨rfl, rfl⟩ | rfl
          · rw [if_pos rfl]
            exact mergeMovesSkip n1 n2 _ l1 l2 s res s1 ⟨h, hne⟩
          · by_cases hr : rest = .skip
            · rw [if_pos hr]
              subst hr
              rw [evaluateSeqAssoc, evaluateSeqSkip] at h
              exact mergeMovesSkip n1 n2 _ l1 l2 s res s1 ⟨h, hne⟩
            · rw [if_neg hr]
              exact mergeMovesThm n1 n2 _ rest l1 l2 s res s1 ⟨h, hne⟩
  | _ => exact h

/-- Exact HOL `push_env_handler` (`word_unreachProofScript.sml:244-253`); `x'`, `handler` and
`s` are free in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "push_env_handler"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnvHandler {width : Nat} [NeZero width] {C F : Type}
    (x' : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    pushEnv x' (match handler with
        | none => none
        | some (y1, q2, y2, y3) => some (y1, seqAssocRight q2 .skip, y2, y3)) (decClock s) =
      pushEnv x' handler (decClock s) := by
  cases handler with
  | none => rfl
  | some h =>
      obtain ⟨y1, q2, y2, y3⟩ := h
      rfl

/-- Exact HOL `evaluate_Loop_body_eq` (`word_unreachProofScript.sml:323-344`); `p1`, `p2`,
`names` and `exit_names` are free in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_Loop_body_eq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateLoopBodyEq {width : Nat} [NeZero width] {C F : Type}
    (p1 p2 : WordLangProgHOL (BitVec width)) (names exitNames : NumSet) :
    (∀ (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
        (s1 : WordSemStateFiniteExact width C F),
        evaluate p1 s = (res, s1) ∧ res ≠ some .error → evaluate p2 s = (res, s1)) →
    ∀ (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
      (s1 : WordSemStateFiniteExact width C F),
      evaluate (.loop names p1 exitNames) s = (res, s1) ∧ res ≠ some .error →
      evaluate (.loop names p2 exitNames) s = (res, s1) := by
  intro hbody s
  induction hc : s.clock using Nat.strongRecOn generalizing s with
  | ind c ih =>
  intro res s1 ⟨h, hne⟩
  have hl := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hl] at h ⊢
  cases hcs : cutState (names, .ln) s with
  | none => rw [hcs] at h; simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hne
  | some s' =>
  rw [hcs] at h
  simp only at h ⊢
  rcases he : evaluate p1 s' with ⟨r, t⟩
  rw [he] at h
  have hrne : r ≠ some .error := by
    rintro rfl
    simp only [wordSemContLoop, Bool.false_eq_true, ↓reduceIte, wordSemExitLoop,
      Prod.mk.injEq] at h
    exact hne h.1.symm
  rw [hbody s' r t ⟨he, hrne⟩]
  simp only at h ⊢
  by_cases hcont : wordSemContLoop r = true
  · rw [if_pos hcont] at h ⊢
    by_cases ht0 : t.clock = 0
    · rw [if_pos ht0] at h ⊢; exact h
    · rw [if_neg ht0] at h ⊢
      have hcl : (decClock t).clock < c := by
        have h1 := (evaluate_clock p1 s' r t he).1
        have h2 := (cutState_clock_termdep (names, .ln) s s' hcs).1
        simp only [decClock]
        omega
      exact ih _ hcl (decClock t) rfl res s1 ⟨h, hne⟩
  · rw [if_neg hcont] at h ⊢
    exact h

/-- `p'` reproduces every non-`Error` run of `p` (Flapjack infrastructure). -/
private def Agrees (C F : Type) (p p' : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (s : WordSemStateFiniteExact width C F) (r : Option (WordSemResult width))
    (t : WordSemStateFiniteExact width C F),
    evaluate p s = (r, t) ∧ r ≠ some .error → evaluate p' s = (r, t)

private theorem seqLift (p p' acc : WordLangProgHOL (BitVec width)) (hp : Agrees C F p p')
    (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width C F)
    (h : evaluate (.seq p acc) s = (res, s1)) (hne : res ≠ some .error) :
    evaluate (.seq p' acc) s = (res, s1) := by
  rw [evSeq] at h ⊢
  rcases he : evaluate p s with ⟨r, t⟩
  rw [he] at h
  have hr : r ≠ some .error := by
    rintro rfl
    simp only [Prod.mk.injEq] at h
    exact hne h.1.symm
  rw [hp s r t ⟨he, hr⟩]
  exact h

private theorem iteCongr (v : Cmp) (n : Nat) (ri : WordRegImm (BitVec width))
    (q1 q1' q2 q2' : WordLangProgHOL (BitVec width)) (h1 : Agrees C F q1 q1')
    (h2 : Agrees C F q2 q2') : Agrees C F (.ite v n ri q1 q2) (.ite v n ri q1' q2') := by
  intro s r t ⟨h, hne⟩
  have hi := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hi] at h ⊢
  cases hx : WordSemStateFiniteExact.getVar n s with
  | none => rw [hx] at h; exact h
  | some x =>
  cases hy : WordSemStateFiniteExact.getVarImm ri s with
  | none => rw [hx, hy] at h; exact h
  | some y =>
  rw [hx, hy] at h
  simp only at h ⊢
  cases hc : wordSemWordCmp v x y with
  | none => rw [hc] at h; exact h
  | some b =>
      cases b
      · rw [hc] at h; exact h2 s r t ⟨h, hne⟩
      · rw [hc] at h; exact h1 s r t ⟨h, hne⟩

private theorem mtCongr (q q' : WordLangProgHOL (BitVec width)) (hq : Agrees C F q q') :
    Agrees C F (.mustTerminate q) (.mustTerminate q') := by
  intro s r t ⟨h, hne⟩
  have hm := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  rw [hm] at h ⊢
  by_cases h0 : s.termdep = 0
  · rw [if_pos h0] at h ⊢; exact h
  rw [if_neg h0] at h ⊢
  rcases he : evaluate q { s with clock := wordSemMustTerminateLimit width,
                                  termdep := s.termdep - 1 } with ⟨r0, t0⟩
  rw [he] at h
  have hr : r0 ≠ some .error := by
    rintro rfl
    simp only [Prod.mk.injEq] at h
    exact hne h.1.symm
  rw [hq _ r0 t0 ⟨he, hr⟩]
  exact h

private theorem callNoneIsSome (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    (evaluate (.call none dest args handler) s).1.isSome = true := by
  have hc := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [hc]
  cases hg : WordSemStateFiniteExact.getVars args s with
  | none => rfl
  | some xs =>
  simp only
  by_cases hb : wordSemBadDestArgs dest args = true
  · rw [if_pos hb]; rfl
  rw [if_neg hb]
  cases hf : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) s.code s.stackSize with
  | none => rfl
  | some f =>
  obtain ⟨args1, prog, ss⟩ := f
  simp only
  cases handler with
  | some _ => rfl
  | none =>
  simp only
  by_cases h0 : s.clock = 0
  · rw [if_pos h0]; rfl
  rw [if_neg h0]
  rcases evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with ⟨r, t⟩
  simp only
  by_cases hbad : wordSemBadFunReturn r = true
  · rw [if_pos hbad]; rfl
  · rw [if_neg hbad]
    cases r with
    | none => simp [wordSemBadFunReturn] at hbad
    | some _ => rfl

private theorem callSomeCongr (x1 : List Nat) (x2 : WordLangCutsetsHOL) (x3 x4 : Nat)
    (q1 q1' : WordLangProgHOL (BitVec width)) (dest : Option Nat) (args : List Nat)
    (handler handler' : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (h1 : Agrees C F q1 q1')
    (hH : (handler = none ∧ handler' = none) ∨ ∃ y1 q2 q2' y2 y3,
      handler = some (y1, q2, y2, y3) ∧ handler' = some (y1, q2', y2, y3) ∧
        Agrees C F q2 q2') :
    Agrees C F (.call (some (x1, x2, q1, x3, x4)) dest args handler)
      (.call (some (x1, x2, q1', x3, x4)) dest args handler') := by
  have hpe : ∀ (x : Spt (WordLocW width) × Spt (WordLocW width))
      (st : WordSemStateFiniteExact width C F), pushEnv x handler' st = pushEnv x handler st := by
    intro x st
    rcases hH with ⟨rfl, rfl⟩ | ⟨y1, q2, q2', y2, y3, rfl, rfl, _⟩ <;> rfl
  intro s r t ⟨h, hne⟩
  have hc := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [hc] at h; rw [hc]
  revert h
  cases WordSemStateFiniteExact.getVars args s with
  | none => exact id
  | some xs =>
  simp only
  cases wordSemBadDestArgs dest args
  case true => exact id
  simp only [Bool.false_eq_true, ↓reduceIte, wordSemAddRetLoc]
  cases wordSemFindCode dest (.loc x3 x4 :: xs) s.code s.stackSize with
  | none => exact id
  | some f =>
  obtain ⟨args1, prog, ss⟩ := f
  simp only
  by_cases hn : sptDomainEmpty x2.fst ∨ ¬ x1.Nodup
  · simp only [hn, ↓reduceIte]; exact id
  simp only [hn, ↓reduceIte]
  cases wordSemCutEnvs x2 s.locals with
  | none => exact id
  | some envs =>
  simp only [hpe]
  by_cases h0 : s.clock = 0
  · simp only [h0, ↓reduceIte]; exact id
  simp only [h0, ↓reduceIte]
  generalize evaluate prog (WordSemStateFiniteExact.callEnv args1 ss
      (pushEnv envs handler (decClock s))) = e
  rcases e with ⟨r0, t0⟩
  rcases r0 with _ | r0
  · exact id
  cases r0 with
  | result x ys =>
      simp only
      by_cases hx : x ≠ .loc x3 x4 ∨ ys.length ≠ x1.length
      · simp only [hx, ↓reduceIte]; exact id
      simp only [hx, ↓reduceIte]
      cases popEnv t0 with
      | none => exact id
      | some s1' =>
      simp only
      by_cases hu : sptDomainEqUnion s1'.locals envs.1 envs.2
      · simp only [hu, ↓reduceIte]; exact fun h => h1 _ r t ⟨h, hne⟩
      · simp only [hu, ↓reduceIte]; exact id
  | exception x y =>
      rcases hH with ⟨rfl, rfl⟩ | ⟨y1, q2, q2', y2, y3, rfl, rfl, h2⟩
      · exact id
      · simp only
        by_cases hx : x ≠ .loc y2 y3
        · rw [if_pos hx, if_pos hx]; exact id
        rw [if_neg hx, if_neg hx]
        by_cases hu : sptDomainEqUnion t0.locals envs.1 envs.2
        · simp only [hu, ↓reduceIte]; exact fun h => h2 _ r t ⟨h, hne⟩
        · simp only [hu, ↓reduceIte]; exact id
  | _ => exact id

/-- Exact HOL `evaluate_Seq_assoc_right_lemma` (`word_unreachProofScript.sml:255-321`,
including the suspended `Loop` case of 365-377). HOL proves it by `Seq_assoc_right_ind`;
the Lean proof recurses structurally on the first program. -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml"
  "evaluate_Seq_assoc_right_lemma" (fmap_as_finite_support := [fpRegs, store])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqAssocRightLemma {width : Nat} [NeZero width] {C F : Type} :
    ∀ (p1 p2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F),
      evaluate (.seq p1 p2) s = (res, s1) ∧ res ≠ some .error →
      evaluate (seqAssocRight p1 p2) s = (res, s1)
  | .skip, p2, s, res, s1, ⟨h, _⟩ => by
      rw [evaluateSkipSeq] at h; exact h
  | .seq q1 q2, p2, s, res, s1, ⟨h, hne⟩ => by
      show evaluate (seqAssocRight q1 (seqAssocRight q2 p2)) s = (res, s1)
      refine evaluateSeqAssocRightLemma q1 (seqAssocRight q2 p2) s res s1 ⟨?_, hne⟩
      rw [← evaluateSeqAssoc, evSeq] at h
      rw [evSeq]
      rcases he : evaluate q1 s with ⟨r1, t1⟩
      rw [he] at h
      cases r1 with
      | none => exact evaluateSeqAssocRightLemma q2 p2 t1 res s1 ⟨h, hne⟩
      | some _ => exact h
  | .ite v n ri q1 q2, p2, s, res, s1, ⟨h, hne⟩ => by
      show evaluate (simpSeq (.ite v n ri (seqAssocRight q1 .skip) (seqAssocRight q2 .skip)) p2) s =
        (res, s1)
      refine evaluateSimpSeq _ _ s res s1 ⟨seqLift _ _ _ (iteCongr v n ri q1 _ q2 _
        (fun s' r t ⟨h', hr⟩ => evaluateSeqAssocRightLemma q1 .skip s' r t
          ⟨by rw [evaluateSeqSkip]; exact h', hr⟩)
        (fun s' r t ⟨h', hr⟩ => evaluateSeqAssocRightLemma q2 .skip s' r t
          ⟨by rw [evaluateSeqSkip]; exact h', hr⟩)) s res s1 h hne, hne⟩
  | .mustTerminate q, p2, s, res, s1, ⟨h, hne⟩ => by
      show evaluate (simpSeq (.mustTerminate (seqAssocRight q .skip)) p2) s = (res, s1)
      refine evaluateSimpSeq _ _ s res s1 ⟨seqLift _ _ _ (mtCongr q _
        (fun s' r t ⟨h', hr⟩ => evaluateSeqAssocRightLemma q .skip s' r t
          ⟨by rw [evaluateSeqSkip]; exact h', hr⟩)) s res s1 h hne, hne⟩
  | .call none dest args handler, p2, s, res, s1, ⟨h, _⟩ => by
      show evaluate (.call none dest args handler) s = (res, s1)
      rw [seq_of_isSome _ _ _ (callNoneIsSome dest args handler s)] at h
      exact h
  | .call (some (x1, x2, q1, x3, x4)) dest args handler, p2, s, res, s1, ⟨h, hne⟩ => by
      have hq1 : Agrees C F q1 (seqAssocRight q1 .skip) := fun s' r t ⟨h', hr⟩ =>
        evaluateSeqAssocRightLemma q1 .skip s' r t ⟨by rw [evaluateSeqSkip]; exact h', hr⟩
      cases handler with
      | none =>
          exact evaluateSimpSeq _ _ s res s1 ⟨seqLift _ _ _ (callSomeCongr x1 x2 x3 x4 q1 _ dest
            args none none hq1 (Or.inl ⟨rfl, rfl⟩)) s res s1 h hne, hne⟩
      | some hh =>
          obtain ⟨y1, q2, y2, y3⟩ := hh
          have hq2 : Agrees C F q2 (seqAssocRight q2 .skip) := fun s' r t ⟨h', hr⟩ =>
            evaluateSeqAssocRightLemma q2 .skip s' r t ⟨by rw [evaluateSeqSkip]; exact h', hr⟩
          exact evaluateSimpSeq _ _ s res s1 ⟨seqLift _ _ _ (callSomeCongr x1 x2 x3 x4 q1 _ dest
            args (some (y1, q2, y2, y3)) (some (y1, seqAssocRight q2 .skip, y2, y3)) hq1
            (Or.inr ⟨y1, q2, _, y2, y3, rfl, rfl, hq2⟩)) s res s1 h hne, hne⟩
  | .loop names body exitNames, p2, s, res, s1, ⟨h, hne⟩ => by
      show evaluate (simpSeq (.loop names (seqAssocRight body .skip) exitNames) p2) s = (res, s1)
      refine evaluateSimpSeq _ _ s res s1 ⟨seqLift _ _ _
        (evaluateLoopBodyEq body _ names exitNames
          (fun s' r t ⟨h', hr⟩ => evaluateSeqAssocRightLemma body .skip s' r t
            ⟨by rw [evaluateSeqSkip]; exact h', hr⟩)) s res s1 h hne, hne⟩
  | .move a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .inst a, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .assign a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .get a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .set a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .store a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .alloc a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .storeConsts a b c d e, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .raise a, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .return a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .break a, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .continue a, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .tick, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .opCurrHeap a b c, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .locValue a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .install a b c d e, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .codeBufferWrite a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .dataBufferWrite a b, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .ffi a b c d e f, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh
  | .shareInst a b c, p2, s, res, s1, hh => evaluateSimpSeq _ p2 s res s1 hh

/-- Exact HOL `evaluate_remove_unreach` (`word_unreachProofScript.sml:368-377`). -/
@[hol "cakeml/compiler/backend/proofs/word_unreachProofScript.sml" "evaluate_remove_unreach"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateRemoveUnreach {width : Nat} [NeZero width] {C F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F),
      evaluate p s = (res, s1) ∧ res ≠ some .error → evaluate (removeUnreach p) s = (res, s1) :=
  fun p s res s1 ⟨h, hne⟩ => evaluateSeqAssocRightLemma p .skip s res s1
    ⟨by rw [evaluateSeqSkip]; exact h, hne⟩

end Semantics

end Flapjack.Compiler.Backend.WordUnreach
