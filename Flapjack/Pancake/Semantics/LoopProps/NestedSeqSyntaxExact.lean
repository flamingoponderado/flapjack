import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact
import Flapjack.Pancake.Semantics.LoopProps.CutSets
import Flapjack.Pancake.LoopLang.AssignedVars

/-!
# loopProps `survives`/`cut_sets` `nested_seq` lemmas and friends

Counterparts of `cakeml/pancake/semantics/loopPropsScript.sml`'s
`survives_nested_seq_intro` (719), `nested_assigns_survives` (729),
`cut_sets_nested_seq` (767), `lookup_alist_insert_any` (321) and
`evaluate_tail_calls_eqs` (74) over the exact carriers (bead `flapjack-pxgp.15`).
-/

namespace Flapjack

/-- The two exact renderings of HOL `nested_seq_def` (`loopNestedSeqHOL` in
    `LoopLang.lean` and `holLoopNestedSeq` in `LoopLang/AssignedVars.lean`) are the
    same function, so lemmas stated over either compose. -/
theorem loopNestedSeqHOL_eq_holLoopNestedSeq {width : Nat} [NeZero width] :
    (loopNestedSeqHOL : List (HolLoopProg width) → HolLoopProg width) = holLoopNestedSeq := by
  funext p
  induction p with
  | nil => rfl
  | cons c p ih => simp [loopNestedSeqHOL, holLoopNestedSeq, ih]

/-- HOL `alist$ALOOKUP` (`ALOOKUP [] q = NONE`,
    `ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q`).  HOL library,
    no tag. -/
def holAlookup {α β : Type} [DecidableEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, q => if x = q then some y else holAlookup t q

variable {width : Nat} [NeZero width]

/-- Exact HOL `survives_nested_seq_intro` (`loopPropsScript.sml:719-723`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "survives_nested_seq_intro"
  (words_as_type_indexed_bitvec)]
theorem survives_nested_seq_intro :
    ∀ (p q : List (HolLoopProg width)) (n : Nat),
      survivesHOLExact n (holLoopNestedSeq p) = true ∧
      survivesHOLExact n (holLoopNestedSeq q) = true →
      survivesHOLExact n (holLoopNestedSeq (p ++ q)) = true
  | [], q, n, ⟨_, hq⟩ => hq
  | c :: p, q, n, ⟨hp, hq⟩ => by
      simp only [List.cons_append, holLoopNestedSeq, survivesHOLExact, Bool.and_eq_true] at hp ⊢
      exact ⟨hp.1, survives_nested_seq_intro p q n ⟨hp.2, hq⟩⟩

/-- Exact HOL `nested_assigns_survives` (`loopPropsScript.sml:729-732`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "nested_assigns_survives"
  (words_as_type_indexed_bitvec)]
theorem nested_assigns_survives :
    ∀ (xs : List Nat) (ys : List (HolLoopExp width)) (n : Nat),
      xs.length = ys.length →
      survivesHOLExact n (holLoopNestedSeq (List.zipWith HolLoopProg.assign xs ys)) = true
  | [], [], _, _ => by simp [holLoopNestedSeq, survivesHOLExact]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: xs, y :: ys, n, h => by
      simp only [List.zipWith_cons_cons, holLoopNestedSeq, survivesHOLExact, Bool.true_and]
      exact nested_assigns_survives xs ys n (by simpa using h)

/-- Exact HOL `cut_sets_nested_seq` (`loopPropsScript.sml:767-769`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "cut_sets_nested_seq"
  (words_as_type_indexed_bitvec)]
theorem cut_sets_nested_seq :
    ∀ (p q : List (HolLoopProg width)) (l : NumSet),
      cutSetsHOL l (holLoopNestedSeq (p ++ q)) =
        cutSetsHOL (cutSetsHOL l (holLoopNestedSeq p)) (holLoopNestedSeq q)
  | [], q, l => by simp [holLoopNestedSeq, cutSetsHOL]
  | c :: p, q, l => by
      simp only [List.cons_append, holLoopNestedSeq, cutSetsHOL]
      exact cut_sets_nested_seq p q (cutSetsHOL l c)

/-- Exact HOL `lookup_alist_insert_any` (`loopPropsScript.sml:321-325`):
    `lookup n (alist_insert xs ys t) = case ALOOKUP (ZIP (xs,ys)) n of
      NONE => lookup n t | SOME v => SOME v`.  HOL `ZIP` truncates to the shorter
    list exactly as `List.zip`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "lookup_alist_insert_any"]
theorem lookup_alist_insert_any {α : Type} :
    ∀ (n : Nat) (xs : List Nat) (ys : List α) (t : Spt α),
      sptLookup n (LoopSemStateFiniteExact.sptAlistInsert xs ys t) =
        match holAlookup (xs.zip ys) n with
        | none => sptLookup n t
        | some v => some v
  | n, [], _, t => by simp [LoopSemStateFiniteExact.sptAlistInsert, holAlookup]
  | n, _ :: _, [], t => by simp [LoopSemStateFiniteExact.sptAlistInsert, holAlookup]
  | n, x :: xs, y :: ys, t => by
      simp only [LoopSemStateFiniteExact.sptAlistInsert, List.zip_cons_cons, holAlookup]
      rw [sptLookup_sptInsert]
      by_cases h : n = x
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h)]; exact lookup_alist_insert_any n xs ys t

namespace LoopPropsNestedSeqSyntaxFiniteSupport

/-- Local same-module witness for the canonical finite-support
`LoopSemStateFiniteExact` carrier used by the `fmap_as_finite_support := [globals]`
qualified `evaluate_tail_calls_eqs` port in this module (re-exports the checked
witness of `Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopPropsNestedSeqSyntaxFiniteSupport

namespace LoopSemStateFiniteExact

variable {F : Type}

/-- Exact HOL `evaluate_tail_calls_eqs` (`loopPropsScript.sml:74-78`):
    `!f t lc x. find_code (SOME f) ([]:'a word_loc list) t.code = SOME x ==>
      evaluate ((Call NONE (SOME f) [] NONE), t) =
      evaluate (Call NONE (SOME f) [] NONE, t with locals := lc)`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_tail_calls_eqs"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_tail_calls_eqs (f : Nat) (t : LoopSemStateFiniteExact width F)
    (lc : Spt (WordLocW width)) (x : Spt (WordLocW width) × HolLoopProg width)
    (h : findCode (some f) ([] : List (WordLocW width)) t.code = some x) :
    evaluate (.call none (some f) [] none) t =
      evaluate (.call none (some f) [] none) { t with locals := lc } := by
  rw [evaluate, evaluate]
  simp only [getVars]
  cases x with
  | mk env prog =>
    simp only [h]
    rfl

end LoopSemStateFiniteExact

end Flapjack
