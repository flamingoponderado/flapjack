module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Locations
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-!
# Stack-frame lemmas of HOL `word_elimProof`

Counterpart of `cakeml/compiler/backend/proofs/word_elimProofScript.sml:203-289`:
`get_stack_hd_thm`, `get_stack_LASTN`, `get_stack_CONS`,
`get_stack_enc_stack` and `get_stack_dec_stack`.

HOL's `StackFrame lsz e0 e handler` is the tagged `WordSemStackFrame width`, and
HOL's `LASTN` is `wordSemLastN` (the `rich_list` rendering in `WordSem.Env`).
The untagged helpers `getStack_nil`, `getStack_cons` and
`sptUnion_ln_right` are Flapjack infrastructure with no separate HOL original.
-/

namespace Flapjack.Compiler.Backend.WordElim

namespace WordElimStacksSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged `pushEnv_def2` of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordElimStacksSupport

/-- Flapjack-only helper: the `get_stack` clause for the empty stack. -/
@[simp] theorem getStack_nil {width : Nat} [NeZero width] :
    getStack ([] : List (WordSemStackFrame width)) = .ln := rfl

/-- Flapjack-only helper: the `get_stack` clause for a cons. -/
@[simp] theorem getStack_cons {width : Nat} [NeZero width] (lsz : Option Nat)
    (nonGcCutset gcCutset : List (Nat × WordLocW width))
    (handler : Option (Nat × Nat × Nat)) (rest : List (WordSemStackFrame width)) :
    getStack (.stackFrame lsz nonGcCutset gcCutset handler :: rest) =
      sptUnion (sptUnion (getNumWordlocAlist nonGcCutset) (getNumWordlocAlist gcCutset))
        (getStack rest) := rfl

/-- Flapjack-only helper: unioning `LN` on the right is the identity. -/
@[simp] theorem sptUnion_ln_right {α : Type} (tree : Spt α) : sptUnion tree .ln = tree := by
  cases tree <;> simp [sptUnion]

/-- Exact HOL `get_stack_hd_thm` (`word_elimProofScript.sml:212-231`): with the
    frame's cut sets at the head, the head frame's locals and the tail stack are
    inside `dr`.  HOL's `lsz` is free in the source statement and is bound here
    after `t`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_stack_hd_thm"
  (words_as_type_indexed_bitvec)]
theorem getStack_hd_thm {width : Nat} [NeZero width] (stack : List (WordSemStackFrame width))
    (dr : Nat → Prop) (l0 l : List (Nat × WordLocW width))
    (opt : Option (Nat × Nat × Nat)) (t : List (WordSemStackFrame width))
    (lsz : Option Nat)
    (premise : sptDomainSet (getStack stack) ⊆ dr ∧
      stack = .stackFrame lsz l l0 opt :: t) :
    sptDomainSet (getLocals (sptUnion (sptFromAList l0) (sptFromAList l))) ⊆ dr ∧
      sptDomainSet (getStack t) ⊆ dr := by
  obtain ⟨hd, shape⟩ := premise
  subst shape
  constructor
  · change ∀ n, sptMem n (getLocals (sptUnion (sptFromAList l0) (sptFromAList l))) → dr n
    intro n hmem
    have hunion := getLocals_union_subset (sptFromAList l0) (sptFromAList l) hmem
    change sptMem n (sptUnion (getLocals (sptFromAList l0)) (getLocals (sptFromAList l))) at hunion
    rcases (sptMem_sptUnion _ _ _).mp hunion with hl0 | hl
    · have hmemStack : sptMem n (getStack (.stackFrame lsz l l0 opt :: t)) := by
        simp only [getStack_cons, sptMem_sptUnion]
        exact Or.inl (Or.inr (getNumWordlocAlist_get_locals l0 hl0))
      exact hd hmemStack
    · have hmemStack : sptMem n (getStack (.stackFrame lsz l l0 opt :: t)) := by
        simp only [getStack_cons, sptMem_sptUnion]
        exact Or.inl (Or.inl (getNumWordlocAlist_get_locals l hl))
      exact hd hmemStack
  · change ∀ n, sptMem n (getStack t) → dr n
    intro n hmem
    have hmemStack : sptMem n (getStack (.stackFrame lsz l l0 opt :: t)) := by
      simp only [getStack_cons, sptMem_sptUnion]
      exact Or.inr hmem
    exact hd hmemStack

/-- Exact HOL `get_stack_CONS` (`word_elimProofScript.sml:241-246`): a single
    frame and the tail are both inside the whole stack's location set. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_stack_CONS"
  (words_as_type_indexed_bitvec)]
theorem getStack_CONS {width : Nat} [NeZero width] (h : WordSemStackFrame width)
    (t : List (WordSemStackFrame width)) :
    sptDomainSet (getStack [h]) ⊆ sptDomainSet (getStack (h :: t)) ∧
      sptDomainSet (getStack t) ⊆ sptDomainSet (getStack (h :: t)) := by
  cases h with
  | stackFrame lsz nonGcCutset gcCutset handler =>
      constructor
      · change ∀ n, sptMem n (getStack [.stackFrame lsz nonGcCutset gcCutset handler]) →
          sptMem n (getStack (.stackFrame lsz nonGcCutset gcCutset handler :: t))
        intro n hmem
        rw [getStack_cons, getStack_nil, sptUnion_ln_right, sptMem_sptUnion] at hmem
        rw [getStack_cons, sptMem_sptUnion, sptMem_sptUnion]
        exact Or.inl hmem
      · change ∀ n, sptMem n (getStack t) →
          sptMem n (getStack (.stackFrame lsz nonGcCutset gcCutset handler :: t))
        intro n hmem
        rw [getStack_cons, sptMem_sptUnion, sptMem_sptUnion]
        exact Or.inr hmem

/-- Flapjack-only helper: HOL's `LASTN_ALT` (`rich_list`, outside `cakeml/`),
    `LASTN n xs = DROP (LENGTH xs - n) xs`, for the `wordSemLastN` rendering. -/
theorem wordSemLastN_eq_drop {α : Type} (n : Nat) (xs : List α) :
    wordSemLastN n xs = xs.drop (xs.length - n) := by
  simp only [wordSemLastN, List.take_reverse, List.reverse_reverse]

/-- Flapjack-only helper: `get_stack` of a concatenation is the union of the
    two halves' location sets. -/
theorem getStack_append {width : Nat} [NeZero width]
    (xs ys : List (WordSemStackFrame width)) :
    getStack (xs ++ ys) = sptUnion (getStack xs) (getStack ys) := by
  induction xs with
  | nil => simp [getStack_nil, sptUnion]
  | cons head tail ih =>
      cases head with
      | stackFrame lsz nonGcCutset gcCutset handler =>
          simp only [List.cons_append, getStack_cons, ih, sptUnion_assoc]

/-- Flapjack-only helper: a suffix's location set is inside the whole list's. -/
theorem getStack_suffix {width : Nat} [NeZero width]
    (xs ys : List (WordSemStackFrame width)) :
    sptDomainSet (getStack ys) ⊆ sptDomainSet (getStack (xs ++ ys)) := by
  intro location hmem
  rw [getStack_append]
  change sptMem location (sptUnion (getStack xs) (getStack ys))
  rw [sptMem_sptUnion]
  exact Or.inr hmem

/-- Flapjack-only helper: dropping a prefix keeps the location set inside the
    whole stack's. -/
theorem getStack_drop {width : Nat} [NeZero width] (k : Nat)
    (stack : List (WordSemStackFrame width)) :
    sptDomainSet (getStack (stack.drop k)) ⊆ sptDomainSet (getStack stack) := by
  conv_rhs => rw [← List.take_append_drop k stack]
  exact getStack_suffix (stack.take k) (stack.drop k)

/-- Exact HOL `get_stack_LASTN` (`word_elimProofScript.sml:233-239`): the last
    `n` frames contribute only locations already in the whole stack.  HOL's
    `LASTN` is `wordSemLastN`, and `domain … ⊆ …` is stated literally with
    `sptDomainSet`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_stack_LASTN"
  (words_as_type_indexed_bitvec)]
theorem getStack_LASTN {width : Nat} [NeZero width] (stack : List (WordSemStackFrame width))
    (n : Nat) :
    sptDomainSet (getStack (wordSemLastN n stack)) ⊆ sptDomainSet (getStack stack) := by
  rw [wordSemLastN_eq_drop]
  exact getStack_drop (stack.length - n) stack

/-- Exact HOL `get_stack_enc_stack` (`word_elimProofScript.sml:248-260`): every
    location named by an encoded stack entry lies in `reachable`, given that
    the stack's own locations do.  HOL's `reachable` is a `num_map`, so its
    payload type is independent, as in the typed capture; the `case
    dest_word_loc e of` result is stated as a `match`.
-/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_stack_enc_stack"
  (words_as_type_indexed_bitvec)]
theorem getStack_encStack {width : Nat} [NeZero width] {β : Type}
    (stack : List (WordSemStackFrame width)) (reachable : Spt β) :
    sptDomainSet (getStack stack) ⊆ sptDomainSet reachable →
      ∀ e, e ∈ wordSemEncStack stack →
        (match destWordLoc e with
          | none => (∅ : Set Nat)
          | some n => ({n} : Set Nat)) ⊆ sptDomainSet reachable := by
  induction stack with
  | nil =>
      intro _ e hmem
      simp only [wordSemEncStack, List.not_mem_nil] at hmem
  | cons head tail ih =>
      cases head with
      | stackFrame lsz nonGcCutset gcCutset handler =>
          intro hprem e hmem
          simp only [wordSemEncStack, List.mem_append, List.mem_map] at hmem
          rcases hmem with ⟨⟨key, value⟩, hentry, hvalue⟩ | htail
          · cases e with
            | word w =>
                simp [destWordLoc_word]
            | loc block offset =>
                rw [destWordLoc_loc]
                have hval : value = .loc block offset := hvalue
                rw [hval] at hentry
                intro location hmem
                simp only [Set.mem_singleton_iff] at hmem
                rw [hmem]
                exact hprem (by
                  change sptMem block
                    (getStack (.stackFrame lsz nonGcCutset gcCutset handler :: tail))
                  rw [getStack_cons, sptMem_sptUnion, sptMem_sptUnion]
                  exact Or.inl (Or.inr
                    ((getNumWordlocAlist_thm (α := Unit) block () gcCutset).mp
                      ⟨offset, List.mem_map.mpr ⟨(key, .loc block offset), hentry, rfl⟩⟩)))
          · have hpremTail : sptDomainSet (getStack tail) ⊆ sptDomainSet reachable := by
              intro location hmem
              exact hprem (by
                change sptMem location
                  (getStack (.stackFrame lsz nonGcCutset gcCutset handler :: tail))
                rw [getStack_cons, sptMem_sptUnion, sptMem_sptUnion]
                exact Or.inr hmem)
            exact ih hpremTail e htail

/-- Flapjack-only helper: `get_stack_dec_stack` by induction on the stack, with
    the encoded value list, `reachable` and the decoded stack generalised; the
    three HOL premises are separate arguments here. -/
theorem getStack_decStack_aux {width : Nat} [NeZero width] {β : Type}
    (stack : List (WordSemStackFrame width)) :
    ∀ (locs : List (WordLocW width)) (reachable : Spt β)
      (newStack : List (WordSemStackFrame width)),
      (∀ n n0, (.loc n n0 : WordLocW width) ∈ locs → sptMem n reachable) →
      sptDomainSet (getStack stack) ⊆ sptDomainSet reachable →
      wordSemDecStack locs stack = some newStack →
      sptDomainSet (getStack newStack) ⊆ sptDomainSet reachable := by
  induction stack with
  | nil =>
      intro locs reachable newStack hlocals hprem hdec
      cases locs with
      | nil =>
          simp only [wordSemDecStack] at hdec
          injection hdec with hnew
          subst hnew
          intro location hmem
          exact hprem hmem
      | cons head tail =>
          simp only [wordSemDecStack] at hdec
          exact absurd hdec (by simp)
  | cons frame rest ih =>
      intro locs reachable newStack hlocals hprem hdec
      cases frame with
      | stackFrame lsz nonGcCutset gcCutset handler =>
          rw [wordSemDecStack] at hdec
          split at hdec
          · exact absurd hdec (by simp)
          · split at hdec
            · exact absurd hdec (by simp)
            · rename_i decoded hdecSome
              injection hdec with hnew
              subst hnew
              intro location hmem
              have ihapp := ih (locs.drop gcCutset.length) reachable decoded
                (fun n n0 hmem => hlocals n n0 (List.mem_of_mem_drop hmem))
                (by
                  intro location hmem'
                  exact hprem (by
                    change sptMem location
                      (getStack (.stackFrame lsz nonGcCutset gcCutset handler :: rest))
                    rw [getStack_cons, sptMem_sptUnion, sptMem_sptUnion]
                    exact Or.inr hmem'))
                hdecSome
              change sptMem location
                (sptUnion
                  (sptUnion (getNumWordlocAlist nonGcCutset)
                    (getNumWordlocAlist
                      ((gcCutset.map Prod.fst).zip (locs.take gcCutset.length))))
                  (getStack decoded)) at hmem
              rw [sptMem_sptUnion, sptMem_sptUnion] at hmem
              rcases hmem with (hnonGc | hgc) | htail
              · exact hprem (by
                  change sptMem location
                    (getStack (.stackFrame lsz nonGcCutset gcCutset handler :: rest))
                  rw [getStack_cons, sptMem_sptUnion, sptMem_sptUnion]
                  exact Or.inl (Or.inl hnonGc))
              · obtain ⟨offset, hentry⟩ :=
                  (getNumWordlocAlist_thm (α := Unit) location ()
                    ((gcCutset.map Prod.fst).zip (locs.take gcCutset.length))).mpr hgc
                rw [List.map_snd_zip (l₁ := gcCutset.map Prod.fst)
                  (l₂ := locs.take gcCutset.length) (by simp)] at hentry
                exact hlocals location offset (List.mem_of_mem_take hentry)
              · exact ihapp htail

/-- Exact HOL `get_stack_dec_stack` (`word_elimProofScript.sml:262-287`): after
    decoding, the new stack's locations are inside `reachable`, given the
    encoded values, the old stack and the decoded stack.  HOL states the three
    conditions as ONE conjunction premise; `reachable` is a `num_map`, so its
    payload type is independent, as in the typed capture. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_stack_dec_stack"
  (words_as_type_indexed_bitvec)]
theorem getStack_decStack {width : Nat} [NeZero width] {β : Type}
    (locs : List (WordLocW width)) (stack : List (WordSemStackFrame width))
    (reachable : Spt β) (newStack : List (WordSemStackFrame width)) :
    ((∀ n n0, (.loc n n0 : WordLocW width) ∈ locs → sptMem n reachable) ∧
      sptDomainSet (getStack stack) ⊆ sptDomainSet reachable ∧
      wordSemDecStack locs stack = some newStack) →
    sptDomainSet (getStack newStack) ⊆ sptDomainSet reachable := by
  rintro ⟨hlocals, hprem, hdec⟩
  exact getStack_decStack_aux stack locs reachable newStack hlocals hprem hdec

/-- Exact HOL `push_env_def2` (`word_elimProofScript.sml:910-922`): the fully
    expanded `push_env` with its `let` bindings, including the handler field
    update `case handler of NONE => s.handler | SOME x => LENGTH s.stack` on
    the rebound handler.  HOL writes the statement with free `env`, `handler`
    and `s`; Lean binds the same three in that order. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "push_env_def2"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnv_def2 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.pushEnv envs handler state =
      (let l0 := sptToAList envs.1
       let (l, permute) := wordSemEnvToList envs.2 state.permute
       let handler := match handler with
         | none => none
         | some (_, _, l1, l2) => some (state.handler, l1, l2)
       let stack := WordSemStackFrame.stackFrame state.localsSize l0 l handler :: state.stack
       { state with
         stack := stack
         stackMax := wordSemOptionMax state.stackMax (wordSemStackSize stack)
         permute := permute
         handler := match handler with
           | none => state.handler
           | some _ => state.stack.length }) := by
  cases handler with
  | none => rfl
  | some entry =>
      obtain ⟨w, h, l1, l2⟩ := entry
      rfl

end Flapjack.Compiler.Backend.WordElim
