import Flapjack.Compiler.Backend.WordCopy.Proofs.Move
import Flapjack.Compiler.Backend.WordUnreach.Proofs
import Flapjack.Misc.SptreeLookup

/-!
# word_copyProof: moves, store equivalences and expression congruences

Ports of `cakeml/compiler/backend/proofs/word_copyProofScript.sml` lines 758-1156 other than
the `copy_prop_inst` semantics: the model after a disjoint `Move`, `copy_prop_move_correct`,
the `word_exp` congruences, `remove_eq` commutation and `unset_var`, `copy_prop_share`, the
`set_store_eq`/`lookup_store_eq` facts and models, and the `Loop` body congruence. HOL
`set tt ∩ set ss = ∅` is `∀ x, ¬ (x ∈ tt ∧ x ∈ ss)`.
-/

namespace Flapjack.Compiler.Backend.WordCopy

open Flapjack

namespace WordCopyStoreWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordCopyStoreWitnesses

/-- Exact HOL `copy_prop_move_model` (`word_copyProofScript.sml:758-806`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_model"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem copyPropMoveModel {width : Nat} [NeZero width] {C F : Type} {cs cs' : CopyState}
    {st : WordSemStateFiniteExact width C F} {moves moves' : List (Nat × Nat)}
    {values : List (WordLocW width)} :
    cpStateInv cs → cpStateModels cs st →
      (∀ x, ¬ (x ∈ moves.map Prod.fst ∧ x ∈ moves.map Prod.snd)) →
      copyPropMove moves cs = (moves', cs') →
      WordSemStateFiniteExact.getVars (moves.map Prod.snd) st = some values →
      cpStateModels cs' (WordSemStateFiniteExact.setVars (moves.map Prod.fst) values st) := by
  intro hinv hm
  induction moves generalizing values moves' cs' with
  | nil =>
      intro _ hmv hv
      simp only [copyPropMove, Prod.mk.injEq] at hmv
      obtain ⟨_, rfl⟩ := hmv
      exact cpStateModelsSame ⟨hm, rfl, rfl⟩
  | cons p moves ih =>
      obtain ⟨t, s⟩ := p
      intro hdis hmv hv
      simp only [List.map_cons, WordSemStateFiniteExact.getVars] at hv
      cases hs : WordSemStateFiniteExact.getVar s st with
      | none => rw [hs] at hv; cases hv
      | some val =>
      rw [hs] at hv
      cases hr : WordSemStateFiniteExact.getVars (moves.map Prod.snd) st with
      | none => rw [hr] at hv; cases hv
      | some values' =>
      rw [hr] at hv
      cases hv
      have hcs' : cs' = setEq (removeEq (copyPropMove moves cs).2 t) t s := by
        have := congrArg Prod.snd hmv
        simp only [copyPropMove] at this
        exact this.symm
      subst hcs'
      have hdis' : ∀ x, ¬ (x ∈ moves.map Prod.fst ∧ x ∈ moves.map Prod.snd) := by
        intro x ⟨h1, h2⟩
        exact hdis x ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
      have ih' := ih hdis' (Prod.ext rfl rfl) hr
      have hsn : s ∉ moves.map Prod.fst := by
        intro h; exact hdis s ⟨List.mem_cons_of_mem _ h, List.mem_cons_self⟩
      have hlook : sptLookup s (WordSemStateFiniteExact.setVars (moves.map Prod.fst) values' st).locals
          = some val := by
        simp only [WordSemStateFiniteExact.setVars]
        rw [lookupAlistInsertSame hsn]; exact hs
      exact setEqRemoveEqModels ⟨copyPropMove_inv2 moves cs hinv, ih', hlook⟩

/-- Exact HOL `EVERY_NOT_MEM_D` (`word_copyProofScript.sml:808-812`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "EVERY_NOT_MEM_D"]
theorem everyNotMemD {tt ss : List Nat} :
    (∀ t ∈ tt, t ∉ ss) → ∀ x, ¬ (x ∈ tt ∧ x ∈ ss) :=
  fun h x ⟨h1, h2⟩ => h x h1 h2

/-- Exact HOL `copy_prop_move_correct` (`word_copyProofScript.sml:814-838`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_move_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem copyPropMoveCorrect {width : Nat} [NeZero width] {C F : Type} {cs cs' : CopyState}
    {st st' : WordSemStateFiniteExact width C F} {pri : Nat} {moves : List (Nat × Nat)}
    {prog' : WordLangProgHOL (BitVec width)} {err : Option (WordSemResult width)} :
    cpStateInv cs ∧ cpStateModels cs st ∧ copyPropProg (.move pri moves) cs = (prog', cs') ∧
      Flapjack.WordSemStateFiniteExact.evaluate (.move pri moves) st = (err, st') →
    Flapjack.WordSemStateFiniteExact.evaluate prog' st = (err, st') ∧
      (err = none → cpStateModels cs' st') := by
  rintro ⟨hinv, hm, hp, he⟩
  simp only [copyPropProg] at hp
  split at hp
  case isTrue hdis =>
    rcases hmv : copyPropMove moves cs with ⟨moves', cs''⟩
    rw [hmv] at hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    refine ⟨copyPropMoveEval hinv hm hmv he, fun herr => ?_⟩
    subst herr
    rw [(WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.1
      st pri moves] at he
    split at he
    · cases hg : WordSemStateFiniteExact.getVars (moves.map Prod.snd) st with
      | none => rw [hg] at he; cases he
      | some vs =>
          rw [hg] at he
          simp only [Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          exact copyPropMoveModel hinv hm (everyNotMemD hdis) hmv hg
    · cases he
  case isFalse =>
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨he, fun _ => emptyEqModel⟩

/-- Exact HOL `word_exp_cong_Var` (`word_copyProofScript.sml:840-845`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "word_exp_cong_Var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpCongVar {width : Nat} [NeZero width] {C F : Type}
    {st : WordSemStateFiniteExact width C F} {x x' : Nat} :
    WordSemStateFiniteExact.getVar x' st = WordSemStateFiniteExact.getVar x st →
      WordSemStateFiniteExact.wordExp st (.var x') = WordSemStateFiniteExact.wordExp st (.var x) := by
  intro h; simp only [WordSemStateFiniteExact.wordExp]; exact h

/-- Exact HOL `word_exp_cong_Load` (`word_copyProofScript.sml:847-852`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "word_exp_cong_Load"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpCongLoad {width : Nat} [NeZero width] {C F : Type}
    {st : WordSemStateFiniteExact width C F} {addr addr' : WordLangExpHOL (BitVec width)} :
    WordSemStateFiniteExact.wordExp st addr' = WordSemStateFiniteExact.wordExp st addr →
      WordSemStateFiniteExact.wordExp st (.load addr') =
        WordSemStateFiniteExact.wordExp st (.load addr) := by
  intro h; simp only [WordSemStateFiniteExact.wordExp, h]

/-- Exact HOL `word_exp_cong_Op` (`word_copyProofScript.sml:854-862`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "word_exp_cong_Op"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpCongOp {width : Nat} [NeZero width] {C F : Type}
    {st : WordSemStateFiniteExact width C F} {op : BinOp}
    {aa aa' : List (WordLangExpHOL (BitVec width))} :
    aa'.map (WordSemStateFiniteExact.wordExp st) = aa.map (WordSemStateFiniteExact.wordExp st) →
      WordSemStateFiniteExact.wordExp st (.op op aa') =
        WordSemStateFiniteExact.wordExp st (.op op aa) := by
  intro h
  simp only [WordSemStateFiniteExact.wordExp]
  have e : ∀ l : List (WordLangExpHOL (BitVec width)),
      (l.attach.map fun ⟨e, _⟩ => WordSemStateFiniteExact.wordExp st e) =
        l.map (WordSemStateFiniteExact.wordExp st) := by
    intro l; simp
  rw [e, e, h]

/-- Exact HOL `word_exp_cong_Shift` (`word_copyProofScript.sml:864-870`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "word_exp_cong_Shift"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpCongShift {width : Nat} [NeZero width] {C F : Type}
    {st : WordSemStateFiniteExact width C F} {sh : Shift}
    {e e' e2 e2' : WordLangExpHOL (BitVec width)} :
    WordSemStateFiniteExact.wordExp st e' = WordSemStateFiniteExact.wordExp st e →
      WordSemStateFiniteExact.wordExp st e2' = WordSemStateFiniteExact.wordExp st e2 →
      WordSemStateFiniteExact.wordExp st (.shift sh e' e2') =
        WordSemStateFiniteExact.wordExp st (.shift sh e e2) := by
  intro h1 h2; simp only [WordSemStateFiniteExact.wordExp, h1, h2]

/-- Exact HOL `remove_eq_comm` (`word_copyProofScript.sml:931-935`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_comm"]
theorem removeEqComm {cs : CopyState} {x y : Nat} :
    removeEq (removeEq cs x) y = removeEq (removeEq cs y) x := by
  unfold removeEq
  cases hx : sptLookup x cs.toEq <;> cases hy : sptLookup y cs.toEq <;> simp_all [emptyEq]

/-- Exact HOL `remove_eq_model_unset_var` (`word_copyProofScript.sml:956-965`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_model_unset_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem removeEqModelUnsetVar {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {t : Nat} :
    cpStateInv cs → cpStateModels cs st →
      cpStateModels (removeEq cs t) (WordSemStateFiniteExact.unsetVar t st) := by
  rintro ⟨_, _, _, h4⟩ ⟨m1, m2⟩
  unfold removeEq
  cases ht : sptLookup t cs.toEq with
  | some _ => exact emptyEqModel
  | none =>
      dsimp only
      have hne : ∀ c vrep, sptLookup c cs.fromEq = some vrep → vrep ≠ t := by
        rintro c vrep hc rfl; have := h4 c vrep hc; rw [ht] at this; cases this
      refine ⟨fun v c vrep hv hc => ?_, fun s c vrep hsc hc => ?_⟩
      · have hvt : v ≠ t := by rintro rfl; rw [ht] at hv; cases hv
        simp only [WordSemStateFiniteExact.unsetVar, sptLookup_sptDelete, if_neg hvt,
          if_neg (hne c vrep hc)]
        exact m1 v c vrep hv hc
      · simp only [WordSemStateFiniteExact.unsetVar, sptLookup_sptDelete, if_neg (hne c vrep hc)]
        exact m2 s c vrep hsc hc

/-- Exact HOL `CPstate_modelsD_copy_prop_share` (`word_copyProofScript.sml:983-991`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_modelsD_copy_prop_share"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cpStateModelsDCopyPropShare {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {e : WordLangExpHOL (BitVec width)} :
    cpStateInv cs → cpStateModels cs st →
      WordSemStateFiniteExact.wordExp st (copyPropShare e cs) = WordSemStateFiniteExact.wordExp st e := by
  intro hinv hm
  unfold copyPropShare
  split
  · exact cpStateModelsDVar ⟨hinv, hm⟩
  · apply wordExpCongOp
    simp only [List.map_cons, List.map_nil, cpStateModelsDVar ⟨hinv, hm⟩]
  · rfl

/-- Exact HOL `lookup_store_eq_SOME` (`word_copyProofScript.sml:993-1000`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_SOME"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem lookupStoreEqSome {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {s : WordStoreHOL} {v : Nat} :
    cpStateModels cs st ∧ lookupStoreEq cs s = some v →
      st.store.lookup s = sptLookup v st.locals := by
  rintro ⟨⟨_, m2⟩, h⟩
  unfold lookupStoreEq at h
  cases hs : cs.storeToEq.lookup s with
  | none => rw [hs] at h; cases h
  | some c =>
      rw [hs] at h
      simp only at h
      cases hf : sptLookup c cs.fromEq with
      | none => rw [hf] at h; cases h
      | some r => rw [hf] at h; simp only [Option.some.injEq] at h; subst h; exact m2 s c r hs hf

/-- Exact HOL `lookup_remove_eq` (`word_copyProofScript.sml:1002-1007`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_remove_eq"]
theorem lookupRemoveEq {n : Nat} {cs : CopyState} : sptLookup n (removeEq cs n).toEq = none :=
  removeEq_self_none cs n

/-- Exact HOL `lookup_eq_set_store_eq` (`word_copyProofScript.sml:1009-1019`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_store_eq"]
theorem lookupEqSetStoreEq {cs : CopyState} {x y : Nat} {s : WordStoreHOL} :
    cpStateInv cs ∧ isAllocVar x = true → lookupEq (setStoreEq cs s x) y = lookupEq cs y := by
  rintro ⟨⟨h1, _, _, _⟩, hx⟩
  rw [setStoreEq_eq, if_pos hx]
  cases hcl : liveClass cs x with
  | some c => rfl
  | none =>
      have hxe : lookupEq cs x = x := by
        unfold liveClass at hcl
        unfold lookupEq
        cases hl : sptLookup x cs.toEq with
        | none => rfl
        | some c =>
            rw [hl] at hcl
            simp only at hcl
            split at hcl
            · rename_i hn; simp [hn]
            · cases hcl
      unfold lookupEq
      dsimp only
      by_cases hyx : y = x
      · subst hyx
        rw [sptLookupInsert, if_pos rfl]
        dsimp only
        rw [sptLookupInsert, if_pos rfl]
        exact hxe.symm
      · rw [sptLookupInsert, if_neg hyx]
        cases hl : sptLookup y cs.toEq with
        | none => rfl
        | some c =>
            have := h1 y c hl
            dsimp only
            rw [sptLookupInsert, if_neg (by omega)]

/-- `List.lookup` of a consed entry at another key (Flapjack infrastructure). -/
theorem listLookupConsNe {α β : Type} [DecidableEq α] {a b : α} {v : β} {l : List (α × β)}
    (h : b ≠ a) : ((a, v) :: l).lookup b = l.lookup b := by
  simp [List.lookup, show (b == a) = false from by simpa using h]

/-- Exact HOL `lookup_store_eq_set_store_eq_1` (`word_copyProofScript.sml:1021-1031`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_set_store_eq_1"]
theorem lookupStoreEqSetStoreEq1 {cs : CopyState} {x y : Nat} {s : WordStoreHOL} :
    cpStateInv cs ∧ isAllocVar x = true ∧ lookupStoreEq (setStoreEq cs s x) s = some y →
      lookupEq cs x = lookupEq cs y := by
  rintro ⟨⟨_, _, _, h4⟩, hx, h⟩
  rw [setStoreEq_eq, if_pos hx] at h
  cases hcl : liveClass cs x with
  | none =>
      rw [hcl] at h
      simp [lookupStoreEq, List.lookup, sptLookupInsert] at h
      rw [h]
  | some c =>
      obtain ⟨hxc, hfrom⟩ := liveClass_some.mp hcl
      rw [hcl] at h
      simp only [lookupStoreEq, List.lookup, beq_self_eq_true] at h
      cases hr : sptLookup c cs.fromEq with
      | none => exact absurd hr hfrom
      | some r =>
          rw [hr] at h; simp only [Option.some.injEq] at h; subst h
          rw [lookupEqI cs r x (Or.inr ⟨c, hxc, hr⟩), lookupEqI cs r r (Or.inr ⟨c, h4 c r hr, hr⟩)]

/-- Exact HOL `lookup_store_eq_set_store_eq_2` (`word_copyProofScript.sml:1033-1044`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_set_store_eq_2"]
theorem lookupStoreEqSetStoreEq2 {cs : CopyState} {x y : Nat} {s t : WordStoreHOL} :
    cpStateInv cs ∧ isAllocVar x = true ∧ s ≠ t ∧ lookupStoreEq (setStoreEq cs s x) t = some y →
      lookupStoreEq cs t = some y := by
  rintro ⟨⟨_, _, h3, _⟩, hx, hst, h⟩
  rw [setStoreEq_eq, if_pos hx] at h
  cases hcl : liveClass cs x with
  | none =>
      rw [hcl] at h
      unfold lookupStoreEq at h ⊢
      dsimp only at h
      rw [listLookupConsNe (Ne.symm hst)] at h
      cases hs : cs.storeToEq.lookup t with
      | none => rw [hs] at h; cases h
      | some c =>
          rw [hs] at h
          have := h3 t c hs
          simpa [sptLookupInsert, show c ≠ cs.next by omega] using h
  | some c =>
      rw [hcl] at h
      unfold lookupStoreEq at h ⊢
      dsimp only at h
      rw [listLookupConsNe (Ne.symm hst)] at h
      exact h

/-- Exact HOL `set_store_eq_model_set_store` (`word_copyProofScript.sml:1046-1069`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_store_eq_model_set_store"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setStoreEqModelSetStore {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {n : Nat} {w : WordLocW width} {s : WordStoreHOL} :
    cpStateInv cs ∧ cpStateModels cs st ∧ WordSemStateFiniteExact.getVar n st = some w →
      cpStateModels (setStoreEq cs s n) (WordSemStateFiniteExact.setStore s w st) := by
  rintro ⟨hinv, hm, hn⟩
  by_cases hx : isAllocVar n = true
  · obtain ⟨d1, d2⟩ := cpStateModelsD ⟨hinv, hm⟩
    have hl : ∀ y, lookupEq (setStoreEq cs s n) y = lookupEq cs y := fun y =>
      lookupEqSetStoreEq ⟨hinv, hx⟩
    refine cpStateModelsI ⟨setStoreEqInv hinv, fun x y hxy => ?_, fun x y hxy => ?_⟩
    · rw [hl, hl] at hxy; exact d1 x y hxy
    · show (st.store.updateEq (s, w)).lookup x = sptLookup y st.locals
      simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL]
      split
      · rename_i hxs; subst hxs
        have e := lookupStoreEqSetStoreEq1 ⟨hinv, hx, hxy⟩
        rw [hl, lookupEqIdempotent hinv] at e
        rw [← d1 n y e]; exact hn.symm
      · rename_i hxs
        rw [hl] at hxy
        exact d2 x y (lookupStoreEqSetStoreEq2 ⟨hinv, hx, Ne.symm hxs, hl y ▸ hxy⟩)
  · rw [setStoreEq_eq, if_neg hx]; exact emptyEqModel

/-- Exact HOL `lookup_eq_remove_t_same` (`word_copyProofScript.sml:1071-1075`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_remove_t_same"]
theorem lookupEqRemoveTSame {cs : CopyState} {t : Nat} : lookupEq (removeEq cs t) t = t := by
  unfold lookupEq; rw [removeEq_self_none]

/-- Exact HOL `lookup_store_eq_set_store_eq_same` (`word_copyProofScript.sml:1077-1083`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_set_store_eq_same"]
theorem lookupStoreEqSetStoreEqSame {cs : CopyState} {x : Nat} {s : WordStoreHOL} :
    sptLookup x cs.toEq = none ∧ isAllocVar x = true →
      lookupStoreEq (setStoreEq cs s x) s = some x := by
  rintro ⟨hx, ha⟩
  rw [setStoreEq_eq, if_pos ha]
  have : liveClass cs x = none := by simp [liveClass, hx]
  rw [this]
  simp [lookupStoreEq, List.lookup, sptLookupInsert]

/-- Exact HOL `set_store_eq_model_set_var` (`word_copyProofScript.sml:1085-1124`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_store_eq_model_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setStoreEqModelSetVar {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {n : Nat} {w : WordLocW width} {s : WordStoreHOL} :
    cpStateInv cs ∧ cpStateModels cs st ∧ lookupStoreEq cs s = none ∧
      WordSemStateFiniteExact.getStore s st = some w →
    cpStateModels (setStoreEq (removeEq cs n) s n) (WordSemStateFiniteExact.setVar n w st) := by
  rintro ⟨hinv, hm, _, hw⟩
  by_cases hx : isAllocVar n = true
  · have hinv0 := removeEqInv cs n hinv
    have hm0 : cpStateModels (removeEq cs n) (WordSemStateFiniteExact.setVar n w st) :=
      removeEqModelSetVar ⟨hinv, hm⟩
    obtain ⟨d1, d2⟩ := cpStateModelsD ⟨hinv0, hm0⟩
    have hl : ∀ y, lookupEq (setStoreEq (removeEq cs n) s n) y = lookupEq (removeEq cs n) y :=
      fun y => lookupEqSetStoreEq ⟨hinv0, hx⟩
    refine cpStateModelsI ⟨setStoreEqInv hinv0, fun x y hxy => ?_, fun x y hxy => ?_⟩
    · rw [hl, hl] at hxy; exact d1 x y hxy
    · rw [hl] at hxy
      by_cases hxs : x = s
      · subst hxs
        rw [lookupStoreEqSetStoreEqSame ⟨removeEq_self_none cs n, hx⟩] at hxy
        have hyn : y = n := lookupEqRemoveEqT ⟨hinv, (Option.some.inj hxy).symm⟩
        subst hyn
        show st.store.lookup x = sptLookup y (sptInsert y w st.locals)
        rw [sptLookupInsert, if_pos rfl]; exact hw
      · exact d2 x y (lookupStoreEqSetStoreEq2 ⟨hinv0, hx, Ne.symm hxs, (hl y).symm ▸ hxy⟩)
  · rw [setStoreEq_eq, if_neg hx]; exact emptyEqModel

/-- Exact HOL `evaluate_Loop_body_cong_err` (`word_copyProofScript.sml:1129-1156`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "evaluate_Loop_body_cong_err"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateLoopBodyCongErr {width : Nat} [NeZero width] {C F : Type} :
    ∀ (s : WordSemStateFiniteExact width C F) (names : WordLangNumSetHOL)
      (c c' : WordLangProgHOL (BitVec width)) (exitNames : WordLangNumSetHOL)
      (res : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      (∀ (v : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
          (s' : WordSemStateFiniteExact width C F),
          Flapjack.WordSemStateFiniteExact.evaluate c v = (res, s') ∧ res ≠ some .error →
          Flapjack.WordSemStateFiniteExact.evaluate c' v = (res, s')) ∧
        Flapjack.WordSemStateFiniteExact.evaluate (.loop names c exitNames) s = (res, s') ∧
        res ≠ some .error →
      Flapjack.WordSemStateFiniteExact.evaluate (.loop names c' exitNames) s = (res, s') :=
  fun s names c c' exitNames res s' ⟨hb, he, hne⟩ =>
    WordUnreach.evaluateLoopBodyEq c c' names exitNames hb s res s' ⟨he, hne⟩

end Flapjack.Compiler.Backend.WordCopy
