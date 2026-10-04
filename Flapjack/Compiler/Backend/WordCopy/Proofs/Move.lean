import Flapjack.Compiler.Backend.WordCopy.Proofs.Models
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

/-!
# word_copyProof: `copy_prop_move` and the invariant through `copy_prop_prog`

Ports of `cakeml/compiler/backend/proofs/word_copyProofScript.sml` lines 470-756: the model
after a single `set_eq` move, `lookup_eq` idempotence and its `get_var`/`word_exp`
consequences, the evaluation of `copy_prop_move`'s rewritten `Move`, and preservation of
`CPstate_inv` by `copy_prop_move`, `copy_prop_inst` and `copy_prop_prog`. HOL `alist_insert`
is the untagged library rendering `LoopSemStateFiniteExact.sptAlistInsert`.
-/

namespace Flapjack.Compiler.Backend.WordCopy

open Flapjack

namespace WordCopyMoveWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordCopyMoveWitnesses

/-- After `remove_eq cs t`, `t` has no class (Flapjack infrastructure). -/
theorem removeEq_self_none (cs : CopyState) (t : Nat) :
    sptLookup t (removeEq cs t).toEq = none := by
  unfold removeEq
  cases h : sptLookup t cs.toEq with
  | none => exact h
  | some _ => rfl

/-- Exact HOL `copy_prop_move_model_aux` (`word_copyProofScript.sml:470-526`). -/
theorem copyPropMoveModelAux {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {t s : Nat} {sval : WordLocW width} :
    cpStateInv cs ∧ cpStateModels cs st ∧ bothAllocVars (t, s) ∧
      sptLookup s st.locals = some sval →
    cpStateModels (setEq (removeEq cs t) t s)
      { st with locals := sptInsert t sval st.locals } := by
  rintro ⟨hinv, hm, hb, hs⟩
  have hinv0 := removeEqInv cs t hinv
  have ht := removeEq_self_none cs t
  have hm0 : cpStateModels (removeEq cs t) st := removeEqModel hm
  obtain ⟨d1, d2⟩ := cpStateModelsD ⟨hinv0, hm0⟩
  have hinv' := setEqInv (s := s) ⟨hinv0, ht⟩
  -- the value of any variable in the class of `t` is `sval`
  have hT : ∀ x, lookupEq (setEq (removeEq cs t) t s) x = t →
      sptLookup x (sptInsert t sval st.locals) = some sval := by
    intro x hx
    rcases (lookupEqSetEqD hinv0 ht hx).1 rfl with rfl | hcls
    · simp [sptLookupInsert]
    · by_cases hxt : x = t
      · subst hxt; simp [sptLookupInsert]
      · rw [sptLookupInsert, if_neg hxt, d1 x s hcls, hs]
  have hN : ∀ x, lookupEq (setEq (removeEq cs t) t s) x ≠ t →
      x ≠ t ∧ lookupEq (setEq (removeEq cs t) t s) x = lookupEq (removeEq cs t) x := by
    intro x hx
    refine ⟨?_, (lookupEqSetEqD hinv0 ht rfl).2 hx⟩
    rintro rfl; exact hx (lookupEqSetEqT ⟨hinv0, hb⟩)
  refine cpStateModelsI ⟨hinv', fun x y hxy => ?_, fun x y hxy => ?_⟩
  · by_cases hr : lookupEq (setEq (removeEq cs t) t s) x = t
    · rw [hT x hr, hT y (hxy ▸ hr)]
    · obtain ⟨hxt, hx⟩ := hN x hr
      obtain ⟨hyt, hy⟩ := hN y (hxy ▸ hr)
      show sptLookup x (sptInsert t sval st.locals) = sptLookup y (sptInsert t sval st.locals)
      rw [sptLookupInsert, if_neg hxt, sptLookupInsert, if_neg hyt]
      exact d1 x y (hx ▸ hy ▸ hxy)
  · obtain ⟨e1, e2⟩ := lookupStoreEqSetEqD hinv0 ht hxy
    show st.store.lookup x = sptLookup y (sptInsert t sval st.locals)
    by_cases hr : lookupEq (setEq (removeEq cs t) t s) y = t
    · rw [hT y hr, d2 x s (e1 hr), hs]
    · obtain ⟨hyt, hy⟩ := hN y hr
      rw [sptLookupInsert, if_neg hyt]
      exact d2 x y (hy ▸ e2 hr)

/-- Exact HOL `set_eq_remove_eq_models` (`word_copyProofScript.sml:528-540`). -/
theorem setEqRemoveEqModels {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {t s : Nat} {sval : WordLocW width} :
    cpStateInv cs ∧ cpStateModels cs st ∧ sptLookup s st.locals = some sval →
    cpStateModels (setEq (removeEq cs t) t s)
      { st with locals := sptInsert t sval st.locals } := by
  rintro ⟨hinv, hm, hs⟩
  by_cases hb : bothAllocVars (t, s)
  · exact copyPropMoveModelAux ⟨hinv, hm, hb, hs⟩
  · rw [setEq_eq, if_neg (show ¬(isAllocVar t = true ∧ isAllocVar s = true) from hb)]
    exact removeEqModelInsert hinv hm

/-- Exact HOL `lookup_eq_idempotent` (`word_copyProofScript.sml:542-550`). -/
theorem lookupEqIdempotent {cs : CopyState} {x : Nat} :
    cpStateInv cs → lookupEq cs (lookupEq cs x) = lookupEq cs x := by
  intro ⟨_, _, _, h4⟩
  rcases lookupEq_cases cs x with ⟨hx, _⟩ | ⟨c, r, _, hr, hx⟩
  · rw [hx, hx]
  · rw [hx]; exact lookupEqI cs r r (Or.inr ⟨c, h4 c r hr, hr⟩)

/-- Exact HOL `CPstate_modelsD_get_var` (`word_copyProofScript.sml:552-561`). -/
theorem cpStateModelsDGetVar {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {x : Nat} :
    cpStateInv cs ∧ cpStateModels cs st →
      WordSemStateFiniteExact.getVar (lookupEq cs x) st = WordSemStateFiniteExact.getVar x st :=
  fun ⟨_, hm⟩ => cpStateModel hm

/-- Exact HOL `CPstate_modelsD_get_vars` (`word_copyProofScript.sml:563-571`). -/
theorem cpStateModelsDGetVars {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {xs : List Nat} :
    cpStateInv cs ∧ cpStateModels cs st →
      WordSemStateFiniteExact.getVars (xs.map (lookupEq cs)) st =
        WordSemStateFiniteExact.getVars xs st := by
  intro h
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, WordSemStateFiniteExact.getVars, cpStateModelsDGetVar h, ih]

/-- Exact HOL `CPstate_modelsD_get_var_imm` (`word_copyProofScript.sml:573-580`). -/
theorem cpStateModelsDGetVarImm {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {x : WordRegImm (BitVec width)} :
    cpStateInv cs ∧ cpStateModels cs st →
      WordSemStateFiniteExact.getVarImm (lookupEqImm cs x) st =
        WordSemStateFiniteExact.getVarImm x st := by
  intro h
  cases x with
  | imm w => rfl
  | reg n => exact cpStateModelsDGetVar h

/-- Exact HOL `CPstate_modelsD_Var` (`word_copyProofScript.sml:582-589`). -/
theorem cpStateModelsDVar {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {x : Nat} :
    cpStateInv cs ∧ cpStateModels cs st →
      WordSemStateFiniteExact.wordExp st (.var (lookupEq cs x)) =
        WordSemStateFiniteExact.wordExp st (.var x) := by
  intro h
  simp only [WordSemStateFiniteExact.wordExp]
  exact cpStateModelsDGetVar h

/-- Exact HOL `CPstate_modelsD_lookup_eq_imm` (`word_copyProofScript.sml:591-600`). -/
theorem cpStateModelsDLookupEqImm {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {x : WordRegImm (BitVec width)} :
    cpStateInv cs → cpStateModels cs st →
      WordSemStateFiniteExact.wordExp st
          (match lookupEqImm cs x with | .reg r => .var r | .imm w => .const w) =
        WordSemStateFiniteExact.wordExp st (match x with | .reg r => .var r | .imm w => .const w) := by
  intro hinv hm
  cases x with
  | imm w => rfl
  | reg n => exact cpStateModelsDVar ⟨hinv, hm⟩

/-- Exact HOL `MAP_get_var_eqD` (`word_copyProofScript.sml:602-613`). -/
theorem mapGetVarEqD {width : Nat} [NeZero width] {C F : Type}
    {st : WordSemStateFiniteExact width C F} {xx yy : List Nat} :
    xx.map (fun x => WordSemStateFiniteExact.getVar x st) =
        yy.map (fun x => WordSemStateFiniteExact.getVar x st) →
      WordSemStateFiniteExact.getVars xx st = WordSemStateFiniteExact.getVars yy st := by
  induction xx generalizing yy with
  | nil => intro h; cases yy with | nil => rfl | cons _ _ => cases h
  | cons x xx ih =>
      intro h
      cases yy with
      | nil => cases h
      | cons y yy =>
          simp only [List.map_cons, List.cons.injEq] at h
          simp only [WordSemStateFiniteExact.getVars, h.1, ih h.2]

/-- The rewritten moves of `copy_prop_move` (Flapjack infrastructure, from
`copy_prop_move_def`). -/
theorem copyPropMove_fst (moves : List (Nat × Nat)) (cs : CopyState) :
    (copyPropMove moves cs).1 = moves.map (fun (x, y) => (x, lookupEq cs y)) := by
  induction moves with
  | nil => rfl
  | cons p moves ih =>
      obtain ⟨x, y⟩ := p
      simp only [copyPropMove, List.map_cons]
      rw [← ih]

/-- Exact HOL `copy_prop_move_eval_aux1` (`word_copyProofScript.sml:615-633`). -/
theorem copyPropMoveEvalAux1 {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st : WordSemStateFiniteExact width C F} {moves : List (Nat × Nat)} :
    cpStateInv cs → cpStateModels cs st → ∀ (moves' : List (Nat × Nat)) (cs' : CopyState),
      copyPropMove moves cs = (moves', cs') →
      (moves'.map Prod.snd).map (fun x => WordSemStateFiniteExact.getVar x st) =
        (moves.map Prod.snd).map (fun x => WordSemStateFiniteExact.getVar x st) := by
  intro hinv hm moves' cs' h
  have : moves' = moves.map (fun (x, y) => (x, lookupEq cs y)) := by
    rw [← copyPropMove_fst, h]
  subst this
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  exact cpStateModelsDGetVar ⟨hinv, hm⟩

/-- Exact HOL `copy_prop_move_get_vars` (`word_copyProofScript.sml:635-644`). -/
theorem copyPropMoveGetVars {width : Nat} [NeZero width] {C F : Type} {cs cs' : CopyState}
    {st : WordSemStateFiniteExact width C F} {moves moves' : List (Nat × Nat)} :
    cpStateInv cs → cpStateModels cs st → copyPropMove moves cs = (moves', cs') →
      WordSemStateFiniteExact.getVars (moves'.map Prod.snd) st =
        WordSemStateFiniteExact.getVars (moves.map Prod.snd) st :=
  fun hinv hm h => mapGetVarEqD (copyPropMoveEvalAux1 hinv hm moves' cs' h)

/-- Exact HOL `copy_prop_move_eval_aux2` (`word_copyProofScript.sml:646-652`). -/
theorem copyPropMoveEvalAux2 {width : Nat} [NeZero width] {C F : Type}
    {st : WordSemStateFiniteExact width C F} {moves1 moves2 : List (Nat × Nat)} {pri : Nat} :
    moves1.map Prod.fst = moves2.map Prod.fst →
      WordSemStateFiniteExact.getVars (moves1.map Prod.snd) st =
        WordSemStateFiniteExact.getVars (moves2.map Prod.snd) st →
      Flapjack.WordSemStateFiniteExact.evaluate (.move pri moves1) st =
        Flapjack.WordSemStateFiniteExact.evaluate (.move pri moves2) st := by
  intro h1 h2
  rw [(WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.1 st pri moves1,
    (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.1 st pri moves2, h1, h2]

/-- Exact HOL `copy_prop_move_eval_aux3` (`word_copyProofScript.sml:654-665`). -/
theorem copyPropMoveEvalAux3 {moves : List (Nat × Nat)} {cs : CopyState} :
    ∀ (moves' : List (Nat × Nat)) (cs' : CopyState),
      copyPropMove moves cs = (moves', cs') → moves'.map Prod.fst = moves.map Prod.fst := by
  intro moves' cs' h
  have : moves' = moves.map (fun (x, y) => (x, lookupEq cs y)) := by
    rw [← copyPropMove_fst, h]
  subst this
  simp only [List.map_map]
  rfl

/-- Exact HOL `copy_prop_move_eval` (`word_copyProofScript.sml:667-679`). -/
theorem copyPropMoveEval {width : Nat} [NeZero width] {C F : Type} {cs cs' : CopyState}
    {st st' : WordSemStateFiniteExact width C F} {moves moves' : List (Nat × Nat)} {pri : Nat}
    {err : Option (WordSemResult width)} :
    cpStateInv cs → cpStateModels cs st → copyPropMove moves cs = (moves', cs') →
      Flapjack.WordSemStateFiniteExact.evaluate (.move pri moves) st = (err, st') →
        Flapjack.WordSemStateFiniteExact.evaluate (.move pri moves') st = (err, st') := by
  intro hinv hm hmv he
  rw [copyPropMoveEvalAux2 (copyPropMoveEvalAux3 moves' cs' hmv)
    (copyPropMoveGetVars hinv hm hmv)]
  exact he

/-- Exact HOL `lookup_alist_insert_same` (`word_copyProofScript.sml:681-687`; the second
declaration of that name at 741 is commented out in HOL). -/
theorem lookupAlistInsertSame {α : Type} {s : Nat} {tt : List Nat} {values : List α}
    {locals : Spt α} :
    s ∉ tt →
      sptLookup s (LoopSemStateFiniteExact.sptAlistInsert tt values locals) = sptLookup s locals := by
  induction tt generalizing values with
  | nil => intro _; rfl
  | cons t tt ih =>
      intro h
      cases values with
      | nil => rfl
      | cons v vs =>
          simp only [List.mem_cons, not_or] at h
          simp only [LoopSemStateFiniteExact.sptAlistInsert]
          rw [sptLookupInsert, if_neg h.1]
          exact ih h.2

/-- `copy_prop_move` preserves `CPstate_inv` (Flapjack infrastructure, the projection form
of `copy_prop_move_inv`). -/
theorem copyPropMove_inv2 : ∀ (moves : List (Nat × Nat)) (cs : CopyState),
    cpStateInv cs → cpStateInv (copyPropMove moves cs).2
  | [], _, h => h
  | (x, _y) :: moves, cs, h =>
      setEqInv ⟨removeEqInv _ x (copyPropMove_inv2 moves cs h), removeEq_self_none _ x⟩

/-- Exact HOL `copy_prop_move_inv` (`word_copyProofScript.sml:689-703`). -/
theorem copyPropMoveInv {cs cs' : CopyState} {moves moves' : List (Nat × Nat)} :
    cpStateInv cs → copyPropMove moves cs = (moves', cs') → cpStateInv cs' := by
  intro h hmv
  have := copyPropMove_inv2 moves cs h
  rw [hmv] at this
  exact this

/-- `copy_prop_inst` preserves `CPstate_inv` (Flapjack infrastructure, the projection form
of `copy_prop_inst_inv`). -/
theorem copyPropInst_inv2 {width : Nat} [NeZero width] (ins : WordLangInst (BitVec width))
    (cs : CopyState) (h : cpStateInv cs) : cpStateInv (copyPropInst ins cs).2 := by
  rcases ins with _ | ⟨r, w⟩ | ⟨a⟩ | ⟨m, r, ⟨a, w⟩⟩
  · exact h
  · exact removeEqInv _ _ h
  · cases a <;> first | exact removeEqInv _ _ h | exact removeEqsInv _ _ h
  · cases m <;> first | exact h | exact removeEqInv _ _ h

/-- Exact HOL `copy_prop_inst_inv` (`word_copyProofScript.sml:705-716`). -/
theorem copyPropInstInv {width : Nat} [NeZero width] {cs cs' : CopyState}
    {ins : WordLangInst (BitVec width)} {prog' : WordLangProgHOL (BitVec width)} :
    cpStateInv cs → copyPropInst ins cs = (prog', cs') → cpStateInv cs' := by
  intro h hi
  have := copyPropInst_inv2 ins cs h
  rw [hi] at this
  exact this

/-- `copy_prop_prog` preserves `CPstate_inv` (Flapjack infrastructure, the projection form
of `copy_prop_prog_inv`). -/
theorem copyPropProg_inv2 {width : Nat} [NeZero width] :
    ∀ (prog : WordLangProgHOL (BitVec width)) (cs : CopyState),
      cpStateInv cs → cpStateInv (copyPropProg prog cs).2
  | .move pri xs, cs, h => by
      simp only [copyPropProg]
      split
      · exact copyPropMove_inv2 xs cs h
      · exact emptyEqInv
  | .inst i, cs, h => copyPropInst_inv2 i cs h
  | .mustTerminate p, cs, h => copyPropProg_inv2 p cs h
  | .seq p1 p2, cs, h => copyPropProg_inv2 p2 _ (copyPropProg_inv2 p1 cs h)
  | .ite _ _ _ p1 p2, cs, h => mergeEqsInv ⟨copyPropProg_inv2 p1 cs h, copyPropProg_inv2 p2 cs h⟩
  | .set name e, cs, h => by
      cases e <;> first | exact setStoreEqInv h | exact emptyEqInv
  | .get n name, cs, h => by
      simp only [copyPropProg]
      split
      · exact setStoreEqInv (removeEqInv cs n h)
      · split
        · exact copyPropMove_inv2 _ cs h
        · exact h
  | .skip, _, h => h
  | .return _ _, _, h => h
  | .raise _, _, h => h
  | .opCurrHeap _ _ _, cs, h => removeEqInv cs _ h
  | .tick, _, h => h
  | .call _ _ _ _, _, _ => emptyEqInv
  | .alloc _ _, _, _ => emptyEqInv
  | .storeConsts _ _ _ _ _, cs, h => removeEqsInv _ cs h
  | .locValue _ _, cs, h => removeEqInv cs _ h
  | .install _ _ _ _ _, _, _ => emptyEqInv
  | .codeBufferWrite _ _, _, h => h
  | .dataBufferWrite _ _, _, h => h
  | .ffi _ _ _ _ _ _, _, _ => emptyEqInv
  | .shareInst _ _ _, cs, h => removeEqInv cs _ h
  | .loop _ _ _, _, _ => emptyEqInv
  | .break _, _, h => h
  | .continue _, _, h => h
  | .assign _ _, _, _ => emptyEqInv
  | .store _ _, _, _ => emptyEqInv

/-- Exact HOL `copy_prop_prog_inv` (`word_copyProofScript.sml:718-739`). -/
theorem copyPropProgInv {width : Nat} [NeZero width] {cs cs' : CopyState}
    {prog prog' : WordLangProgHOL (BitVec width)} :
    cpStateInv cs ∧ copyPropProg prog cs = (prog', cs') → cpStateInv cs' := by
  rintro ⟨h, hp⟩
  have := copyPropProg_inv2 prog cs h
  rw [hp] at this
  exact this

/-- Exact HOL `empty_eq_model` (`word_copyProofScript.sml:752-756`). -/
theorem emptyEqModel {width : Nat} [NeZero width] {C F : Type}
    {st : WordSemStateFiniteExact width C F} : cpStateModels emptyEq st :=
  emptyEqModels st

end Flapjack.Compiler.Backend.WordCopy
