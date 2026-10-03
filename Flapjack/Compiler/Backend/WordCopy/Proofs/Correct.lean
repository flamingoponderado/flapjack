import Flapjack.Compiler.Backend.WordCopy.Proofs.Inst
import Flapjack.Misc.Sptree.InsertUnchanged

/-!
# word_copyProof: `copy_prop_correct` and `evaluate_copy_prop`

Ports of the main theorems of `cakeml/compiler/backend/proofs/word_copyProofScript.sml`
(lines 1158-1407): every program case of `copy_prop_correct` (including the resumed `Loop`
case), and the top-level `evaluate_copy_prop`. HOL proves `copy_prop_correct` by structural
induction on the program; the Lean proof recurses structurally on it.
-/

namespace Flapjack.Compiler.Backend.WordCopy

open Flapjack

namespace WordCopyCorrectWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordCopyCorrectWitnesses

section Clauses
variable {width : Nat} [NeZero width] {C F : Type}

local notation "ev" => Flapjack.WordSemStateFiniteExact.evaluate

private abbrev R := WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C) (F := F)

private theorem evSkip' (s : WordSemStateFiniteExact width C F) : ev .skip s = (none, s) :=
  R.1 s
private theorem evStoreConsts (s : WordSemStateFiniteExact width C F) a b c d ws :
    ev (.storeConsts a b c d ws) s =
      match WordSemStateFiniteExact.getVar c s, WordSemStateFiniteExact.getVar d s with
      | some (.word aa), some (.word off) =>
          if ¬ wordSemConstAddresses aa ws s.mdomain = true then (some .error, s)
          else
            let s := { s with memory := wordSemConstWrites aa off ws s.memory }
            let s := WordSemStateFiniteExact.setVar d (.word off)
              (WordSemStateFiniteExact.unsetVar a (WordSemStateFiniteExact.unsetVar b s))
            (none, WordSemStateFiniteExact.setVar c
              (.word (aa + wordSemBytesInWord * BitVec.ofNat width ws.length)) s)
      | _, _ => (some .error, s) :=
  R.2.2.1 ws b a s d c
private theorem evMove' (s : WordSemStateFiniteExact width C F) pri moves :
    ev (.move pri moves) s =
      if (moves.map Prod.fst).Nodup then
        match WordSemStateFiniteExact.getVars (moves.map Prod.snd) s with
        | none => (some .error, s)
        | some vs => (none, WordSemStateFiniteExact.setVars (moves.map Prod.fst) vs s)
      else (some .error, s) :=
  R.2.2.2.1 s pri moves
private theorem evGet (s : WordSemStateFiniteExact width C F) v name :
    ev (.get v name) s =
      match WordSemStateFiniteExact.getStore name s with
      | none => (some .error, s)
      | some x => (none, WordSemStateFiniteExact.setVar v x s) :=
  R.2.2.2.2.2.2.1 v s name
private theorem evSet (s : WordSemStateFiniteExact width C F) v exp :
    ev (.set v exp) s =
      if v = .handler ∨ v = .bitmapBase then (some .error, s)
      else
        match WordSemStateFiniteExact.wordExp s exp with
        | none => (some .error, s)
        | some w => (none, WordSemStateFiniteExact.setStore v w s) :=
  R.2.2.2.2.2.2.2.1 v s exp
private theorem evOpCurrHeap (s : WordSemStateFiniteExact width C F) src dst b :
    ev (.opCurrHeap b dst src) s =
      match WordSemStateFiniteExact.wordExp s (.op b [.var src, .lookup .currHeap]) with
      | none => (some .error, s)
      | some w => (none, WordSemStateFiniteExact.setVar dst w s) :=
  R.2.2.2.2.2.2.2.2.1 src s dst b
private theorem evTick (s : WordSemStateFiniteExact width C F) :
    ev .tick s = if s.clock = 0 then (some .timeOut, WordSemStateFiniteExact.flushState true s)
      else (none, WordSemStateFiniteExact.decClock s) :=
  R.2.2.2.2.2.2.2.2.2.2.1 s
private theorem evMT (s : WordSemStateFiniteExact width C F) p :
    ev (.mustTerminate p) s =
      if s.termdep = 0 then (some .error, s)
      else
        match ev p { s with clock := wordSemMustTerminateLimit width,
                            termdep := s.termdep - 1 } with
        | (res, s1) =>
            match res with
            | some .timeOut => (some .error, s)
            | _ => (res, { s1 with clock := s.clock, termdep := s.termdep }) :=
  R.2.2.2.2.2.2.2.2.2.2.2.1 s p
private theorem evSeq' (s : WordSemStateFiniteExact width C F) c1 c2 :
    ev (.seq c1 c2) s =
      match ev c1 s with
      | (res, s1) =>
          match res with
          | none => ev c2 s1
          | _ => (res, s1) :=
  R.2.2.2.2.2.2.2.2.2.2.2.2.1 s c2 c1
private theorem evReturn (s : WordSemStateFiniteExact width C F) n ms :
    ev (.return n ms) s =
      match WordSemStateFiniteExact.getVar n s, WordSemStateFiniteExact.getVars ms s with
      | some (.loc l1 l2), some ys =>
          (some (.result (.loc l1 l2) ys), WordSemStateFiniteExact.flushState false s)
      | _, _ => (some .error, s) :=
  R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s n ms
private theorem evRaise (s : WordSemStateFiniteExact width C F) n :
    ev (.raise n) s =
      match WordSemStateFiniteExact.getVar n s with
      | none => (some .error, s)
      | some w =>
          match WordSemStateFiniteExact.jumpExc s with
          | none => (some .error, s)
          | some (s, l1, l2) => (some (.exception (.loc l1 l2) w), s) :=
  R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s n
private theorem evIte (s : WordSemStateFiniteExact width C F) ri r1 cmp c2 c1 :
    ev (.ite cmp r1 ri c1 c2) s =
      match WordSemStateFiniteExact.getVar r1 s, WordSemStateFiniteExact.getVarImm ri s with
      | some x, some y =>
          match wordSemWordCmp cmp x y with
          | some true => ev c1 s
          | some false => ev c2 s
          | none => (some .error, s)
      | _, _ => (some .error, s) :=
  R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s ri r1 cmp c2 c1
private theorem evLocValue (s : WordSemStateFiniteExact width C F) r l1 :
    ev (.locValue r l1) s =
      if sptMem l1 s.code then (none, WordSemStateFiniteExact.setVar r (.loc l1 0) s)
      else (some .error, s) :=
  R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s r l1
private theorem evCBW (s : WordSemStateFiniteExact width C F) r2 r1 :
    ev (.codeBufferWrite r1 r2) s =
      match WordSemStateFiniteExact.getVar r1 s, WordSemStateFiniteExact.getVar r2 s with
      | some (.word w1), some (.word w2) =>
          match wordSemBufferWrite s.codeBuffer w1 (w2.setWidth 8) with
          | some newCb => (none, { s with codeBuffer := newCb })
          | none => (some .error, s)
      | _, _ => (some .error, s) :=
  R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s r2 r1
private theorem evDBW (s : WordSemStateFiniteExact width C F) r2 r1 :
    ev (.dataBufferWrite r1 r2) s =
      match WordSemStateFiniteExact.getVar r1 s, WordSemStateFiniteExact.getVar r2 s with
      | some (.word w1), some (.word w2) =>
          match wordSemBufferWrite s.dataBuffer w1 w2 with
          | some newDb => (none, { s with dataBuffer := newDb })
          | none => (some .error, s)
      | _, _ => (some .error, s) :=
  R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s r2 r1
private theorem evShare (s : WordSemStateFiniteExact width C F) v op exp :
    ev (.shareInst op v exp) s =
      match WordSemStateFiniteExact.wordExp s exp with
      | some (.word ad) => WordSemStateFiniteExact.shareInst op v ad s
      | _ => (some .error, s) :=
  R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v s op exp

end Clauses

/-- A successful `share_inst` writes at most the local `v` (Flapjack infrastructure). -/
theorem shareInstModel {width : Nat} [NeZero width] {C F : Type} {cs : CopyState}
    {st st' : WordSemStateFiniteExact width C F} {op : WordMemOp} {v : Nat} {ad : BitVec width}
    (hinv : cpStateInv cs) (hm : cpStateModels cs st)
    (h : WordSemStateFiniteExact.shareInst (rw := width) op v ad st = (none, st')) :
    cpStateModels (removeEq cs v) st' := by
  cases op <;> simp only [WordSemStateFiniteExact.shareInst, WordSemStateFiniteExact.shMemSetVar,
    WordSemStateFiniteExact.shMemStore, WordSemStateFiniteExact.shMemStoreByte,
    WordSemStateFiniteExact.shMemStore16, WordSemStateFiniteExact.shMemStore32] at h
  all_goals
    repeat'
      first
      | (simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h; done)
      | (simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h)
      | split at h
  all_goals
    first
    | exact removeEqModelSetVar ⟨hinv, cpStateModelsSame ⟨hm, rfl, rfl⟩⟩
    | exact removeEqModel (cpStateModelsSame ⟨hm, rfl, rfl⟩)

/-- `(SOME x, s) = (err, st')` contradicts `err = NONE` (Flapjack infrastructure). -/
theorem someNotNone {α β : Type} {x : α} {s st' : β} {err : Option α}
    (he : (some x, s) = (err, st')) (herr : err = none) : False := by
  simp only [Prod.mk.injEq] at he; rw [herr] at he; cases he.1

/-- Exact HOL `copy_prop_correct` (`word_copyProofScript.sml:1158-1393`, with the resumed
`Loop` case at 1379-1389). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "copy_prop_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem copyPropCorrect {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (cs : CopyState)
      (st : WordSemStateFiniteExact width C F) (prog' : WordLangProgHOL (BitVec width))
      (cs' : CopyState) (err : Option (WordSemResult width))
      (st' : WordSemStateFiniteExact width C F),
      cpStateInv cs ∧ cpStateModels cs st ∧ copyPropProg prog cs = (prog', cs') ∧
        err ≠ some .error ∧ Flapjack.WordSemStateFiniteExact.evaluate prog st = (err, st') →
      Flapjack.WordSemStateFiniteExact.evaluate prog' st = (err, st') ∧
        (err = none → cpStateModels cs' st')
  | .skip, cs, st, prog', cs', err, st', ⟨_, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨he, fun _ => ?_⟩
      rw [evSkip'] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact hm
  | .move pri moves, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ =>
      copyPropMoveCorrect ⟨hinv, hm, hp, he⟩
  | .inst i, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ =>
      copyPropInstCorrect ⟨hinv, hm, by simpa only [copyPropProg] using hp, he⟩
  | .assign n e, cs, st, prog', cs', err, st', ⟨_, _, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨he, fun _ => emptyEqModel⟩
  | .get n name, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, hne, he⟩ => by
      have he0 := he
      rw [evGet] at he
      simp only [copyPropProg] at hp
      cases hl : lookupStoreEq cs name with
      | none =>
          rw [hl] at hp
          simp only [Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          refine ⟨he0, fun herr => ?_⟩
          cases hx : WordSemStateFiniteExact.getStore name st with
          | none => rw [hx] at he; exact (someNotNone he herr).elim
          | some x =>
              rw [hx] at he
              simp only [Prod.mk.injEq] at he
              obtain ⟨-, rfl⟩ := he
              exact setStoreEqModelSetVar ⟨hinv, hm, hl, hx⟩
      | some v =>
          rw [hl] at hp
          have hsv := lookupStoreEqSome ⟨hm, hl⟩
          cases hx : WordSemStateFiniteExact.getStore name st with
          | none =>
              rw [hx] at he
              simp only [Prod.mk.injEq] at he
              exact absurd he.1.symm hne
          | some x =>
              rw [hx] at he
              simp only [Prod.mk.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              have hvx : sptLookup v st.locals = some x := by
                rw [← hsv]; exact hx
              simp only at hp
              split at hp
              · simp only [copyPropMove, Prod.mk.injEq] at hp
                obtain ⟨rfl, rfl⟩ := hp
                refine ⟨?_, fun _ => setEqRemoveEqModels ⟨hinv, hm, hvx⟩⟩
                rw [evMove']
                simp only [List.map_cons, List.map_nil, List.nodup_cons, List.not_mem_nil,
                  not_false_eq_true, List.nodup_nil, and_self, if_true,
                  WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
                  cpStateModel hm, hvx]
                rfl
              · rename_i hvn
                have hvn' : v = n := by simpa using hvn
                subst hvn'
                simp only [Prod.mk.injEq] at hp
                obtain ⟨rfl, rfl⟩ := hp
                have hst : WordSemStateFiniteExact.setVar v x st = st := by
                  simp only [WordSemStateFiniteExact.setVar]
                  rw [sptInsertUnchanged _ _ _ hvx]
                rw [hst]
                exact ⟨evSkip' st, fun _ => hm⟩
  | .set name e, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ => by
      cases e with
      | var n =>
          simp only [copyPropProg, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          rw [evSet] at he ⊢
          rw [cpStateModelsDVar ⟨hinv, hm⟩]
          refine ⟨he, fun herr => ?_⟩
          split at he
          · exact (someNotNone he herr).elim
          · cases hx : WordSemStateFiniteExact.wordExp st (.var n) with
            | none => rw [hx] at he; exact (someNotNone he herr).elim
            | some w =>
                rw [hx] at he
                simp only [Prod.mk.injEq] at he
                obtain ⟨-, rfl⟩ := he
                exact setStoreEqModelSetStore ⟨hinv, hm, by
                  simpa only [WordSemStateFiniteExact.wordExp] using hx⟩
      | _ =>
          simp only [copyPropProg, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact ⟨he, fun _ => emptyEqModel⟩
  | .store e n, cs, st, prog', cs', err, st', ⟨_, _, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨he, fun _ => emptyEqModel⟩
  | .mustTerminate p, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, hne, he⟩ => by
      simp only [copyPropProg] at hp
      rcases hq : copyPropProg p cs with ⟨p1', cs1⟩
      rw [hq] at hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [evMT] at he ⊢
      split at he
      · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
      · rename_i hd
        rw [if_neg hd]
        have hm1 : cpStateModels cs
            { st with clock := wordSemMustTerminateLimit width, termdep := st.termdep - 1 } :=
          cpStateModelsSame ⟨hm, rfl, rfl⟩
        rcases hev : Flapjack.WordSemStateFiniteExact.evaluate p
            { st with clock := wordSemMustTerminateLimit width, termdep := st.termdep - 1 } with
          ⟨res, s1⟩
        rw [hev] at he
        dsimp only at he
        have he0 := he
        split at he
        · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨ih1, ih2⟩ := copyPropCorrect p cs _ p1' cs1 res s1 ⟨hinv, hm1, hq, hne, hev⟩
          rw [ih1]
          exact ⟨he0, fun herr => cpStateModelsSame ⟨ih2 herr, rfl, rfl⟩⟩
  | .call ret dest args handler, cs, st, prog', cs', err, st', ⟨_, _, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨he, fun _ => emptyEqModel⟩
  | .seq p1 p2, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, hne, he⟩ => by
      simp only [copyPropProg] at hp
      rcases hq1 : copyPropProg p1 cs with ⟨q1, cs1⟩
      rw [hq1] at hp
      dsimp only at hp
      rcases hq2 : copyPropProg p2 cs1 with ⟨q2, cs2⟩
      rw [hq2] at hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [evSeq'] at he ⊢
      rcases hev : Flapjack.WordSemStateFiniteExact.evaluate p1 st with ⟨res, s1⟩
      rw [hev] at he
      cases res with
      | none =>
          obtain ⟨e1, m1⟩ := copyPropCorrect p1 cs st q1 cs1 none s1 ⟨hinv, hm, hq1, by simp, hev⟩
          rw [e1]
          exact copyPropCorrect p2 cs1 s1 q2 cs2 err st'
            ⟨copyPropProgInv ⟨hinv, hq1⟩, m1 rfl, hq2, hne, he⟩
      | some r =>
          dsimp only at he
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨e1, -⟩ := copyPropCorrect p1 cs st q1 cs1 (some r) s1 ⟨hinv, hm, hq1, hne, hev⟩
          rw [e1]
          exact ⟨rfl, fun h => by cases h⟩
  | .ite cmp r ri p1 p2, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, hne, he⟩ => by
      simp only [copyPropProg] at hp
      rcases hq1 : copyPropProg p1 cs with ⟨q1, cs1⟩
      rcases hq2 : copyPropProg p2 cs with ⟨q2, cs2⟩
      rw [hq1, hq2] at hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [evIte] at he ⊢
      rw [cpStateModelsDGetVar ⟨hinv, hm⟩, cpStateModelsDGetVarImm ⟨hinv, hm⟩]
      cases hx : WordSemStateFiniteExact.getVar r st with
      | none => rw [hx] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
      | some x =>
      cases hy : WordSemStateFiniteExact.getVarImm ri st with
      | none => rw [hx, hy] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
      | some y =>
      rw [hx, hy] at he
      dsimp only at he ⊢
      cases hc : wordSemWordCmp cmp x y with
      | none => rw [hc] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hne
      | some b =>
          rw [hc] at he
          cases b with
          | true =>
              obtain ⟨e1, m1⟩ := copyPropCorrect p1 cs st q1 cs1 err st' ⟨hinv, hm, hq1, hne, he⟩
              exact ⟨e1, fun h => mergeEqsModel1 (m1 h)⟩
          | false =>
              obtain ⟨e2, m2⟩ := copyPropCorrect p2 cs st q2 cs2 err st' ⟨hinv, hm, hq2, hne, he⟩
              exact ⟨e2, fun h => mergeEqsModel2 (m2 h)⟩
  | .loop names c exitNames, cs, st, prog', cs', err, st', ⟨_, _, hp, hne, he⟩ => by
      simp only [copyPropProg] at hp
      rcases hq : copyPropProg c emptyEq with ⟨c', x⟩
      rw [hq] at hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨evaluateLoopBodyCongErr st names c c' exitNames err st'
        ⟨fun v res s' ⟨h1, h2⟩ =>
          (copyPropCorrect c emptyEq v c' x res s' ⟨emptyEqInv, emptyEqModel, hq, h2, h1⟩).1,
          he, hne⟩, fun _ => emptyEqModel⟩
  | .alloc r live, cs, st, prog', cs', err, st', ⟨_, _, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨he, fun _ => emptyEqModel⟩
  | .storeConsts a b c d ws, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨he, fun herr => ?_⟩
      rw [evStoreConsts] at he
      split at he
      · split at he
        · exact (someNotNone he herr).elim
        · simp only [Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          show cpStateModels (removeEq (removeEq (removeEq (removeEq cs a) b) c) d) _
          rw [removeEqComm (x := c) (y := d), removeEqComm (cs := cs) (x := a) (y := b)]
          have i1 := removeEqInv cs b hinv
          have i2 := removeEqInv _ a i1
          have i3 := removeEqInv _ d i2
          exact removeEqModelSetVar ⟨i3, removeEqModelSetVar ⟨i2, removeEqModelUnsetVar i1
            (removeEqModelUnsetVar hinv (cpStateModelsSame ⟨hm, rfl, rfl⟩))⟩⟩
      · exact (someNotNone he herr).elim
  | .raise v, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [evRaise] at he ⊢
      rw [cpStateModelsDGetVar ⟨hinv, hm⟩]
      refine ⟨he, fun herr => ?_⟩
      split at he
      · exact (someNotNone he herr).elim
      · split at he
        · exact (someNotNone he herr).elim
        · exact (someNotNone he herr).elim
  | .return v1 v2, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [evReturn] at he ⊢
      rw [cpStateModelsDGetVar ⟨hinv, hm⟩, cpStateModelsDGetVars ⟨hinv, hm⟩]
      refine ⟨he, fun herr => ?_⟩
      split at he
      · exact (someNotNone he herr).elim
      · exact (someNotNone he herr).elim
  | .break k, cs, st, prog', cs', err, st', ⟨_, _, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨he, fun herr => ?_⟩
      rw [R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at he
      exact (someNotNone he herr).elim
  | .continue k, cs, st, prog', cs', err, st', ⟨_, _, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨he, fun herr => ?_⟩
      rw [R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at he
      exact (someNotNone he herr).elim
  | .tick, cs, st, prog', cs', err, st', ⟨_, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨he, fun herr => ?_⟩
      rw [evTick] at he
      split at he
      · exact (someNotNone he herr).elim
      · simp only [Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he
        exact cpStateModelsSame ⟨hm, rfl, rfl⟩
  | .opCurrHeap b dst src, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [evOpCurrHeap] at he ⊢
      rw [wordExpCongOp (aa := [.var src, .lookup .currHeap]) ?_]
      · refine ⟨he, fun herr => ?_⟩
        split at he
        · exact (someNotNone he herr).elim
        · simp only [Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          exact removeEqModelSetVar ⟨hinv, hm⟩
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
        split
        · rfl
        · exact cpStateModelsDVar ⟨hinv, hm⟩
  | .locValue r l1, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨he, fun herr => ?_⟩
      rw [evLocValue] at he
      split at he
      · simp only [Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he
        exact removeEqModelSetVar ⟨hinv, hm⟩
      · exact (someNotNone he herr).elim
  | .install r1 r2 r3 r4 live, cs, st, prog', cs', err, st', ⟨_, _, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨he, fun _ => emptyEqModel⟩
  | .codeBufferWrite r1 r2, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [evCBW] at he ⊢
      rw [cpStateModelsDGetVar ⟨hinv, hm⟩, cpStateModelsDGetVar ⟨hinv, hm⟩]
      refine ⟨he, fun herr => ?_⟩
      split at he
      · split at he
        · simp only [Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          exact cpStateModelsSame ⟨hm, rfl, rfl⟩
        · exact (someNotNone he herr).elim
      · exact (someNotNone he herr).elim
  | .dataBufferWrite r1 r2, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [evDBW] at he ⊢
      rw [cpStateModelsDGetVar ⟨hinv, hm⟩, cpStateModelsDGetVar ⟨hinv, hm⟩]
      refine ⟨he, fun herr => ?_⟩
      split at he
      · split at he
        · simp only [Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          exact cpStateModelsSame ⟨hm, rfl, rfl⟩
        · exact (someNotNone he herr).elim
      · exact (someNotNone he herr).elim
  | .ffi i r1 r2 r3 r4 live, cs, st, prog', cs', err, st', ⟨_, _, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨he, fun _ => emptyEqModel⟩
  | .shareInst op v exp, cs, st, prog', cs', err, st', ⟨hinv, hm, hp, _, he⟩ => by
      simp only [copyPropProg, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [evShare] at he ⊢
      rw [cpStateModelsDCopyPropShare hinv hm]
      refine ⟨he, fun herr => ?_⟩
      split at he
      · subst herr; exact shareInstModel hinv hm he
      · exact (someNotNone he herr).elim

/-- Exact HOL `evaluate_copy_prop` (`word_copyProofScript.sml:1396-1404`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "evaluate_copy_prop"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCopyProp {width : Nat} [NeZero width] {C F : Type}
    {e : WordLangProgHOL (BitVec width)} {s : WordSemStateFiniteExact width C F} :
    (Flapjack.WordSemStateFiniteExact.evaluate e s).1 ≠ some .error →
      Flapjack.WordSemStateFiniteExact.evaluate (copyProp e) s =
        Flapjack.WordSemStateFiniteExact.evaluate e s := by
  intro hne
  rcases hev : Flapjack.WordSemStateFiniteExact.evaluate e s with ⟨r, t⟩
  rw [hev] at hne
  rcases hq : copyPropProg e emptyEq with ⟨p', cs'⟩
  have : copyProp e = p' := by simp only [copyProp, hq]
  rw [this]
  exact (copyPropCorrect e emptyEq s p' cs' r t ⟨emptyEqInv, emptyEqModel, hq, hne, hev⟩).1

end Flapjack.Compiler.Backend.WordCopy
