import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Alloc
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Loop

/-!
# `evaluate_stack_swap` `Call` case

The `Call` case of `wordPropsScript.sml:2316-2363` `evaluate_stack_swap`
(proof `wordPropsScript.sml:2879-3233`), with the induction hypotheses of HOL
`evaluate_ind`. The untagged helpers are Flapjack proof infrastructure for the
tagged case: the pushed frame and the call environment do not depend on the
stack below the frame (`s_val_eq_stack_size`, `s_val_eq_length`), and popping
the frame restores the caller's handler.
-/

namespace Flapjack

namespace WordSemStackEq

open WordSemStateFiniteExact

section CallCase

variable {width : Nat} [NeZero width] {C F : Type}

/-- `LASTN n` ignores elements beyond the last `n`. -/
theorem lastN_cons {α : Type} (n : Nat) (x : α) (l : List α) (h : n ≤ l.length) :
    wordSemLastN n (x :: l) = wordSemLastN n l := by
  unfold wordSemLastN
  rw [List.reverse_cons, List.take_append_of_le_length (by simpa using h)]

private theorem stackSizeConsCall (fr : WordSemStackFrame width)
    (rest : List (WordSemStackFrame width)) :
    wordSemStackSize (fr :: rest) =
      wordSemOptionAdd (wordSemStackSizeFrame fr) (wordSemStackSize rest) := rfl

/-- The call environment over a value-equal stack. -/
theorem callEnv_withStack (a : List (WordLocW width)) (ss : Option Nat)
    (t : WordSemStateFiniteExact width C F) (ys : List (WordSemStackFrame width))
    (h : sValEq t.stack ys) :
    WordSemStateFiniteExact.callEnv a ss { t with stack := ys } =
      { WordSemStateFiniteExact.callEnv a ss t with stack := ys } := by
  simp only [WordSemStateFiniteExact.callEnv]
  rw [sValEqStackSize _ _ h]

/-- Pushing a frame over a value-equal stack: only the stack below the new frame
changes (the handler of a pushed handler frame is the stack length). -/
theorem pushEnv_withStack (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (t : WordSemStateFiniteExact width C F) (xs : List (WordSemStackFrame width))
    (hv : sValEq t.stack xs) :
    ∃ fr, (pushEnv envs h t).stack = fr :: t.stack ∧
      pushEnv envs h { t with stack := xs } = { pushEnv envs h t with stack := fr :: xs } := by
  rcases h with _ | ⟨_, _, _, _⟩
  · refine ⟨_, rfl, ?_⟩
    simp only [pushEnv]
    rw [stackSizeConsCall, stackSizeConsCall, sValEqStackSize _ _ hv]
    rfl
  · refine ⟨_, rfl, ?_⟩
    simp only [pushEnv]
    rw [stackSizeConsCall, stackSizeConsCall, sValEqStackSize _ _ hv, ← sValEqLength _ _ hv]
    rfl

/-- Popping a key-equal copy of a pushed frame restores the pusher's handler. -/
theorem pushEnv_popEnv_handler (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (t s2 y : WordSemStateFiniteExact width C F)
    (hk : sKeyEq (pushEnv envs h t).stack s2.stack)
    (hh : s2.handler = (pushEnv envs h t).handler) (hp : popEnv s2 = some y) :
    y.handler = t.handler := by
  unfold popEnv at hp
  rcases hs : s2.stack with _ | ⟨⟨m, e0, e, opt⟩, rest⟩
  · rw [hs] at hk
    rcases h with _ | ⟨_, _, _, _⟩ <;> exact absurd hk (by simp [pushEnv, sKeyEq])
  · rw [hs] at hk hp
    rcases h with _ | ⟨_, _, l1, l2⟩
    · obtain ⟨-, hf⟩ := hk
      have hopt := ((sFrameKeyEqDef2 _ _ _ _ _ _ _ _).mp hf).2.1
      subst hopt
      simp only [Option.some.injEq] at hp
      subst hp
      exact hh
    · obtain ⟨-, hf⟩ := hk
      have hopt := ((sFrameKeyEqDef2 _ _ _ _ _ _ _ _).mp hf).2.1
      subst hopt
      simp only [Option.some.injEq] at hp
      subst hp
      rfl

/-- Pairs agreeing on both projections are equal (local list-pair reassembly
infrastructure). -/
theorem listEq_of_map_fst_snd {α β : Type} :
    ∀ (l l' : List (α × β)), l.map Prod.fst = l'.map Prod.fst →
      l.map Prod.snd = l'.map Prod.snd → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | (a, b) :: l, (a', b') :: l', h1, h2 => by
      simp only [List.map_cons, List.cons.injEq] at h1 h2
      rw [h1.1, h2.1, listEq_of_map_fst_snd l l' h1.2 h2.2]

/-- A tail call's `bad_fun_return` post-processing keeps the
`evaluate_stack_swap` conclusion of the callee run, moved from the call
environment to the caller (same stack and handler). -/
theorem stackSwapRel_badRet (s T : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
    (E E' : List (WordSemStackFrame width) →
      Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (hr : stackSwapRel T (res, s1) E) (hTs : T.stack = s.stack) (hTh : T.handler = s.handler)
    (hE : ∀ xs, sValEq s.stack xs → ∀ t, E xs = (res, t) →
      E' xs = (if wordSemBadFunReturn res = true then (some .error, t) else (res, t))) :
    stackSwapRel s
      (if wordSemBadFunReturn res = true then (some .error, s1) else (res, s1)) E' := by
  have hv : ∀ xs, sValEq s.stack xs → sValEq T.stack xs := fun xs h => by rw [hTs]; exact h
  rcases res with _ | r
  · trivial
  · cases r with
    | error => trivial
    | «break» k => trivial
    | «continue» k => trivial
    | timeOut =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, fun xs h => hE xs h _ (hx xs (hv xs h))⟩
    | notEnoughSpace =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, fun xs h => hE xs h _ (hx xs (hv xs h))⟩
    | finalFfi e =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, fun xs h => hE xs h _ (hx xs (hv xs h))⟩
    | result v vs =>
        obtain ⟨hk, hh, hx⟩ := hr
        refine ⟨hTs ▸ hk, hh.trans hTh, fun xs h => ?_⟩
        obtain ⟨st, he, hvs, hks⟩ := hx xs (hv xs h)
        exact ⟨st, hE xs h _ he, hvs, hks⟩
    | exception a b =>
        obtain ⟨hlt, e0, e, n, ls, m, lss, hl, hm, hloc, hks, hhn, hx⟩ := hr
        rw [hTs, hTh] at hlt hl
        refine ⟨hlt, e0, e, n, ls, m, lss, hl, hm, hloc, hks, hhn, ?_⟩
        rintro xs e0' e' ls' ⟨hlx, h⟩
        rw [← hTh] at hlx
        obtain ⟨st, locs, he, rest⟩ := hx xs e0' e' ls' ⟨hlx, hv xs h⟩
        exact ⟨st, locs, hE xs h _ he, rest⟩

end CallCase

namespace EvaluateStackSwapCallWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateStackSwapCallWitnesses

open EvaluateStackSwapCallWitnesses

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Call` case
(proof `wordPropsScript.sml:2879-3233`): the HOL conclusion at
`Call ret dest args handler`, from exactly HOL `evaluate_ind`'s four `Call`
induction hypotheses (the return handler after a returning call's `Result`,
the exception handler after its `Exception`, the callee of a returning call,
and the callee of a tail call); no extra premise. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_swap"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateStackSwap_Call {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    ∀ s : WordSemStateFiniteExact width C F,
      (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x ys s1,
          WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
          wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
          v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
          v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
          wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
          evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) = (v5, s2) ∧
          v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length) ∧
          popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
        stackSwapPost retHandler (WordSemStateFiniteExact.setVars n ys s1)) ∧
      (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x' y v n' v2 h
          v4 l1' l2',
          WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
          wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
          v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
          v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
          wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
          evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) = (v5, s2) ∧
          v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
          v4 = (l1', l2') ∧ x' = .loc l1' l2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
        stackSwapPost h (WordSemStateFiniteExact.setVar n' y s2)) ∧
      (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs,
          WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
          wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
          v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
          v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
          wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 →
        stackSwapPost prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))) ∧
      (∀ xs v3 args1 v10 prog ss,
          WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
          wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
          v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = none ∧ handler = none ∧ s.clock ≠ 0 →
        stackSwapPost prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s))) →
      stackSwapPost (.call ret dest args handler) s := by
  rintro s ⟨ihA, ihB, ihC, ihD⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)
    ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [stackSwapPost_iff, ht s ret handler dest args]
  cases hgv : WordSemStateFiniteExact.getVars args s with
  | none => trivial
  | some xv =>
  dsimp only
  by_cases hbad : wordSemBadDestArgs dest args = true
  · rw [if_pos hbad]; trivial
  rw [if_neg hbad]
  cases hfc : wordSemFindCode dest (wordSemAddRetLoc ret xv) s.code s.stackSize with
  | none => trivial
  | some fc =>
  obtain ⟨args1, prog, ss⟩ := fc
  dsimp only
  cases ret with
  | none =>
    cases handler with
    | some _ => trivial
    | none =>
    dsimp only
    by_cases hz : s.clock = 0
    · rw [if_pos hz]
      refine ⟨rfl, rfl, fun xs hxs => ?_⟩
      show evaluate _ _ = _
      rw [ht, getVars_withStack, hgv]
      dsimp only
      rw [if_neg hbad, hfc]
      dsimp only
      rw [if_pos hz]
      rfl
    · rw [if_neg hz]
      have ih := (stackSwapPost_iff _ _).mp
        (ihD xv _ args1 _ prog ss ⟨hgv, hbad, hfc, rfl, rfl, rfl, rfl, hz⟩)
      rcases he : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with
        ⟨res, s1⟩
      rw [he] at ih
      dsimp only
      refine stackSwapRel_badRet s _ res s1 _ _ ih rfl rfl (fun xs hxs t he' => ?_)
      show evaluate _ _ = _
      rw [ht, getVars_withStack, hgv]
      dsimp only
      rw [if_neg hbad, hfc]
      dsimp only
      rw [if_neg hz]
      have hT : WordSemStateFiniteExact.callEnv args1 ss (decClock { s with stack := xs }) =
          { WordSemStateFiniteExact.callEnv args1 ss (decClock s) with stack := xs } :=
        callEnv_withStack _ _ (decClock s) xs hxs
      rw [hT, he']
  | some rv =>
  obtain ⟨n, names, retHandler, l1, l2⟩ := rv
  dsimp only
  by_cases hg : sptDomainEmpty names.1 ∨ ¬ n.Nodup
  · rw [if_pos hg]; trivial
  rw [if_neg hg]
  cases hce : wordSemCutEnvs names s.locals with
  | none => trivial
  | some envs =>
  dsimp only
  by_cases hz : s.clock = 0
  · rw [if_pos hz]
    refine ⟨rfl, rfl, fun xs hxs => ?_⟩
    show evaluate _ _ = _
    rw [ht, getVars_withStack, hgv]
    dsimp only
    rw [if_neg hbad, hfc]
    dsimp only
    rw [if_neg hg, hce]
    dsimp only
    rw [if_pos hz]
    obtain ⟨fr, hfr, hpe⟩ := pushEnv_withStack envs handler s xs hxs
    have hv' : sValEq (pushEnv envs handler s).stack (fr :: xs) := by
      rw [hfr]; exact ⟨hxs, of_eq_true (sFrameValEqRefl fr)⟩
    rw [hpe, callEnv_withStack _ _ _ _ hv']
  rw [if_neg hz]
  have ihP := (stackSwapPost_iff _ _).mp (ihC xv _ args1 _ prog ss _ n _ names _ retHandler _ l1 l2
    envs ⟨hgv, hbad, hfc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg, hce, hz⟩)
  obtain ⟨fr, hfr, -⟩ := pushEnv_withStack envs handler (decClock s) s.stack
    (of_eq_true (sValEqRefl _))
  have hPx : ∀ xs, sValEq s.stack xs →
      WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (decClock { s with stack := xs })) =
        { WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)) with
          stack := fr :: xs } := by
    intro xs hxs
    obtain ⟨fr', hfr', hpe⟩ := pushEnv_withStack envs handler (decClock s) xs hxs
    have hff : fr' = fr := by
      rw [hfr] at hfr'
      exact (List.cons.inj hfr').1.symm
    subst hff
    show WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler
      { decClock s with stack := xs }) = _
    rw [hpe, callEnv_withStack]
    rw [hfr']; exact ⟨hxs, of_eq_true (sFrameValEqRefl _)⟩
  have hPs : (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).stack =
      fr :: s.stack := hfr
  have hvP : ∀ xs, sValEq s.stack xs →
      sValEq (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).stack
        (fr :: xs) := fun xs h => by rw [hPs]; exact ⟨h, of_eq_true (sFrameValEqRefl fr)⟩
  rcases he : evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with ⟨r, s2⟩
  rw [he] at ihP
  rcases r with _ | r
  · trivial
  cases r with
  | error => trivial
  | «break» _ => trivial
  | «continue» _ => trivial
  | timeOut =>
      obtain ⟨a, b, hx⟩ := ihP
      refine ⟨a, b, fun xs hxs => ?_⟩
      show evaluate _ _ = _
      rw [ht, getVars_withStack, hgv]
      dsimp only
      rw [if_neg hbad, hfc]
      dsimp only
      rw [if_neg hg, hce]
      dsimp only
      rw [if_neg hz, hPx xs hxs]
      have hq := hx _ (hvP xs hxs)
      dsimp only at hq
      rw [hq]
      try rfl
  | notEnoughSpace =>
      obtain ⟨a, b, hx⟩ := ihP
      refine ⟨a, b, fun xs hxs => ?_⟩
      show evaluate _ _ = _
      rw [ht, getVars_withStack, hgv]
      dsimp only
      rw [if_neg hbad, hfc]
      dsimp only
      rw [if_neg hg, hce]
      dsimp only
      rw [if_neg hz, hPx xs hxs]
      have hq := hx _ (hvP xs hxs)
      dsimp only at hq
      rw [hq]
      try rfl
  | finalFfi _ =>
      obtain ⟨a, b, hx⟩ := ihP
      refine ⟨a, b, fun xs hxs => ?_⟩
      show evaluate _ _ = _
      rw [ht, getVars_withStack, hgv]
      dsimp only
      rw [if_neg hbad, hfc]
      dsimp only
      rw [if_neg hg, hce]
      dsimp only
      rw [if_neg hz, hPx xs hxs]
      have hq := hx _ (hvP xs hxs)
      dsimp only at hq
      rw [hq]
      try rfl
  | result x ys =>
    obtain ⟨hk, hh, hx⟩ := ihP
    dsimp only
    by_cases hg2 : x ≠ .loc l1 l2 ∨ ys.length ≠ n.length
    · rw [if_pos hg2]; trivial
    rw [if_neg hg2]
    cases hpop : popEnv s2 with
    | none => trivial
    | some s1 =>
    dsimp only
    by_cases hd : sptDomainEqUnion s1.locals envs.1 envs.2
    case neg => rw [if_neg hd]; trivial
    rw [if_pos hd]
    have ihR := (stackSwapPost_iff _ _).mp (ihA xv _ args1 _ prog ss _ n _ names _ retHandler _
      l1 l2 envs _ s2 _ x ys s1 ⟨hgv, hbad, hfc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg, hce, hz,
        he, rfl, rfl, hg2, hpop, hd⟩)
    obtain ⟨n0, l, ls, opt, hs2st, y1, hpy, -, -, hky⟩ :=
      pushEnvPopEnvSKeyEq envs handler (decClock s) s2 hk
    rw [hpop] at hpy
    simp only [Option.some.injEq] at hpy
    subst hpy
    have hh1 : s1.handler = s.handler := pushEnv_popEnv_handler envs handler (decClock s) s2 s1
      hk hh hpop
    have hs1 : s1.stack = ls := by
      unfold popEnv at hpop
      rw [hs2st] at hpop
      rcases opt with _ | ⟨_, _, _⟩ <;>
        (simp only [Option.some.injEq] at hpop; subst hpop; rfl)
    refine stackSwapRel_seqTail s (WordSemStateFiniteExact.setVars n ys s1) _ _ _ ihR hky hh1
      (fun xs hxs => ?_)
    obtain ⟨st0, hst0, hvs, hks⟩ := hx (fr :: xs) (hvP xs hxs)
    dsimp only at hst0
    rw [hs2st] at hvs
    cases st0 with
    | nil => exact absurd hvs (by simp [sValEq])
    | cons fz zs =>
    obtain ⟨hvzs, hfv⟩ := hvs
    obtain ⟨hkzs, hfk⟩ := hks
    have hk2 := hk
    rw [hPs, hs2st] at hk2
    obtain ⟨-, hfk2⟩ := hk2
    have hfeq : WordSemStackFrame.stackFrame n0 (sptToAList envs.1) l opt = fz := by
      have h1 : sKeyEq [WordSemStackFrame.stackFrame n0 (sptToAList envs.1) l opt] [fr] :=
        ⟨trivial, (sKeyEqSym [fr] [_]).mp ⟨trivial, hfk2⟩ |>.2⟩
      have h2 : sKeyEq [fr] [fz] := ⟨trivial, hfk⟩
      have := sValAndKeyEq [WordSemStackFrame.stackFrame n0 (sptToAList envs.1) l opt] [fz]
        ⟨⟨trivial, hfv⟩, sKeyEqTrans _ _ _ ⟨h1, h2⟩⟩
      exact (List.cons.inj this).1
    subst hfeq
    refine ⟨zs, ?_, by show sValEq s1.stack zs; rw [hs1]; exact hvzs, hkzs⟩
    show evaluate _ _ = _
    rw [ht, getVars_withStack, hgv]
    dsimp only
    rw [if_neg hbad, hfc]
    dsimp only
    rw [if_neg hg, hce]
    dsimp only
    rw [if_neg hz, hPx xs hxs]
    rw [hst0]
    dsimp only
    rw [if_neg hg2, popEnv_withStack s2 _ ls zs hs2st, hpop]
    dsimp only [Option.map]
    rw [if_pos hd]
    rfl
  | exception x y =>
    obtain ⟨hlt, e0, e, nn, ls, m, lss, hl, hm, hloc, hks, hhn, hx⟩ := ihP
    cases handler with
    | none =>
      dsimp only
      have hfr0 : fr = .stackFrame (decClock s).localsSize (sptToAList envs.1)
          (wordSemEnvToList envs.2 (decClock s).permute).1 none := by
        simp only [pushEnv, List.cons.injEq] at hfr
        exact hfr.1.symm
      have hPh : (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs none (decClock s))).handler = s.handler := rfl
      have hlt' : s.handler < (fr :: s.stack).length := by rw [← hPs]; exact hlt
      rw [hPh, hPs] at hl
      have hle : s.handler + 1 ≤ s.stack.length := by
        rcases Nat.lt_or_ge s.handler s.stack.length with h | h
        · exact h
        · have heq : s.handler + 1 = (fr :: s.stack).length := by
            simp only [List.length_cons] at hlt' ⊢; omega
          rw [lastNLengthCond _ _ heq, hfr0] at hl
          simp at hl
      rw [lastN_cons _ _ _ hle] at hl
      refine ⟨hle, e0, e, nn, ls, m, lss, hl, hm, hloc, hks, hhn, ?_⟩
      rintro xs e0' e' ls' ⟨hlx, hxs⟩
      have hlen := sValEqLength _ _ hxs
      have hlx' : wordSemLastN ((WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs none (decClock s))).handler + 1) (fr :: xs) =
          .stackFrame m e0' e' (some nn) :: ls' := by
        rw [hPh, lastN_cons _ _ _ (hlen ▸ hle)]; exact hlx
      obtain ⟨st, locs, heq, rest⟩ := hx (fr :: xs) e0' e' ls' ⟨hlx', hvP xs hxs⟩
      dsimp only at heq
      refine ⟨st, locs, ?_, rest⟩
      show evaluate _ _ = _
      rw [ht, getVars_withStack, hgv]
      dsimp only
      rw [if_neg hbad, hfc]
      dsimp only
      rw [if_neg hg, hce]
      dsimp only
      rw [if_neg hz, hPx xs hxs]
      rw [heq]
    | some hv =>
      obtain ⟨n', hprog, l1', l2'⟩ := hv
      dsimp only
      by_cases hx' : x ≠ .loc l1' l2'
      · rw [if_pos hx']; trivial
      rw [if_neg hx']
      by_cases hd : sptDomainEqUnion s2.locals envs.1 envs.2
      case neg => rw [if_neg hd]; trivial
      rw [if_pos hd]
      have hxl : x = .loc l1' l2' := by simpa using hx'
      have ihH := (stackSwapPost_iff _ _).mp (ihB xv _ args1 _ prog ss _ n _ names _ retHandler _
        l1 l2 envs _ s2 _ x y _ n' _ hprog _ l1' l2' ⟨hgv, hbad, hfc, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, hg, hce, hz, he, rfl, rfl, rfl, rfl, rfl, rfl, hxl, hd⟩)
      have hPh : (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs (some (n', hprog, l1', l2')) (decClock s))).handler = s.stack.length := rfl
      have hfr0 : fr = .stackFrame (decClock s).localsSize (sptToAList envs.1)
          (wordSemEnvToList envs.2 (decClock s).permute).1 (some (s.handler, l1', l2')) := by
        simp only [pushEnv, List.cons.injEq] at hfr
        exact hfr.1.symm
      have hwhole : s.stack.length + 1 = (fr :: s.stack).length := by simp
      rw [hPh, hPs, lastNLengthCond _ _ hwhole, hfr0] at hl
      simp only [List.cons.injEq, WordSemStackFrame.stackFrame.injEq, Option.some.injEq] at hl
      obtain ⟨⟨hm0, he0, hee, hnn⟩, hls⟩ := hl
      subst hls
      have hks' : sKeyEq s.stack s2.stack := (sKeyEqSym _ _).mp hks
      have hh2 : s2.handler = s.handler := by rw [hhn, ← hnn]
      refine stackSwapRel_seqTail s (WordSemStateFiniteExact.setVar n' y s2) _ _ _ ihH hks' hh2
        (fun xs hxs => ?_)
      have hlen := sValEqLength _ _ hxs
      have hlx : wordSemLastN ((WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs (some (n', hprog, l1', l2')) (decClock s))).handler + 1) (fr :: xs) =
          .stackFrame m e0 e (some nn) :: xs := by
        rw [hPh, lastNLengthCond _ _ (by simp [hlen]), hfr0, hm0, he0, hee, hnn]
      obtain ⟨st, locs, heq, ⟨lss', hf', hlocs, hsnd⟩, hvs, hks2⟩ :=
        hx (fr :: xs) e0 e xs ⟨hlx, hvP xs hxs⟩
      dsimp only at heq
      have hlss : lss = lss' := listEq_of_map_fst_snd _ _ (hloc.1.symm.trans hf') hsnd
      subst hlss
      have hlocs' : locs = s2.locals := hlocs.trans hloc.2.symm
      subst hlocs'
      refine ⟨st, ?_, hvs, hks2⟩
      show evaluate _ _ = _
      rw [ht, getVars_withStack, hgv]
      dsimp only
      rw [if_neg hbad, hfc]
      dsimp only
      rw [if_neg hg, hce]
      dsimp only
      rw [if_neg hz, hPx xs hxs]
      rw [heq]
      dsimp only
      rw [if_neg hx', if_pos hd, ← hhn]
      rfl

end WordSemStackEq

end Flapjack
