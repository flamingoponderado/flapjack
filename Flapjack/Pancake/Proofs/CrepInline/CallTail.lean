import Flapjack.Pancake.Proofs.CrepInline.Call
import Flapjack.Pancake.Proofs.CrepInline.UnreachElimEvaluate
import Flapjack.Pancake.Proofs.CrepInline.ArgLoadStrong
import Flapjack.Pancake.Proofs.CrepInline.ClockExpressions

/-!
# `inline_prog_correct`: the `Call` case, `Tail` part

`Resume inline_prog_correct[Tail]` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2536-2575`,
bead `flapjack-pxn.18.5.5.42.2`): an inlined tail call.  `inline_prog`
replaces `Call NONE fname argexps`, whose callee `(ns, body)` is in
`inl_bag`, with `inline_tail (arg_load tmp_vars argexps ns body')`, where
`body' = FST (unreach_elim (inline_prog (inl_bag \\ fname) body))`.  The proof
follows HOL's:
1. the callee IH relates the callee run to the run of
   `inline_prog (inl_bag \\ fname) body` from `dec_clock s1` with the
   argument locals;
2. `unreach_elim_correct` transfers that run to `body'`;
3. `general_simulate_arg_load_strong_all_drule` (with `t = FEMPTY`) relates
   the `arg_load` wrapper;
4. the source call's result mapping finishes the case.

The theorem is a Flapjack helper of the tagged Call case (`.42.4`), like
`callNonInlined`.
-/

namespace Flapjack

namespace CrepInlineCallCase

open CrepInlineCanonical CrepInlineExact

variable {width : Nat} [NeZero width] {σ : Type}

/-- HOL `inline_prog_def` on an inlined tail call (`crep_inlineScript.sml:212-224`). -/
theorem inlineProgHOLExact_call_tail (inlBag : InlMap width)
    (fname : CrepInlineMapHOLName) (args : List (CrepExpHOL width))
    (ns : List Nat) (body : CrepProgHOL width)
    (h : inlBag.lookup fname = some (ns, body)) :
    inlineProgHOLExact inlBag (.call none fname args) =
      inlineTailHOLExact (argLoadHOLExact
        (genlistSuccAddHOLExact (max ((args.flatMap crepExpVarsHOL).foldl max 0) (ns.foldl max 0))
          ns.length)
        args ns (unreachElimHOLExact (inlineProgHOLExact (inlBag.erase fname) body)).1) := by
  unfold inlineProgHOLExact
  simp only [inlineProgHOLCoreExact]
  split
  · rename_i heq; rw [h] at heq; cases heq
  · rename_i ns' body' heq
    rw [h] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [inlineProgHOLCoreExact_eq_inlineProgHOLExact]

theorem submap_erase (m : InlMap width) (k : CrepInlineMapHOLName) :
    HolFiniteMapExact.submap (m.erase k) m := by
  intro x v h
  simp only [HolFiniteMapExact.erase, FDOMSUB] at h
  split at h
  · cases h
  · exact h

theorem submap_trans' {α β : Type} {a b c : HolFiniteMapExact α β}
    (h1 : HolFiniteMapExact.submap a b) (h2 : HolFiniteMapExact.submap b c) :
    HolFiniteMapExact.submap a c :=
  fun x v h => h2 x v (h1 x v h)

theorem updateList_eq_updateListEq (l : List (Nat × HolWordLab width)) :
    (HolFiniteMapExact.empty : HolFiniteMapExact Nat (HolWordLab width)).updateList l =
      HolFiniteMapExact.empty.updateListEq l := by
  have h : ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (HolWordLab width)).updateList l).lookup =
      (HolFiniteMapExact.empty.updateListEq l).lookup := by
    simp only [HolFiniteMapExact.updateList, HolFiniteMapExact.updateListEq]
    exact (FUPDATE_LIST_HOL_eq_FUPDATE_LIST _ l).symm
  cases hA : (HolFiniteMapExact.empty : HolFiniteMapExact Nat (HolWordLab width)).updateList l
  cases hB : (HolFiniteMapExact.empty : HolFiniteMapExact Nat (HolWordLab width)).updateListEq l
  rw [hA, hB] at h
  simp only at h
  subst h
  rfl

/-- The temporaries of an inlined call: distinct, of the right length, and
    fresh for the callee parameters and the argument expressions. -/
theorem tmpVars_facts (args : List (CrepExpHOL width)) (ns : List Nat) :
    let tmps := genlistSuccAddHOLExact
      (max ((args.flatMap crepExpVarsHOL).foldl max 0) (ns.foldl max 0)) ns.length
    tmps.Nodup ∧ tmps.length = ns.length ∧ (∀ x, x ∈ tmps → x ∉ ns) ∧
      (∀ x, x ∈ tmps → x ∉ (args.map crepExpVarsHOL).flatten) := by
  intro tmps
  have hmem : ∀ x, x ∈ tmps → max ((args.flatMap crepExpVarsHOL).foldl max 0) (ns.foldl max 0) < x := by
    intro x hx
    simp only [tmps, genlistSuccAddHOLExact, List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    omega
  refine ⟨?_, by simp [tmps, genlistSuccAddHOLExact], ?_, ?_⟩
  · simp only [tmps, genlistSuccAddHOLExact]
    have := genlist_all_distinct ns.length
      (max ((args.flatMap crepExpVarsHOL).foldl max 0) (ns.foldl max 0))
    have hf : (fun offset => offset + max ((args.flatMap crepExpVarsHOL).foldl max 0)
        (ns.foldl max 0) + 1) =
        (fun x => max ((args.flatMap crepExpVarsHOL).foldl max 0) (ns.foldl max 0) + (x + 1)) := by
      funext x; omega
    rw [hf]; exact this
  · intro x hx hn
    have h1 := hmem x hx
    have h2 : x ≤ ns.foldl max 0 := mem_le_foldl_max (fun y => y) hn 0
    omega
  · intro x hx hn
    have h1 := hmem x hx
    have hn' : x ∈ args.flatMap crepExpVarsHOL := by
      simpa [List.flatMap] using hn
    have h2 : x ≤ (args.flatMap crepExpVarsHOL).foldl max 0 := mem_le_foldl_max (fun y => y) hn' 0
    omega

/-- `Tail` part of HOL `inline_prog_correct`'s Call case
    (`crep_inlineProofScript.sml:2536-2575`): the inlined tail call.  The
    induction hypothesis is `evaluate_ind`'s Call body premise with
    `P := crepInlineGoal`, as in `callNonInlined`.  Flapjack helper of the
    tagged Call case. -/
theorem callTail
    (fname : Flapjack.Basis.Pure.MlString.MlString) (argexps : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (ihBody : ∀ (args : List (HolWordLab width))
        (v6 : CrepProgHOL width × HolFiniteMapExact Nat (HolWordLab width))
        (prog : CrepProgHOL width) (newlocals : HolFiniteMapExact Nat (HolWordLab width)),
      argexps.mapM (crepExactEvalExpClassical s) = some args →
      lookupCodeHOLFinite s.code.lookup fname args (List.length args) = some v6 →
      v6 = (prog, newlocals) →
      (¬ (match (none : Option (List Nat × Option (BitVec width × CrepProgHOL width))) with
          | none => False
          | some (rts, _) => ¬ rts.Nodup)) →
      s.clock ≠ 0 →
      crepInlineGoal prog { decClockCrepSemHOL s with locals := newlocals }) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (inlFs : InlMap width) (t : CrepSemHOLState width σ) (inlBag : InlMap width)
      (ns : List Nat) (body : CrepProgHOL width),
      inlBag.lookup fname = some (ns, body) →
      evalCrepSemHOLProgExact s (.call none fname argexps) = (r, s') → r ≠ some .error →
      HolFiniteMapExact.submap inlFs s.code → HolFiniteMapExact.submap inlBag inlFs →
      crepInlineStateRelCodeExact s t → crepInlineLocalsStrongRelExact s t →
      crepInlineCodeInlRelExact inlFs s t →
      ∃ t' : CrepSemHOLState width σ,
        evalCrepSemHOLProgExact t (inlineProgHOLExact inlBag (.call none fname argexps)) =
          (r, t') ∧
        crepInlineStateRelCodeExact s' t' ∧ crepInlineCodeInlRelExact inlFs s' t' ∧
        resultPost r s' t' := by
  intro r s' inlFs t inlBag ns body hbagf hev hne hsub hbag hsr hls hci
  rw [inlineProgHOLExact_call_tail _ _ _ _ _ hbagf]
  have hcs : s.code.lookup fname = some (ns, body) := hsub _ _ (hbag _ _ hbagf)
  rw [evalCrepSemHOLProgExact_call_holShape] at hev
  rcases hargs : argexps.mapM (evalCrepSemHOLExp s) with _ | vs
  · simp only [hargs, Prod.mk.injEq] at hev
    exact absurd hev.1.symm hne
  have hargsT := optMmapEvalCodeInlExact s argexps vs t inlFs ⟨hargs, hsr, hls, hci⟩
  simp only [hargs] at hev
  rcases hlk : lookupCodeFiniteHOL s.code fname vs vs.length with _ | ⟨prog, newlocals⟩
  · simp only [hlk, Prod.mk.injEq] at hev
    exact absurd hev.1.symm hne
  simp only [hlk] at hev
  have hlk' := hlk
  unfold lookupCodeFiniteHOL at hlk'
  simp only [hcs] at hlk'
  have hcond : ns.length = vs.length ∧ ns.Nodup := by
    by_cases hc : ns.length = vs.length ∧ ns.Nodup
    · exact hc
    · rw [if_neg hc] at hlk'
      cases hlk'
  rw [if_pos hcond] at hlk'
  simp only [Option.some.injEq, Prod.mk.injEq] at hlk'
  obtain ⟨rfl, rfl⟩ := hlk'
  have hnd : ¬ crepReturnInfoNodupError
      (none : Option (List Nat × Option (BitVec width × CrepProgHOL width))) := by
    simp [crepReturnInfoNodupError]
  rw [if_neg hnd] at hev
  have hclk : s.clock = t.clock := hsr.2.2.2.2.1
  simp only [inlineTailHOLExact]
  rw [evalCrepSemHOLProgExact_seq_fixClockFree, evalCrepSemHOLProgExact_tick]
  by_cases hz : s.clock = 0
  · rw [if_pos hz] at hev
    rw [if_pos (hclk ▸ hz)]
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    refine ⟨t.emptyLocals, rfl, hsr, codeInl_of_code_eq rfl rfl hci, trivial⟩
  rw [if_neg hz] at hev
  rw [if_neg (fun h => hz (hclk ▸ h))]
  dsimp only
  have ihB := ihBody vs (body, HolFiniteMapExact.empty.updateList (ns.zip vs)) body
    (HolFiniteMapExact.empty.updateList (ns.zip vs))
    (by rw [show crepExactEvalExpClassical s = evalCrepSemHOLExp s from
          funext (crepExactEvalExpClassical_eq s)]; exact hargs)
    (lookupCodeFiniteHOL_eq_holFinite _ _ _ _ _ _ hlk) rfl (by simp) hz
  rcases hb : evalCrepSemHOLProgExact
      { decClockCrepSemHOL s with locals := HolFiniteMapExact.empty.updateList (ns.zip vs) } body
    with ⟨r0, s0⟩
  rw [hb] at hev
  have hkey : r = r0 ∧ s' = s0.emptyLocals ∧ r0 ≠ some .error ∧ resultPost r0 s' s' := by
    rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
    all_goals simp only at hev
    all_goals simp only [Prod.mk.injEq] at hev
    · exact absurd hev.1.symm hne
    · exact absurd hev.1.symm hne
    · exact ⟨hev.1.symm, hev.2.symm, by simp, trivial⟩
    · exact absurd hev.1.symm hne
    · exact absurd hev.1.symm hne
    all_goals exact ⟨hev.1.symm, hev.2.symm, by simp, trivial⟩
  obtain ⟨hrr, hss, hr0ne, _⟩ := hkey
  have hsrD : crepInlineStateRelCodeExact
      { decClockCrepSemHOL s with locals := HolFiniteMapExact.empty.updateList (ns.zip vs) }
      { decClockCrepSemHOL t with locals := HolFiniteMapExact.empty.updateList (ns.zip vs) } := by
    obtain ⟨a, b, c, d, e, f, g, h, i⟩ := hsr
    exact ⟨a, b, c, d, by simp [decClockCrepSemHOL, e], f, g, h, i⟩
  obtain ⟨t1, ht1, hrel1, hci1, _⟩ := ihB r0 s0 inlFs
    { decClockCrepSemHOL t with locals := HolFiniteMapExact.empty.updateList (ns.zip vs) }
    (inlBag.erase fname) hb hr0ne hsub (submap_trans' (submap_erase _ _) hbag) hsrD rfl
    (codeInl_of_code_eq rfl rfl hci)
  have hu := CrepInlineUnreachElimEvaluate.unreachElimCorrect _ _ _ _ _ _ ⟨ht1, hr0ne, rfl⟩
  obtain ⟨hnd', hlen', hnotns, hnotargs⟩ := tmpVars_facts argexps ns
  have hargsD : argexps.mapM (evalCrepSemHOLExp (decClockCrepSemHOL t)) = some vs := by
    rw [CrepInlineClockExpressions.optMmapEvalDecClockEq]; exact hargsT
  rw [updateList_eq_updateListEq] at hu
  rcases hn2 : evalCrepSemHOLProgExact (decClockCrepSemHOL t)
      (argLoadHOLExact
        (genlistSuccAddHOLExact (max ((argexps.flatMap crepExpVarsHOL).foldl max 0) (ns.foldl max 0))
          ns.length)
        argexps ns (unreachElimHOLExact (inlineProgHOLExact (inlBag.erase fname) body)).1)
    with ⟨r1, t'⟩
  have hd := generalSimulateArgLoadStrongAllDruleExact (decClockCrepSemHOL t) argexps vs ns
    HolFiniteMapExact.empty _ r0 t1 _ r1 t'
    ⟨hargsD, hcond.1, hcond.2, fun _ _ h => by simp [HolFiniteMapExact.empty] at h, hu,
      fun _ _ => by simp [crepHolFdom, HolFiniteMapExact.empty], hr0ne, hnd', hlen', hnotns,
      hnotargs, by simpa [argLoadHOLExact] using hn2⟩
  obtain ⟨hr1, hrel2, _⟩ := hd
  subst hss
  refine ⟨t', by rw [hr1, hrr], ?_, ?_, ?_⟩
  · obtain ⟨a, b, c, d, e, f, g, h, i⟩ := hrel1
    obtain ⟨a', _, b', c', d', e', f', g', h', i'⟩ := hrel2
    exact ⟨a.trans a', b.trans b', c.trans c', d.trans d', e.trans e', f.trans f',
      g.trans g', h.trans h', i.trans i'⟩
  · exact codeInl_of_code_eq rfl hrel2.2.1.symm hci1
  · rw [hrr]
    rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
    all_goals simp only at hev
    all_goals simp only [Prod.mk.injEq] at hev
    all_goals first | exact absurd hev.1.symm hne | trivial


end CrepInlineCallCase

end Flapjack
