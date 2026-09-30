import Flapjack.Pancake.Proofs.CrepInline.CallTail
import Flapjack.Pancake.Proofs.CrepInline.FiniteMapLemmas
import Flapjack.Pancake.Proofs.CrepInline.WrappedTransformIf
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Assembly
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Assembly
import Flapjack.Pancake.Proofs.CrepInline.NestedDecs

/-!
# `inline_prog_correct`: the `Call` case, `Nontail` part

`Resume inline_prog_correct[Nontail]` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2719-3037`,
bead `flapjack-pxn.18.5.5.42.3`): an inlined assignment call
`Call (SOME (rets, NONE)) fname argexps` with distinct `rets` and callee
`(ns, body)` in `inl_bag`, which `inline_prog` replaces by
`inline_nontail P rets trets tmps argexps ns`.  The proof follows HOL's:
* `evaluate_nested_decs_locals_nested_res_var_drule` handles the outer
  declaration of the return temporaries `trets`.
* The callee IH and `unreach_elim_correct` give the run of the inlined callee.
* `evaluate_state_locals_rel_strong` moves that run to the target locals.
* `wrapped_transform_if` gives the run of the transformed callee `P`, with the
  return values in `trets`.
* `general_simulate_arg_load_strong_all_drule` relates the `arg_load` wrapper.
* `evaluate_nested_seq_assign_drule` covers the final copy `rets := trets`.
* In the returning case, the local maps are equal by `submap_finish_flookup`
  and `evaluate_locals_same_fdom'`.

The finite-map reordering HOL does with `FUPDATE_LIST_APPEND_COMMUTES` is not
needed: `SUBMAP_IMP_FUPDATE_LIST_SUBMAP` gives the required submap directly.
`callNontail` is a Flapjack helper of the tagged Call case (`.42.4`), like
`callTail` and `callNonInlined`.
-/

namespace Flapjack

namespace CrepInlineCallCase

open CrepInlineCanonical CrepInlineExact CrepInlineWrappedTransformIf CrepInlineUnreachElim

variable {width : Nat} [NeZero width] {σ : Type}

/-- The inlined callee body of `inline_prog` for callee `(ns, body)`. -/
noncomputable def inlinedCallee (inlBag : InlMap width) (fname : CrepInlineMapHOLName)
    (body : CrepProgHOL width) : CrepProgHOL width :=
  (unreachElimHOLExact (inlineProgHOLExact (inlBag.erase fname) body)).1

/-- The argument temporaries of `inline_prog`. -/
def argTmps (args : List (CrepExpHOL width)) (ns : List Nat) : List Nat :=
  genlistSuccAddHOLExact (max ((args.flatMap crepExpVarsHOL).foldl max 0) (ns.foldl max 0))
    ns.length

/-- The return temporaries of `inline_prog`. -/
def retTmps (rets : List Nat) (callee : CrepProgHOL width) (tmps : List Nat) : List Nat :=
  genlistSuccAddHOLExact (max (rets.foldl max 0) (max (crepVmaxProgHOLExact callee) (tmps.foldl max 0)))
    rets.length

/-- The transformed callee of `inline_prog`'s assign-call case. -/
noncomputable def transformedCallee (callee : CrepProgHOL width) (trets : List Nat) :
    CrepProgHOL width :=
  if notBranchRetHOLExact callee then .seq .tick (transformEocHOLExact trets callee)
  else .while (.const 1) (transformBranchHOLExact 0 trets callee)

/-- HOL `inline_prog_def` on an inlined assign call (`crep_inlineScript.sml:211-233`). -/
theorem inlineProgHOLExact_call_nontail (inlBag : InlMap width)
    (fname : CrepInlineMapHOLName) (args : List (CrepExpHOL width)) (rets : List Nat)
    (ns : List Nat) (body : CrepProgHOL width)
    (hd : crepAllDistinct rets = true)
    (h : inlBag.lookup fname = some (ns, body)) :
    inlineProgHOLExact inlBag (.call (some (rets, none)) fname args) =
      inlineNontailHOLExact
        (transformedCallee (inlinedCallee inlBag fname body)
          (retTmps rets (inlinedCallee inlBag fname body) (argTmps args ns)))
        rets (retTmps rets (inlinedCallee inlBag fname body) (argTmps args ns))
        (argTmps args ns) args ns := by
  unfold inlineProgHOLExact
  simp only [inlineProgHOLCoreExact, hd, Bool.not_true, Bool.false_eq_true, if_false]
  split
  · rename_i heq; rw [h] at heq; cases heq
  · rename_i ns' body' heq
    rw [h] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [inlineProgHOLCoreExact_eq_inlineProgHOLExact, inlinedCallee, argTmps, retTmps,
      transformedCallee]
    rfl

theorem genlist_gt {base len x : Nat} (hx : x ∈ genlistSuccAddHOLExact base len) : base < x := by
  simp only [genlistSuccAddHOLExact, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  omega

theorem genlist_nodup (base len : Nat) : (genlistSuccAddHOLExact base len).Nodup := by
  simp only [genlistSuccAddHOLExact]
  have hf : (fun offset => offset + base + 1) = (fun x => base + (x + 1)) := by
    funext x; omega
  rw [hf]; exact genlist_all_distinct len base

theorem le_foldl_max_mem {l : List Nat} {y : Nat} (h : y ∈ l) : y ≤ l.foldl max 0 :=
  mem_le_foldl_max (fun z => z) h 0

theorem exists_mem_genlist {base len : Nat} (h : 0 < len) :
    ∃ z, z ∈ genlistSuccAddHOLExact base len := by
  refine ⟨0 + base + 1, ?_⟩
  simp only [genlistSuccAddHOLExact, List.mem_map, List.mem_range]
  exact ⟨0, h, rfl⟩

/-- The return temporaries of an inlined assign call: distinct, of the right
    length, and fresh for the return names, argument temporaries, callee
    parameters, callee variables and argument variables. -/
theorem retTmps_facts (rets ns : List Nat) (args : List (CrepExpHOL width))
    (callee : CrepProgHOL width) (hlen : args.length = ns.length) :
    (retTmps rets callee (argTmps args ns)).Nodup ∧
    (retTmps rets callee (argTmps args ns)).length = rets.length ∧
    ∀ x, x ∈ retTmps rets callee (argTmps args ns) →
      x ∉ rets ∧ x ∉ argTmps args ns ∧ x ∉ ns ∧ x ∉ crepVarProgHOLExact callee ∧
        x ∉ (args.map crepExpVarsHOL).flatten := by
  refine ⟨genlist_nodup _ _, by simp [retTmps, genlistSuccAddHOLExact], ?_⟩
  intro x hx
  have hB := genlist_gt hx
  have hbelow : ∀ y, y ∈ argTmps args ns → y < x := by
    intro y hy; have := le_foldl_max_mem hy; omega
  have htmp : ∀ y, (y ∈ ns ∨ y ∈ args.flatMap crepExpVarsHOL) → ∃ z, z ∈ argTmps args ns ∧ y < z := by
    intro y hy
    have hpos : 0 < ns.length := by
      rcases hy with hy | hy
      · exact List.length_pos_of_mem hy
      · rw [← hlen]
        obtain ⟨e, he, _⟩ := List.mem_flatMap.mp hy
        exact List.length_pos_of_mem he
    obtain ⟨z, hz⟩ := exists_mem_genlist (base := max ((args.flatMap crepExpVarsHOL).foldl max 0)
      (ns.foldl max 0)) hpos
    refine ⟨z, hz, ?_⟩
    have hzgt := genlist_gt hz
    rcases hy with hy | hy
    · have := le_foldl_max_mem hy; omega
    · have := le_foldl_max_mem hy; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hm; have := le_foldl_max_mem hm; omega
  · intro hm; have := hbelow x hm; omega
  · intro hm
    obtain ⟨z, hz, hyz⟩ := htmp x (Or.inl hm)
    have := hbelow z hz; omega
  · intro hm
    have : x ≤ crepVmaxProgHOLExact callee := le_foldl_max_mem hm
    omega
  · intro hm
    have hm' : x ∈ args.flatMap crepExpVarsHOL := by simpa [List.flatMap] using hm
    obtain ⟨z, hz, hyz⟩ := htmp x (Or.inr hm')
    have := hbelow z hz; omega

theorem codeRel_trans {a b c : CrepSemHOLState width σ}
    (h1 : crepInlineStateRelCodeExact a b) (h2 : crepInlineStateRelExact b c) :
    crepInlineStateRelCodeExact a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  obtain ⟨b1, _, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8, a9.trans b9⟩

theorem codeRel_emptyLocals {a b : CrepSemHOLState width σ}
    (h : crepInlineStateRelCodeExact a b) :
    crepInlineStateRelCodeExact a.emptyLocals b := h

theorem finmap_eq_of_submap_fdom {β : Type} {f g : HolFiniteMapExact Nat β}
    (hsub : f.submap g) (hdom : crepHolFdom f.lookup = crepHolFdom g.lookup) : f = g := by
  have h : f.lookup = g.lookup := by
    funext k
    cases hf : f.lookup k with
    | some v => exact (hsub k v hf).symm
    | none =>
        have := congrFun hdom k
        cases hg : g.lookup k with
        | none => rfl
        | some v => simp [crepHolFdom, hf, hg] at this
  cases f; cases g; cases h; rfl

theorem vars_map_var (l : List Nat) :
    ((l.map (CrepExpHOL.var (width := width))).map crepExpVarsHOL).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.flatten_cons, ih, crepExpVarsHOL]; rfl

theorem nestedSeq_assigns (rets trets : List Nat) :
    panMap2 CrepProgHOL.assign rets (trets.map (CrepExpHOL.var (width := width))) =
      rets.zipWith (fun name temporary => CrepProgHOL.assign name (.var temporary)) trets := by
  rw [CrepInlineTransformEoc.panMap2_eq_zipWith, List.zipWith_map_right]

/-- At clock `0` the transformed callee times out at once. -/
theorem transformedCallee_clock0 (callee : CrepProgHOL width) (trets : List Nat)
    (u : CrepSemHOLState width σ) (h0 : u.clock = 0) :
    evalCrepSemHOLProgExact u (transformedCallee callee trets) =
      (some .timeOut, CrepSemHOLState.emptyLocals u) := by
  unfold transformedCallee
  split
  · rw [evalCrepSemHOLProgExact_seq_fixClockFree, evalCrepSemHOLProgExact_tick, if_pos h0]
  · rw [evalCrepSemHOLProgExact_while_holShape]
    simp [evalCrepSemHOLExp, h0]
    exact NeZero.ne width

theorem replicate_const_eval (n : Nat) (u : CrepSemHOLState width σ) :
    (List.replicate n (CrepExpHOL.const (0 : BitVec width))).mapM (evalCrepSemHOLExp u) =
      some (List.replicate n (HolWordLab.word (0 : BitVec width))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.mapM_cons, evalCrepSemHOLExp, ih]
      rfl

theorem mapM_some_isSome {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ k, k ∈ xs → (f k).isSome
  | [], _, _, _, hk => by cases hk
  | a :: rest, ys, h, k, hk => by
      simp only [List.mapM_cons] at h
      cases ha : f a with
      | none => rw [ha] at h; simp at h
      | some va =>
          rw [ha] at h
          cases hr : rest.mapM f with
          | none => rw [hr] at h; simp at h
          | some vr =>
              rcases List.mem_cons.mp hk with rfl | hk'
              · rw [ha]; rfl
              · exact mapM_some_isSome f rest vr hr k hk'

theorem crepAllDistinct_nodup : ∀ (l : List Nat), crepAllDistinct l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
      simp only [crepAllDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
      refine List.nodup_cons.mpr ⟨fun hm => ?_, crepAllDistinct_nodup l h.2⟩
      have := h.1
      rw [List.contains_eq_any_beq, List.any_eq_false] at this
      exact this a hm (by simp)

theorem callNontail
    (fname : Flapjack.Basis.Pure.MlString.MlString) (argexps : List (CrepExpHOL width))
    (rets : List Nat) (s : CrepSemHOLState width σ)
    (ihBody : ∀ (args : List (HolWordLab width))
        (v6 : CrepProgHOL width × HolFiniteMapExact Nat (HolWordLab width))
        (prog : CrepProgHOL width) (newlocals : HolFiniteMapExact Nat (HolWordLab width)),
      argexps.mapM (crepExactEvalExpClassical s) = some args →
      lookupCodeHOLFinite s.code.lookup fname args (List.length args) = some v6 →
      v6 = (prog, newlocals) →
      (¬ (match (some (rets, none) : Option (List Nat × Option (BitVec width × CrepProgHOL width))) with
          | none => False
          | some (rts, _) => ¬ rts.Nodup)) →
      s.clock ≠ 0 →
      crepInlineGoal prog { decClockCrepSemHOL s with locals := newlocals }) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (inlFs : InlMap width) (t : CrepSemHOLState width σ) (inlBag : InlMap width)
      (ns : List Nat) (body : CrepProgHOL width),
      crepAllDistinct rets = true →
      inlBag.lookup fname = some (ns, body) →
      evalCrepSemHOLProgExact s (.call (some (rets, none)) fname argexps) = (r, s') →
      r ≠ some .error →
      HolFiniteMapExact.submap inlFs s.code → HolFiniteMapExact.submap inlBag inlFs →
      crepInlineStateRelCodeExact s t → crepInlineLocalsStrongRelExact s t →
      crepInlineCodeInlRelExact inlFs s t →
      ∃ t' : CrepSemHOLState width σ,
        evalCrepSemHOLProgExact t
            (inlineProgHOLExact inlBag (.call (some (rets, none)) fname argexps)) = (r, t') ∧
        crepInlineStateRelCodeExact s' t' ∧ crepInlineCodeInlRelExact inlFs s' t' ∧
        resultPost r s' t' := by
  intro r s' inlFs t inlBag ns body hdist hbagf hev hne hsub hbag hsr hls hci
  rw [inlineProgHOLExact_call_nontail _ _ _ _ _ _ hdist hbagf]
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
  have hretsNodup : rets.Nodup := crepAllDistinct_nodup rets hdist
  have hnd : ¬ crepReturnInfoNodupError
      (some (rets, none) : Option (List Nat × Option (BitVec width × CrepProgHOL width))) := by
    simp [crepReturnInfoNodupError, hretsNodup]
  rw [if_neg hnd] at hev
  have hclk : s.clock = t.clock := hsr.2.2.2.2.1
  have hlenArgs : argexps.length = ns.length := by
    rw [hcond.1]; exact (opt_mmap_length_eq argexps (evalCrepSemHOLExp s) vs hargs)
  obtain ⟨htrNd, htrLen, htrFresh⟩ :=
    retTmps_facts rets ns argexps (inlinedCallee inlBag fname body) hlenArgs
  obtain ⟨htNd, htLen, htNotNs, htNotArgs⟩ := tmpVars_facts argexps ns
  have htNd' : (argTmps argexps ns).Nodup := htNd
  have htLen' : (argTmps argexps ns).length = ns.length := htLen
  have htNotNs' : ∀ x, x ∈ argTmps argexps ns → x ∉ ns := htNotNs
  have htNotArgs' : ∀ x, x ∈ argTmps argexps ns → x ∉ (argexps.map crepExpVarsHOL).flatten :=
    htNotArgs
  clear htNd htLen htNotNs htNotArgs
  generalize hcal : inlinedCallee inlBag fname body = callee' at *
  generalize htm : argTmps argexps ns = tmps at *
  generalize htr : retTmps rets callee' tmps = trets at *
  simp only [inlineNontailHOLExact]
  generalize hP : transformedCallee callee' trets = P
  have hzerosLen : trets.length = (List.replicate trets.length
      (HolWordLab.word (0 : BitVec width))).length := by simp
  rcases hT0 : evalCrepSemHOLProgExact t (nestedDecsHOL trets
      (List.replicate trets.length (CrepExpHOL.const 0))
      (.seq (argLoadHOLExact tmps argexps ns P)
        (crepNestedSeqHOL (rets.zipWith (fun name temporary => .assign name (.var temporary))
          trets)))) with ⟨r1, t'⟩
  rcases hW : evalCrepSemHOLProgExact
      { t with locals := (t.locals.updateListEq
          (trets.zip (List.replicate trets.length (HolWordLab.word (0 : BitVec width))))) }
      (.seq (argLoadHOLExact tmps argexps ns P)
        (crepNestedSeqHOL (rets.zipWith (fun name temporary => .assign name (.var temporary))
          trets))) with ⟨rW, sW⟩
  obtain ⟨hr1, hrelA, hlocA⟩ := evaluateNestedDecsLocalsNestedResVarDruleExact _ t rW sW trets
    (List.replicate trets.length (CrepExpHOL.const 0))
    (List.replicate trets.length (HolWordLab.word (0 : BitVec width))) r1 t'
    (replicate_const_eval _ t) (by simp) htrNd
    (fun v _ e he => by
      obtain ⟨_, he'⟩ := List.mem_replicate.mp he
      subst he'; simp [crepExpVarsHOL]) hW hT0
  generalize hz : List.replicate trets.length (HolWordLab.word (0 : BitVec width)) = zeros at *
  have hzl : zeros.length = trets.length := by rw [← hz]; simp
  rw [evalCrepSemHOLProgExact_seq_fixClockFree] at hW
  rcases hArg : evalCrepSemHOLProgExact { t with locals := (t.locals.updateListEq (trets.zip zeros)) }
      (argLoadHOLExact tmps argexps ns P) with ⟨rA, sA⟩
  simp only [hArg] at hW
  have hargsZ : argexps.mapM
      (evalCrepSemHOLExp { t with locals := (t.locals.updateListEq (trets.zip zeros)) }) =
        some vs := by
    rw [CrepInlineUpdateListLocals.optMmapUpdateListLocalsNotVarsEvalEq' argexps trets () zeros t t.locals
      ⟨fun x hx => (htrFresh x hx).2.2.2.2, by omega⟩]
    exact hargsT
  have hZsub : (HolFiniteMapExact.empty.updateListEq (trets.zip zeros)).submap
      (t.locals.updateListEq (trets.zip zeros)) := fun k v h => by
    simp only [HolFiniteMapExact.lookup_updateListEq] at h ⊢
    exact submap_fupdateListHOL _ _ _ (fun k v h => by simp [HolFiniteMapExact.empty] at h) k v h
  have hnotZ : ∀ v, v ∉ trets → (HolFiniteMapExact.empty.updateListEq
      (trets.zip zeros) : HolFiniteMapExact Nat (HolWordLab width)).lookup v = none := by
    intro v hv
    simp only [HolFiniteMapExact.lookup_updateListEq]
    have := FLOOKUP_FUPDATE_LIST_HOL_not_mem
      (HolFiniteMapExact.empty : HolFiniteMapExact Nat (HolWordLab width)).lookup
      (trets.zip zeros) v (fun hm => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        exact hv (List.of_mem_zip he).1)
    simp only [FLOOKUP] at this
    rw [this]; rfl
  have hZfresh : ∀ v, v ∈ ns ∨ v ∈ tmps →
      crepHolFdom (HolFiniteMapExact.empty.updateListEq (trets.zip zeros)).lookup v = false := by
    intro v hv
    have hvn : v ∉ trets := fun hm => by
      rcases hv with hv | hv
      · exact (htrFresh v hm).2.2.1 hv
      · exact (htrFresh v hm).2.1 hv
    simp only [crepHolFdom, hnotZ v hvn]; rfl
  have hArg' : evalCrepSemHOLProgExact { t with locals := (t.locals.updateListEq (trets.zip zeros)) }
      (nestedDecsHOL tmps argexps (nestedDecsHOL ns (tmps.map CrepExpHOL.var) P)) = (rA, sA) := by
    simpa [argLoadHOLExact] using hArg
  by_cases hz0 : s.clock = 0
  · rw [if_pos hz0] at hev
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    have hP0 : evalCrepSemHOLProgExact
        { ({ t with locals := (t.locals.updateListEq (trets.zip zeros)) } : CrepSemHOLState width σ) with
          locals := (HolFiniteMapExact.empty.updateListEq (trets.zip zeros)).updateListEq (ns.zip vs) } P =
        (some .timeOut, CrepSemHOLState.emptyLocals
          { ({ t with locals := (t.locals.updateListEq (trets.zip zeros)) } : CrepSemHOLState width σ) with
            locals := (HolFiniteMapExact.empty.updateListEq (trets.zip zeros)).updateListEq (ns.zip vs) }) := by
      rw [← hP]; exact transformedCallee_clock0 _ _ _ (by simp; omega)
    obtain ⟨hrA, hrelD, _⟩ := generalSimulateArgLoadStrongAllDruleExact _ argexps vs ns _ P _ _ tmps rA sA
      ⟨hargsZ, hcond.1, hcond.2, hZsub, hP0, hZfresh, by simp, htNd', htLen', htNotNs', htNotArgs', hArg'⟩
    subst hrA
    simp only [Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨t', by rw [hr1], ?_, ?_, trivial⟩
    · refine codeRel_trans (codeRel_emptyLocals hsr) (stateRel_trans ?_ (stateRel_trans hrelD hrelA))
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact codeInl_of_code_eq rfl (hrelD.2.1.trans hrelA.2.1).symm hci
  rw [if_neg hz0] at hev
  have ihB := ihBody vs (body, HolFiniteMapExact.empty.updateList (ns.zip vs)) body
    (HolFiniteMapExact.empty.updateList (ns.zip vs))
    (by rw [show crepExactEvalExpClassical s = evalCrepSemHOLExp s from
          funext (crepExactEvalExpClassical_eq s)]; exact hargs)
    (lookupCodeFiniteHOL_eq_holFinite _ _ _ _ _ _ hlk) rfl (by simp [hretsNodup]) hz0
  rcases hb : evalCrepSemHOLProgExact
      { decClockCrepSemHOL s with locals := HolFiniteMapExact.empty.updateList (ns.zip vs) } body
    with ⟨q, st⟩
  rw [hb] at hev
  have hq : q ≠ some .error ∧ contResHOLExact q = false ∧
      (∀ retvs, q = some (.return retvs) → rets.length = retvs.length) := by
    rcases q with _ | ⟨_ | _ | n | n | retvs | ex | ev⟩
    all_goals simp only at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm hne
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm hne
    · exact ⟨by simp, rfl, by simp⟩
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm hne
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm hne
    · refine ⟨by simp, rfl, fun rv h => ?_⟩
      simp only [Option.some.injEq, CrepResultHOLExact.return.injEq] at h
      subst h
      by_cases hl : retvs.length ≠ rets.length
      · rw [if_pos hl] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm hne
      · omega
    · exact ⟨by simp, rfl, by simp⟩
    · exact ⟨by simp, rfl, by simp⟩
  obtain ⟨hqne, hqcont, hqlen⟩ := hq
  have hsrD : crepInlineStateRelCodeExact
      { decClockCrepSemHOL s with locals := HolFiniteMapExact.empty.updateList (ns.zip vs) }
      { decClockCrepSemHOL t with locals := HolFiniteMapExact.empty.updateList (ns.zip vs) } := by
    obtain ⟨a, b, c, d, e, f, g, h, i⟩ := hsr
    exact ⟨a, b, c, d, by simp [decClockCrepSemHOL, e], f, g, h, i⟩
  obtain ⟨t1, ht1, hrel1, hci1, _⟩ := ihB q st inlFs
    { decClockCrepSemHOL t with locals := HolFiniteMapExact.empty.updateList (ns.zip vs) }
    (inlBag.erase fname) hb hqne hsub (submap_trans' (submap_erase _ _) hbag) hsrD rfl
    (codeInl_of_code_eq rfl rfl hci)
  have hu := CrepInlineUnreachElimEvaluate.unreachElimCorrect _ _ _ _ _ _ ⟨ht1, hqne, rfl⟩
  rw [updateList_eq_updateListEq] at hu
  have hu' : evalCrepSemHOLProgExact
      { decClockCrepSemHOL t with locals := HolFiniteMapExact.empty.updateListEq (ns.zip vs) }
      callee' = (q, t1) := by
    rw [← hcal]; exact hu
  obtain ⟨t2, ht2, hrel2, _⟩ := evaluateStateLocalsRelStrongExact callee' _ q t1
    { decClockCrepSemHOL { t with locals := (t.locals.updateListEq (trets.zip zeros)) } with
      locals := (HolFiniteMapExact.empty.updateListEq (trets.zip zeros)).updateListEq (ns.zip vs) }
    ⟨hu', hqne, fun k v h => by
      simp only [HolFiniteMapExact.lookup_updateListEq] at h ⊢
      exact submap_fupdateListHOL _ _ _ (fun k v h => by simp [HolFiniteMapExact.empty] at h) k v h,
     ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hconv : unreachElimHOLExact callee' =
      (callee', (unreachElimHOLExact (inlineProgHOLExact (inlBag.erase fname) body)).2) := by
    apply unreachElimConverge (inlineProgHOLExact (inlBag.erase fname) body)
    rw [← hcal]; rfl
  have hmapZ : trets.mapM ((HolFiniteMapExact.empty.updateListEq (trets.zip zeros)).updateListEq
      (ns.zip vs)).lookup = some zeros := by
    rw [list_mapM_congr _ (HolFiniteMapExact.empty.updateListEq (trets.zip zeros)).lookup trets
      (fun x hx => by
        simp only [HolFiniteMapExact.lookup_updateListEq]
        have := FLOOKUP_FUPDATE_LIST_HOL_not_mem
          (HolFiniteMapExact.empty.updateListEq (trets.zip zeros)).lookup (ns.zip vs) x
          (fun hm => by
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
            exact (htrFresh _ hx).2.2.1 (List.of_mem_zip he).1)
        simpa [FLOOKUP] using this)]
    exact CrepInlineTransformEoc.mapM_updateListEq_zip _ trets zeros htrNd hzl.symm
  obtain ⟨rP, sP, hPrun, hrel3, hmatch⟩ := wrappedTransformIf callee'
    { t with locals := (t.locals.updateListEq (trets.zip zeros)) } q t2 _ trets
    ((HolFiniteMapExact.empty.updateListEq (trets.zip zeros)).updateListEq (ns.zip vs))
    ⟨ht2, hconv, fun rv h => by rw [htrLen]; exact hqlen rv h,
     fun x hx => (htrFresh x hx).2.2.2.1, ⟨zeros, hmapZ⟩, htrNd, hqcont,
     by simp; omega, hqne⟩
  rw [show (if notBranchRetHOLExact callee' then CrepProgHOL.seq .tick (transformEocHOLExact trets callee')
      else .while (.const 1) (transformBranchHOLExact 0 trets callee')) = P from by
        rw [← hP]; rfl] at hPrun
  have hrPne : rP ≠ some .error := by
    rcases q with _ | ⟨_ | _ | n | n | retvs | ex | ev⟩ <;> simp at hmatch hqne hqcont
    all_goals first | (rw [hmatch.1]; simp) | (rw [hmatch]; simp)
  obtain ⟨hrA, hrel4, hpost⟩ := generalSimulateArgLoadStrongAllDruleExact _ argexps vs ns _ P rP sP
    tmps rA sA
    ⟨hargsZ, hcond.1, hcond.2, hZsub, hPrun, hZfresh, hrPne, htNd', htLen', htNotNs', htNotArgs',
      hArg'⟩
  subst hrA
  rcases q with _ | ⟨_ | _ | n | n | retvs | ex | ev⟩
  · simp [contResHOLExact] at hqcont
  · exact absurd rfl hqne
  · -- timeOut
    simp only at hmatch
    subst hmatch
    simp only [Prod.mk.injEq] at hev hW
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨t', by rw [hr1], ?_, codeInl_of_code_eq rfl
      (hrel2.2.1.trans (hrel3.2.1.trans (hrel4.2.1.trans hrelA.2.1))).symm hci1, trivial⟩
    exact codeRel_trans (codeRel_emptyLocals hrel1)
      (stateRel_trans hrel2 (stateRel_trans hrel3 (stateRel_trans hrel4 hrelA)))
  · simp [contResHOLExact] at hqcont
  · simp [contResHOLExact] at hqcont
  · -- return
    classical
    obtain ⟨hrP, hretT⟩ := hmatch
    subst hrP
    simp only at hW hpost hev
    obtain ⟨hFD, hFL⟩ := hpost
    by_cases hl : retvs.length ≠ rets.length
    · rw [if_pos hl] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm hne
    rw [if_neg hl] at hev
    rcases hrm : rets.mapM s.locals.lookup with _ | valsR
    · simp only [hrm, Prod.mk.injEq] at hev; exact absurd hev.1.symm hne
    simp only [hrm, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    have hsl : s.locals = t.locals := hls
    have hes : (trets.map CrepExpHOL.var).mapM (evalCrepSemHOLExp sA) = some retvs :=
      (lookupLocalsEqMapVarsHOL trets sA).symm.trans
        (foldl_res_var_zip_lookup_exact sP.locals _ sA.locals ns trets retvs hFL hretT
          (fun x hx => (htrFresh x hx).2.2.1))
    have hFD' : ∀ x y, x ∉ trets → t.locals.lookup x = some y → sA.locals.lookup x = some y := by
      intro x y hx hy
      apply hFD x y
      simp only [crepHolFdiff, crepHolFdom, hnotZ x hx, Option.isSome_none,
        Bool.false_eq_true, if_false, HolFiniteMapExact.lookup_updateListEq]
      have := FLOOKUP_FUPDATE_LIST_HOL_not_mem t.locals.lookup (trets.zip zeros) x
        (fun hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          exact hx (List.of_mem_zip he).1)
      simp only [FLOOKUP] at this
      rw [this]; exact hy
    have hdomS := mapM_some_isSome _ rets valsR hrm
    have hretsA : rets.mapM sA.locals.lookup = some valsR := by
      rw [← hrm]
      apply list_mapM_congr
      intro x hx
      have hsx := hdomS x hx
      cases hv : s.locals.lookup x with
      | none => rw [hv] at hsx; exact absurd hsx (by simp)
      | some y =>
          rw [hsl] at hv
          exact hFD' x y (fun hm => (htrFresh x hm).1 hx) hv
    have hW' : evalCrepSemHOLProgExact sA
        (crepNestedSeqHOL (panMap2 CrepProgHOL.assign rets (trets.map CrepExpHOL.var))) =
        (rW, sW) := by rw [nestedSeq_assigns]; exact hW
    obtain ⟨hrW, hrel5, hunch, hretW⟩ := CrepInlineNestedSeqAssign.evaluateNestedSeqAssignDrule
      rets sA (trets.map CrepExpHOL.var) retvs valsR rW sW
      ⟨hes, fun x hx hm => by rw [vars_map_var] at hm; exact (htrFresh x hm).1 hx, hretsA,
        by omega, hretsNodup, hW'⟩
    subst hrW
    refine ⟨t', by rw [hr1], ?_, ?_, ?_⟩
    · exact codeRel_trans hrel1 (stateRel_trans hrel2 (stateRel_trans hrel3
        (stateRel_trans hrel4 (stateRel_trans hrel5 hrelA))))
    · exact codeInl_of_code_eq rfl (hrel2.2.1.trans (hrel3.2.1.trans (hrel4.2.1.trans
        (hrel5.2.1.trans hrelA.2.1)))).symm hci1
    · show s.locals.updateListEq (rets.zip retvs) = t'.locals
      apply finmap_eq_of_submap_fdom
      · rw [hlocA, hsl]
        apply CrepInlineUpdateListLocals.submapFinishFlookup t.locals rets retvs sW.locals trets
        refine ⟨fun x y ⟨hx1, hx2, hy⟩ => ?_, fun x hx hm => (htrFresh x hm).1 hx,
          hretsNodup, hretW⟩
        rw [hunch x hx1]
        exact hFD' x y hx2 hy
      · have hdt := evaluateLocalsSameFdom'Exact _ t none t' ⟨by rw [hT0, hr1], Or.inl rfl⟩
        rw [← hdt, ← hsl]
        funext k
        simp only [crepHolFdom, HolFiniteMapExact.lookup_updateListEq]
        apply dom_fupdateListHOL
        intro e he
        exact hdomS e.1 (List.of_mem_zip he).1
  · -- exception
    simp only at hmatch
    subst hmatch
    simp only [Prod.mk.injEq] at hev hW
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨t', by rw [hr1], ?_, codeInl_of_code_eq rfl
      (hrel2.2.1.trans (hrel3.2.1.trans (hrel4.2.1.trans hrelA.2.1))).symm hci1, trivial⟩
    exact codeRel_trans (codeRel_emptyLocals hrel1)
      (stateRel_trans hrel2 (stateRel_trans hrel3 (stateRel_trans hrel4 hrelA)))
  · -- finalFfi
    simp only at hmatch
    subst hmatch
    simp only [Prod.mk.injEq] at hev hW
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨t', by rw [hr1], ?_, codeInl_of_code_eq rfl
      (hrel2.2.1.trans (hrel3.2.1.trans (hrel4.2.1.trans hrelA.2.1))).symm hci1, trivial⟩
    exact codeRel_trans (codeRel_emptyLocals hrel1)
      (stateRel_trans hrel2 (stateRel_trans hrel3 (stateRel_trans hrel4 hrelA)))

end CrepInlineCallCase

end Flapjack
