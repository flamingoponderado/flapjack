import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Structural

/-!
# crep_inline `evaluate_state_locals_rel_strong`: remaining atom cases

Counterpart of the atom branches of `cakeml/pancake/proofs/crep_inlineProofScript.sml:400-498`
(bead `flapjack-pxn.18.5.5.43.5.5`): Assign, Store, Store32, StoreByte,
StoreGlob, Raise, Return, Primitive, ExtCall and ShMem.  None has an induction
hypothesis.  `state_rel s t` makes `t` equal to `s with locals := t.locals`, so
the target run repeats the source run on the relocated locals.
-/

namespace Flapjack.CrepInlineExact

namespace StrongMoreAtomsSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end StrongMoreAtomsSupport

/-- Local support: the target of `state_rel s t` is `s` with `t`'s locals. -/
theorem target_eq {width : Nat} [NeZero width] {σ : Type}
    {s t : CrepSemHOLState width σ} (h : crepInlineStateRelExact s t) :
    ∃ tl, t = { s with locals := tl } :=
  ⟨t.locals, (withLocals_eq_of_stateRel h).symm⟩

/-- Local support: the continuing post when neither run changes its locals. -/
theorem post_locals_same {width : Nat} [NeZero width] {σ : Type}
    (s s' t t' : CrepSemHOLState width σ) (hs : s'.locals = s.locals) (ht : t'.locals = t.locals)
    (hloc : crepInlineLocalsRelExact s t) :
    crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t' := by
  refine ⟨fun k v h => ?_, ?_⟩
  · rw [ht]; rw [hs] at h; exact hloc k v h
  · unfold crepInlineLocalsExtRelExact; rw [hs, ht]

/-- Local support: the continuing post when both runs overwrite the same
    existing local with the same value. -/
private theorem post_locals_set {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ) (k : Nat) (w : HolWordLab width)
    (hk : (s.locals.lookup k).isSome) (hloc : crepInlineLocalsRelExact s t) :
    crepInlineLocalsRelExact { s with locals := s.locals.updateEq (k, w) }
        { t with locals := t.locals.updateEq (k, w) } ∧
      crepInlineLocalsExtRelExact s { s with locals := s.locals.updateEq (k, w) } t
        { t with locals := t.locals.updateEq (k, w) } := by
  refine ⟨localsRel_updateEq hloc k w, ?_⟩
  unfold crepInlineLocalsExtRelExact
  funext j
  simp only [crepHolFdiff, crepHolFdom, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  by_cases hjk : j = k
  · subst hjk; simp [hk]
  · simp only [hjk, if_false]
    rfl

/-- Local support: target expression evaluation on the relocated state. -/
private theorem eval_tl {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (tl : HolFiniteMapExact Nat (HolWordLab width))
    (hloc : crepInlineLocalsRelExact s { s with locals := tl })
    (e : CrepExpHOL width) (v : HolWordLab width) (h : evalCrepSemHOLExp s e = some v) :
    evalCrepSemHOLExp { s with locals := tl } e = some v :=
  evalOriginalExtendLocalsExact s e v tl h hloc

/-- Local support: `Assign`. -/
private theorem assignStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (n : Nat) (e : CrepExpHOL width) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.assign n e) s := by
  intro r s' t hev hne hloc hrel
  obtain ⟨tl, rfl⟩ := target_eq hrel
  rw [evalCrepSemHOLProgExact_assign, crepExactEvalExp_eq_eval] at hev
  rw [evalCrepSemHOLProgExact_assign, crepExactEvalExp_eq_eval]
  cases he : evalCrepSemHOLExp s e with
  | none => rw [he] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some w =>
      rw [he] at hev
      rw [eval_tl s tl hloc e w he]
      dsimp only at hev ⊢
      cases hn : s.locals.lookup n with
      | none => rw [hn] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
      | some x =>
          rw [hn] at hev
          have htn : tl.lookup n = some x := hloc n x hn
          simp only [htn]
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
          exact post_locals_set s { s with locals := tl } n w (by simp [hn]) hloc

/-- Local support: the three memory stores, uniformly. -/
private theorem storeLikeGoal {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (hshape : ∀ (u : CrepSemHOLState width σ) (tl : HolFiniteMapExact Nat (HolWordLab width)),
      (∀ r u', evalCrepSemHOLProgExact u p = (r, u') → r ≠ some .error →
        crepInlineLocalsRelExact u { u with locals := tl } →
        r = none ∧ ∃ m, u' = { u with memory := m } ∧
          evalCrepSemHOLProgExact { u with locals := tl } p =
            (none, { u with locals := tl, memory := m }))) :
    strongLocalsGoal p s := by
  intro r s' t hev hne hloc hrel
  obtain ⟨tl, rfl⟩ := target_eq hrel
  obtain ⟨rfl, m, rfl, hevt⟩ := hshape s tl r s' hev hne hloc
  exact ⟨_, hevt, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    post_locals_same s _ _ _ rfl rfl hloc⟩

/-- Local support: `Store`. -/
private theorem storeStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (dst src : CrepExpHOL width) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.store dst src) s := by
  refine storeLikeGoal _ s (fun u tl r u' hev hne hloc => ?_)
  rw [evalCrepSemHOLProgExact_store_holShape] at hev ⊢
  cases hd : evalCrepSemHOLExp u dst with
  | none => simp [hd] at hev; obtain ⟨rfl, rfl⟩ := hev; exact absurd rfl hne
  | some dv =>
      cases hs : evalCrepSemHOLExp u src with
      | none => simp [hd, hs] at hev; obtain ⟨rfl, rfl⟩ := hev; exact absurd rfl hne
      | some sv =>
          rw [eval_tl u tl hloc dst dv hd, eval_tl u tl hloc src sv hs]
          cases dv with
          | word adr =>
              simp only [hd, hs] at hev ⊢
              split at hev

              · rename_i m hm

                rw [hm]

                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev

                exact ⟨rfl, m, rfl, rfl⟩

              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne

/-- Local support: `Store32`. -/
private theorem store32StrongGoal {width : Nat} [NeZero width] {σ : Type}
    (dst src : CrepExpHOL width) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.store32 dst src) s := by
  refine storeLikeGoal _ s (fun u tl r u' hev hne hloc => ?_)
  rw [evalCrepSemHOLProgExact_store32_holShape] at hev ⊢
  cases hd : evalCrepSemHOLExp u dst with
  | none => simp [hd] at hev; obtain ⟨rfl, rfl⟩ := hev; exact absurd rfl hne
  | some dv =>
      cases hs : evalCrepSemHOLExp u src with
      | none => simp [hd, hs] at hev; obtain ⟨rfl, rfl⟩ := hev; exact absurd rfl hne
      | some sv =>
          rw [eval_tl u tl hloc dst dv hd, eval_tl u tl hloc src sv hs]
          cases dv with
          | word adr =>
              cases sv with
              | word w =>
                  simp only [hd, hs] at hev ⊢
                  split at hev

                  · rename_i m hm

                    rw [hm]

                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev

                    exact ⟨rfl, m, rfl, rfl⟩

                  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne

/-- Local support: `StoreByte`. -/
private theorem storeByteStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (dst src : CrepExpHOL width) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.storeByte dst src) s := by
  refine storeLikeGoal _ s (fun u tl r u' hev hne hloc => ?_)
  rw [evalCrepSemHOLProgExact_storeByte_holShape] at hev ⊢
  cases hd : evalCrepSemHOLExp u dst with
  | none => simp [hd] at hev; obtain ⟨rfl, rfl⟩ := hev; exact absurd rfl hne
  | some dv =>
      cases hs : evalCrepSemHOLExp u src with
      | none => simp [hd, hs] at hev; obtain ⟨rfl, rfl⟩ := hev; exact absurd rfl hne
      | some sv =>
          rw [eval_tl u tl hloc dst dv hd, eval_tl u tl hloc src sv hs]
          cases dv with
          | word adr =>
              cases sv with
              | word w =>
                  simp only [hd, hs] at hev ⊢
                  split at hev

                  · rename_i m hm

                    rw [hm]

                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev

                    exact ⟨rfl, m, rfl, rfl⟩

                  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne

/-- Local support: `StoreGlob`. -/
private theorem storeGlobStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (dst : BitVec 5) (src : CrepExpHOL width) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.storeGlob dst src) s := by
  intro r s' t hev hne hloc hrel
  obtain ⟨tl, rfl⟩ := target_eq hrel
  rw [evalCrepSemHOLProgExact_storeGlob_holShape] at hev ⊢
  cases hs : evalCrepSemHOLExp s src with
  | none => simp [hs] at hev; obtain ⟨rfl, rfl⟩ := hev; exact absurd rfl hne
  | some w =>
      rw [eval_tl s tl hloc src w hs]
      simp only [hs] at hev ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        post_locals_same s _ _ _ rfl rfl hloc⟩

/-- Local support: `Raise`. -/
private theorem raiseStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (ex : BitVec width) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.raise ex) s := by
  intro r s' t hev _ _ hrel
  rw [evalCrepSemHOLProgExact_raise] at hev
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel
  exact ⟨_, evalCrepSemHOLProgExact_raise t ex,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, trivial⟩

/-- Local support: `Return`. -/
private theorem returnStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.return es) s := by
  intro r s' t hev hne hloc hrel
  rw [evalCrepSemHOLProgExact_return] at hev ⊢
  cases hws : es.mapM (evalCrepSemHOLExp s) with
  | none => rw [hws] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some ws =>
      rw [hws] at hev
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      rw [evalOptmmapStateLocalsRelExact s es ws t ⟨hws, hrel, hloc⟩]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel
      exact ⟨_, rfl, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, trivial⟩

/-- Local support: a successful list of lookups transfers along `SUBMAP`. -/
theorem mapM_lookup_submap {β : Type} {f g : Nat → Option β}
    (hfg : ∀ k v, f k = some v → g k = some v) :
    ∀ (xs : List Nat) (vs : List β), xs.mapM f = some vs → xs.mapM g = some vs
  | [], _, h => h
  | x :: xs, vs, h => by
      simp only [List.mapM_cons] at h ⊢
      cases hx : f x with
      | none => simp [hx] at h
      | some y =>
          cases hr : xs.mapM f with
          | none => simp [hx, hr] at h
          | some ys =>
              rw [hfg x y hx, mapM_lookup_submap hfg xs ys hr]
              simpa [hx, hr] using h

/-- Local support: `FUPDATE_LIST` preserves `SUBMAP` for the same entries. -/
theorem submap_updateList {β : Type} :
    ∀ (entries : List (Nat × β)) (f g : Nat → Option β),
      (∀ k v, f k = some v → g k = some v) →
      ∀ k v, FUPDATE_LIST_HOL f entries k = some v → FUPDATE_LIST_HOL g entries k = some v
  | [], _, _, h => h
  | e :: es, f, g, h => by
      simp only [FUPDATE_LIST_HOL_cons]
      refine submap_updateList es _ _ (fun k v hk => ?_)
      simp only [FUPDATE_HOL] at hk ⊢
      by_cases hke : k = e.1
      · simp_all
      · simp only [hke, if_false] at hk ⊢; exact h k v hk

/-- Local support: updating existing keys keeps the domain. -/
theorem dom_updateList {β : Type} :
    ∀ (entries : List (Nat × β)) (f : Nat → Option β),
      (∀ e ∈ entries, (f e.1).isSome) →
      ∀ k, (FUPDATE_LIST_HOL f entries k).isSome = (f k).isSome
  | [], _, _, _ => rfl
  | e :: es, f, h, k => by
      simp only [FUPDATE_LIST_HOL_cons]
      rw [dom_updateList es _ (fun e' he' => ?_) k]
      · simp only [FUPDATE_HOL]
        by_cases hke : k = e.1
        · subst hke; simp [h e List.mem_cons_self]
        · simp [hke]
      · simp only [FUPDATE_HOL]
        by_cases hke : e'.1 = e.1
        · simp [hke]
        · simp only [hke, if_false]; exact h e' (List.mem_cons_of_mem _ he')

/-- Local support: `Primitive`. -/
private theorem primitiveStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (names : List Nat) (op : PrimOp) (args : List Nat) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.primitive names op args) s := by
  intro r s' t hev hne hloc hrel
  obtain ⟨tl, rfl⟩ := target_eq hrel
  rw [evalCrepSemHOLProgExact_primitive_holShape] at hev ⊢
  cases ha : args.mapM s.locals.lookup with
  | none => simp only [ha] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some ws =>
      have hta : args.mapM tl.lookup = some ws := mapM_lookup_submap hloc args ws ha
      simp only [ha] at hev
      simp only [hta]
      cases hp : crepPrimopHOLExact op ws with
      | none => simp only [hp] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
      | some results =>
          simp only [hp] at hev ⊢
          by_cases hc : names.length = results.length ∧
              (∀ v ∈ names, (s.locals.lookup v).isSome) ∧ names.Nodup
          · rw [if_pos hc] at hev
            have hct : names.length = results.length ∧
                (∀ v ∈ names, (tl.lookup v).isSome) ∧ names.Nodup := by
              refine ⟨hc.1, fun v hv => ?_, hc.2.2⟩
              have := hc.2.1 v hv
              cases hsv : s.locals.lookup v with
              | none => rw [hsv] at this; exact absurd this (by simp)
              | some x => rw [hloc v x hsv]; rfl
            rw [if_pos hct]
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
            have hkeys : ∀ e ∈ names.zip results, (s.locals.lookup e.1).isSome :=
              fun e he => hc.2.1 e.1 (List.of_mem_zip he).1
            refine ⟨fun k v hk => submap_updateList _ _ _ hloc k v hk, ?_⟩
            unfold crepInlineLocalsExtRelExact
            funext j
            simp only [crepHolFdiff, crepHolFdom, HolFiniteMapExact.lookup_updateListEq]
            simp only [dom_updateList _ _ hkeys j]
            by_cases hj : (s.locals.lookup j).isSome = true
            · simp [hj]
            · have hjn : j ∉ (names.zip results).map Prod.fst := by
                intro hm
                obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
                exact hj (hkeys e he)
              simp only [hj, Bool.false_eq_true, if_false]
              exact (FLOOKUP_FUPDATE_LIST_HOL_not_mem _ _ j hjn).symm
          · rw [if_neg hc] at hev
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne

/-- Local support: `ExtCall`. -/
private theorem extCallStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (fn : Flapjack.Basis.Pure.MlString.MlString) (c cl a al : Nat) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.extCall fn c cl a al) s := by
  intro r s' t hev hne hloc hrel
  obtain ⟨tl, rfl⟩ := target_eq hrel
  rw [evalCrepSemHOLProgExact_extCall_holShape] at hev ⊢
  have hrefl : crepInlineStateRelExact s' s' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases h1 : s.locals.lookup cl with
  | none => simp only [h1] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some v1 =>
  cases h2 : s.locals.lookup c with
  | none => simp only [h1, h2] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some v2 =>
  cases h3 : s.locals.lookup al with
  | none => simp only [h1, h2, h3] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some v3 =>
  cases h4 : s.locals.lookup a with
  | none => simp only [h1, h2, h3, h4] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some v4 =>
  rw [hloc cl v1 h1, hloc c v2 h2, hloc al v3 h3, hloc a v4 h4]
  rw [h1, h2, h3, h4] at hev
  rcases v1 with ⟨w1⟩; rcases v2 with ⟨w2⟩; rcases v3 with ⟨w3⟩; rcases v4 with ⟨w4⟩
  dsimp only at hev ⊢
  split at hev
  · rename_i cb ab hcb hab
    rw [hcb, hab]
    dsimp only at hev ⊢
    split at hev
    · rename_i ev hf
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
    · rename_i nf nb hf
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        post_locals_same s _ _ _ rfl rfl hloc⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne

/-- Local support: the continuing post when both runs overwrite the same
    existing local, with arbitrary other (non-local) field changes. -/
private theorem post_locals_set' {width : Nat} [NeZero width] {σ : Type}
    (s t s' t' : CrepSemHOLState width σ) (k : Nat) (w : HolWordLab width)
    (hs : s'.locals = s.locals.updateEq (k, w)) (ht : t'.locals = t.locals.updateEq (k, w))
    (hk : (s.locals.lookup k).isSome) (hloc : crepInlineLocalsRelExact s t) :
    crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t' := by
  have h := post_locals_set s t k w hk hloc
  unfold crepInlineLocalsRelExact crepInlineLocalsExtRelExact at h ⊢
  rw [hs, ht]
  exact h

/-- Local support: shared-memory loads on the relocated state. -/
private theorem shLoad_rel {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (addr : BitVec width) (nb : Nat) (s : CrepSemHOLState width σ)
    (tl : HolFiniteMapExact Nat (HolWordLab width))
    (hloc : crepInlineLocalsRelExact s { s with locals := tl })
    (hk : (s.locals.lookup name).isSome) :
    letI : DecidablePred s.shMemaddrs := fun a => Classical.propDecidable (s.shMemaddrs a)
    letI : DecidablePred ({ s with locals := tl } : CrepSemHOLState width σ).shMemaddrs :=
      fun a => Classical.propDecidable (s.shMemaddrs a)
    ∀ r s1, crepShMemLoadExactHOL name addr nb s = (r, s1) → r ≠ some .error →
      ∃ t1, crepShMemLoadExactHOL name addr nb { s with locals := tl } = (r, t1) ∧
        crepInlineStateRelExact s1 t1 ∧ strongLocalsPost r s s1 { s with locals := tl } t1 := by
  intro r s1 h hne
  unfold crepShMemLoadExactHOL at h ⊢
  dsimp only at h ⊢
  by_cases hnb : nb = 0
  · simp only [hnb, if_true] at h ⊢
    by_cases hsh : s.shMemaddrs addr
    · simp only [hsh, if_true] at h ⊢
      split at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          post_locals_set' s _ _ _ name _ rfl rfl hk hloc⟩
    · simp only [hsh, if_false] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact absurd rfl hne
  · simp only [hnb, if_false] at h ⊢
    by_cases hsh : s.shMemaddrs (panByteAlignHOL addr)
    · simp only [hsh, if_true] at h ⊢
      split at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          post_locals_set' s _ _ _ name _ rfl rfl hk hloc⟩
    · simp only [hsh, if_false] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact absurd rfl hne

/-- Local support: shared-memory stores on the relocated state. -/
private theorem shStore_rel {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (addr : BitVec width) (nb : Nat) (s : CrepSemHOLState width σ)
    (tl : HolFiniteMapExact Nat (HolWordLab width))
    (hloc : crepInlineLocalsRelExact s { s with locals := tl }) :
    letI : DecidablePred s.shMemaddrs := fun a => Classical.propDecidable (s.shMemaddrs a)
    letI : DecidablePred ({ s with locals := tl } : CrepSemHOLState width σ).shMemaddrs :=
      fun a => Classical.propDecidable (s.shMemaddrs a)
    ∀ r s1, crepShMemStoreExactHOL name addr nb s = (r, s1) → r ≠ some .error →
      ∃ t1, crepShMemStoreExactHOL name addr nb { s with locals := tl } = (r, t1) ∧
        crepInlineStateRelExact s1 t1 ∧ strongLocalsPost r s s1 { s with locals := tl } t1 := by
  intro r s1 h hne
  unfold crepShMemStoreExactHOL at h ⊢
  cases hn : s.locals.lookup name with
  | none => simp only [hn] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact absurd rfl hne
  | some v =>
      have htn : tl.lookup name = some v := hloc name v hn
      simp only [hn] at h
      simp only [htn]
      rcases v with ⟨value⟩
      dsimp only at h ⊢
      by_cases hnb : nb = 0
      · simp only [hnb, if_true] at h ⊢
        by_cases hsh : s.shMemaddrs addr
        · simp only [hsh, if_true] at h ⊢
          split at h
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
              post_locals_same s _ _ _ rfl rfl hloc⟩
        · simp only [hsh, if_false] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact absurd rfl hne
      · simp only [hnb, if_false] at h ⊢
        by_cases hsh : s.shMemaddrs (panByteAlignHOL addr)
        · simp only [hsh, if_true] at h ⊢
          split at h
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
              post_locals_same s _ _ _ rfl rfl hloc⟩
        · simp only [hsh, if_false] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact absurd rfl hne

/-- Local support: `ShMem`. -/
private theorem shMemStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (op : WordMemOp) (name : Nat) (ad : CrepExpHOL width) (s : CrepSemHOLState width σ) :
    strongLocalsGoal (.shMem op name ad) s := by
  classical
  intro r s' t hev hne hloc hrel
  obtain ⟨tl, rfl⟩ := target_eq hrel
  rw [evalCrepSemHOLProgExact_shMem_holShape] at hev ⊢
  cases ha : evalCrepSemHOLExp s ad with
  | none => simp only [ha] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some av =>
      rw [eval_tl s tl hloc ad av ha]
      simp only [ha] at hev
      rcases av with ⟨addr⟩
      dsimp only at hev ⊢
      cases hn : s.locals.lookup name with
      | none =>
          simp only [hn] at hev
          split at hev <;> (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne)
      | some v =>
          have htn : tl.lookup name = some v := hloc name v hn
          simp only [hn] at hev
          simp only [htn]
          have hk : (s.locals.lookup name).isSome := by simp [hn]
          have hload : ∀ nb, ∀ r' s1, crepShMemLoadExactHOL name addr nb s = (r', s1) → r' ≠ some .error →
              ∃ t1, crepShMemLoadExactHOL name addr nb { s with locals := tl } = (r', t1) ∧
                crepInlineStateRelExact s1 t1 ∧ strongLocalsPost r' s s1 { s with locals := tl } t1 :=
            fun nb => shLoad_rel name addr nb s tl hloc hk
          have hstore : ∀ nb, ∀ r' s1, crepShMemStoreExactHOL name addr nb s = (r', s1) →
              r' ≠ some .error →
              ∃ t1, crepShMemStoreExactHOL name addr nb { s with locals := tl } = (r', t1) ∧
                crepInlineStateRelExact s1 t1 ∧ strongLocalsPost r' s s1 { s with locals := tl } t1 :=
            fun nb => shStore_rel name addr nb s tl hloc
          cases op <;> simp only [crepIsLoadMemOp, if_true, if_false, Bool.false_eq_true,
            crepShMemOpExactHOL] at hev ⊢
          all_goals first
            | exact hload _ r s' hev hne
            | (rcases v with ⟨w⟩
               try simp only at hev ⊢
               exact hstore _ r s' hev hne)

/-- `Assign` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongAssignExact {width : Nat} [NeZero width] {σ : Type}
    (n : Nat) (e : CrepExpHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.assign n e) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.assign n e) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  assignStrongGoal n e s r s' t heval herror hlocals hstate

/-- `Store` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongStoreExact {width : Nat} [NeZero width] {σ : Type}
    (dst src : CrepExpHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.store dst src) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.store dst src) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  storeStrongGoal dst src s r s' t heval herror hlocals hstate

/-- `Store32` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongStore32Exact {width : Nat} [NeZero width] {σ : Type}
    (dst src : CrepExpHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.store32 dst src) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.store32 dst src) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  store32StrongGoal dst src s r s' t heval herror hlocals hstate

/-- `StoreByte` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongStoreByteExact {width : Nat} [NeZero width] {σ : Type}
    (dst src : CrepExpHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.storeByte dst src) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.storeByte dst src) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  storeByteStrongGoal dst src s r s' t heval herror hlocals hstate

/-- `StoreGlob` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongStoreGlobExact {width : Nat} [NeZero width] {σ : Type}
    (dst : BitVec 5) (src : CrepExpHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.storeGlob dst src) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.storeGlob dst src) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  storeGlobStrongGoal dst src s r s' t heval herror hlocals hstate

/-- `Raise` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongRaiseExact {width : Nat} [NeZero width] {σ : Type}
    (ex : BitVec width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.raise ex) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.raise ex) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  raiseStrongGoal ex s r s' t heval herror hlocals hstate

/-- `Return` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongReturnExact {width : Nat} [NeZero width] {σ : Type}
    (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.return es) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.return es) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  returnStrongGoal es s r s' t heval herror hlocals hstate

/-- `Primitive` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongPrimitiveExact {width : Nat} [NeZero width] {σ : Type}
    (names : List Nat) (op : PrimOp) (args : List Nat) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.primitive names op args) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.primitive names op args) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  primitiveStrongGoal names op args s r s' t heval herror hlocals hstate

/-- `ExtCall` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongExtCallExact {width : Nat} [NeZero width] {σ : Type}
    (fn : Flapjack.Basis.Pure.MlString.MlString) (c cl a al : Nat) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.extCall fn c cl a al) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.extCall fn c cl a al) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  extCallStrongGoal fn c cl a al s r s' t heval herror hlocals hstate

/-- `ShMem` case of HOL `evaluate_state_locals_rel_strong`; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongShMemExact {width : Nat} [NeZero width] {σ : Type}
    (op : WordMemOp) (name : Nat) (ad : CrepExpHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.shMem op name ad) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.shMem op name ad) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  shMemStrongGoal op name ad s r s' t heval herror hlocals hstate

end Flapjack.CrepInlineExact
