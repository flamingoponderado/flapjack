import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Assembly

/-!
# crep_inline `not_var_prog_flookup_eqn`

Counterpart of `cakeml/pancake/proofs/crep_inlineProofScript.sml:814-880`
(bead `flapjack-pxn.18.5.5.44.5.1`): a continuing run (`NONE`, `Break`,
`Continue`) leaves every local outside `var_prog p` unchanged.  HOL proves it
by `recInduct evaluate_ind`; as for the other crep_inline assemblies
(`EvaluateLocals/Assembly.lean`, "Induction principle and guard spellings"),
the motive is proved here for every program and state by structural recursion
plus an inner clock induction for `While`.  Only the final theorem is a HOL
port; the per-constructor steps are local support.
-/

namespace Flapjack.CrepInlineExact

namespace NotVarProgSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end NotVarProgSupport

/-- Local support: HOL's continuing-result condition. -/
private def contRes {width : Nat} [NeZero width] (r : Option (CrepResultHOLExact width)) : Prop :=
  match r with
  | none => True
  | some (.break _) => True
  | some (.continue _) => True
  | _ => False

/-- Local support: the motive. -/
private def nvMotive {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ) : Prop :=
  ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ) (x : Nat),
    evalCrepSemHOLProgExact s p = (r, s') → x ∉ crepVarProgHOLExact p → contRes r →
    s'.locals.lookup x = s.locals.lookup x

/-- Local support: zip updates leave other keys unchanged. -/
private theorem lookup_updateListEq_zip_not_mem' {β : Type} (m : HolFiniteMapExact Nat β)
    (xs : List Nat) (ys : List β) (k : Nat) (hk : k ∉ xs) :
    (m.updateListEq (xs.zip ys)).lookup k = m.lookup k := by
  rw [HolFiniteMapExact.lookup_updateListEq]
  apply FLOOKUP_FUPDATE_LIST_HOL_not_mem
  intro hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
  exact hk (List.of_mem_zip he).1

private theorem lookup_updateEq_ne {β : Type} (m : HolFiniteMapExact Nat β) (k x : Nat) (v : β)
    (h : x ≠ k) : (m.updateEq (k, v)).lookup x = m.lookup x := by
  simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h]

private theorem lookup_resVarEq_ne {β : Type} (m : HolFiniteMapExact Nat β) (k x : Nat)
    (o : Option β) (h : x ≠ k) : (m.resVarEq (k, o)).lookup x = m.lookup x := by
  cases o <;> simp [HolFiniteMapExact.lookup_resVarEq_none, HolFiniteMapExact.lookup_resVarEq_some,
    FDOMSUB_HOL, FUPDATE_HOL, h]

-- Local support tactic: close a branch whose evaluation result is known.
set_option hygiene false in
local macro "nv_close" : tactic =>
  `(tactic| (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
             first
               | rfl
               | exact hc.elim
               | (simp only [contRes] at hc)
               | skip))

private theorem nv_skip {width : Nat} [NeZero width] {σ : Type} (s : CrepSemHOLState width σ) :
    nvMotive (.skip : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_skip] at h
  nv_close

private theorem nv_break {width : Nat} [NeZero width] {σ : Type} (n : Nat)
    (s : CrepSemHOLState width σ) : nvMotive (.break n : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_break] at h
  nv_close

private theorem nv_continue {width : Nat} [NeZero width] {σ : Type} (n : Nat)
    (s : CrepSemHOLState width σ) : nvMotive (.continue n : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_continue] at h
  nv_close

private theorem nv_tick {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) : nvMotive (.tick : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_tick] at h
  split at h <;> nv_close

private theorem nv_raise {width : Nat} [NeZero width] {σ : Type} (e : BitVec width)
    (s : CrepSemHOLState width σ) : nvMotive (.raise e : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_raise] at h
  nv_close

private theorem nv_return {width : Nat} [NeZero width] {σ : Type} (es : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ) : nvMotive (.return es : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_return] at h
  split at h <;> nv_close

private theorem nv_assign {width : Nat} [NeZero width] {σ : Type} (n : Nat) (e : CrepExpHOL width)
    (s : CrepSemHOLState width σ) : nvMotive (.assign n e : CrepProgHOL width) s := by
  intro r s' x h hx hc
  have hxn : x ≠ n := fun heq => hx (by simp [crepVarProgHOLExact, heq])
  rw [evalCrepSemHOLProgExact_assign] at h
  split at h
  · nv_close
  · split at h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact lookup_updateEq_ne _ _ _ _ hxn
    · nv_close

private theorem nv_store {width : Nat} [NeZero width] {σ : Type} (a b : CrepExpHOL width)
    (s : CrepSemHOLState width σ) : nvMotive (.store a b : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_store_holShape] at h
  split at h
  · split at h <;> nv_close
  · nv_close

private theorem nv_store32 {width : Nat} [NeZero width] {σ : Type} (a b : CrepExpHOL width)
    (s : CrepSemHOLState width σ) : nvMotive (.store32 a b : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_store32_holShape] at h
  split at h
  · split at h <;> nv_close
  · nv_close

private theorem nv_storeByte {width : Nat} [NeZero width] {σ : Type} (a b : CrepExpHOL width)
    (s : CrepSemHOLState width σ) : nvMotive (.storeByte a b : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_storeByte_holShape] at h
  split at h
  · split at h <;> nv_close
  · nv_close

private theorem nv_storeGlob {width : Nat} [NeZero width] {σ : Type} (a : BitVec 5)
    (b : CrepExpHOL width) (s : CrepSemHOLState width σ) :
    nvMotive (.storeGlob a b : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_storeGlob_holShape] at h
  split at h <;> nv_close

private theorem nv_primitive {width : Nat} [NeZero width] {σ : Type} (names : List Nat)
    (op : PrimOp) (args : List Nat) (s : CrepSemHOLState width σ) :
    nvMotive (.primitive names op args : CrepProgHOL width) s := by
  intro r s' x h hx hc
  have hxn : x ∉ names := fun hm => hx (by simp [crepVarProgHOLExact, hm])
  rw [evalCrepSemHOLProgExact_primitive_holShape] at h
  split at h
  · split at h
    · split at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact lookup_updateListEq_zip_not_mem' _ _ _ _ hxn
      · nv_close
    · nv_close
  · nv_close

private theorem nv_extCall {width : Nat} [NeZero width] {σ : Type}
    (fn : Flapjack.Basis.Pure.MlString.MlString) (c cl a al : Nat) (s : CrepSemHOLState width σ) :
    nvMotive (.extCall fn c cl a al : CrepProgHOL width) s := by
  intro r s' x h _ hc
  rw [evalCrepSemHOLProgExact_extCall_holShape] at h
  repeat' (first | (split at h) | skip)
  all_goals nv_close

private theorem nv_shMemLoad {width : Nat} [NeZero width] {σ : Type} (n : Nat)
    (addr : BitVec width) (nb : Nat) (s : CrepSemHOLState width σ) [DecidablePred s.shMemaddrs]
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ) (x : Nat)
    (h : crepShMemLoadExactHOL n addr nb s = (r, s')) (hxn : x ≠ n) (hc : contRes r) :
    s'.locals.lookup x = s.locals.lookup x := by
  unfold crepShMemLoadExactHOL at h
  split at h <;> split at h <;> (try split at h) <;>
    (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
     first
       | rfl
       | exact hc.elim
       | exact lookup_updateEq_ne _ _ _ _ hxn)

private theorem nv_shMemStore {width : Nat} [NeZero width] {σ : Type} (n : Nat)
    (addr : BitVec width) (nb : Nat) (s : CrepSemHOLState width σ) [DecidablePred s.shMemaddrs]
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ) (x : Nat)
    (h : crepShMemStoreExactHOL n addr nb s = (r, s')) :
    s'.locals.lookup x = s.locals.lookup x := by
  unfold crepShMemStoreExactHOL at h
  split at h
  · split at h <;> split at h <;> (try split at h) <;> (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl

private theorem nv_shMem {width : Nat} [NeZero width] {σ : Type} (op : WordMemOp) (n : Nat)
    (ad : CrepExpHOL width) (s : CrepSemHOLState width σ) :
    nvMotive (.shMem op n ad : CrepProgHOL width) s := by
  classical
  intro r s' x h hx hc
  have hxn : x ≠ n := fun heq => hx (by simp [crepVarProgHOLExact, heq])
  have key : ∀ addr : BitVec width, crepShMemOpExactHOL op n addr s = (r, s') →
      s'.locals.lookup x = s.locals.lookup x := by
    intro addr h
    cases op <;> simp only [crepShMemOpExactHOL] at h
    all_goals first
      | exact nv_shMemLoad n addr _ s r s' x h hxn hc
      | exact nv_shMemStore n addr _ s r s' x h
  rw [evalCrepSemHOLProgExact_shMem_holShape] at h
  split at h
  · split at h
    · split at h
      · exact key _ h
      · nv_close
    · split at h
      · exact key _ h
      · nv_close
  · nv_close

private theorem nv_dec {width : Nat} [NeZero width] {σ : Type} (v : Nat) (e : CrepExpHOL width)
    (body : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ u : CrepSemHOLState width σ, nvMotive body u) :
    nvMotive (.dec v e body) s := by
  intro r s' x h hx hc
  have hxv : x ≠ v := fun heq => hx (by simp [crepVarProgHOLExact, heq])
  have hxb : x ∉ crepVarProgHOLExact body := fun hm => hx (by simp [crepVarProgHOLExact, hm])
  rw [evalCrepSemHOLProgExact_dec_holShape] at h
  split at h
  · rename_i val _
    rcases hb : evalCrepSemHOLProgExact { s with locals := s.locals.updateEq (v, val) } body
      with ⟨r0, st⟩
    rw [hb] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    show (st.locals.resVarEq (v, s.locals.lookup v)).lookup x = s.locals.lookup x
    rw [lookup_resVarEq_ne _ _ _ _ hxv, ih _ r0 st x hb hxb hc]
    exact lookup_updateEq_ne _ _ _ _ hxv
  · nv_close

private theorem nv_seq {width : Nat} [NeZero width] {σ : Type} (c1 c2 : CrepProgHOL width)
    (s : CrepSemHOLState width σ)
    (ih1 : ∀ u : CrepSemHOLState width σ, nvMotive c1 u)
    (ih2 : ∀ u : CrepSemHOLState width σ, nvMotive c2 u) :
    nvMotive (.seq c1 c2) s := by
  intro r s' x h hx hc
  have h1 : x ∉ crepVarProgHOLExact c1 := fun hm => hx (by simp [crepVarProgHOLExact, hm])
  have h2 : x ∉ crepVarProgHOLExact c2 := fun hm => hx (by simp [crepVarProgHOLExact, hm])
  rw [evalCrepSemHOLProgExact_seq_fixClockFree] at h
  rcases hs : evalCrepSemHOLProgExact s c1 with ⟨r0, s1⟩
  rw [hs] at h
  cases r0 with
  | none =>
      rw [ih2 s1 r s' x h h2 hc, ih1 s none s1 x hs h1 trivial]
  | some y =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ih1 s _ _ x hs h1 hc

private theorem nv_ite {width : Nat} [NeZero width] {σ : Type} (c : CrepExpHOL width)
    (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih1 : ∀ u : CrepSemHOLState width σ, nvMotive c1 u)
    (ih2 : ∀ u : CrepSemHOLState width σ, nvMotive c2 u) :
    nvMotive (.ite c c1 c2) s := by
  intro r s' x h hx hc
  have h1 : x ∉ crepVarProgHOLExact c1 := fun hm => hx (by simp [crepVarProgHOLExact, hm])
  have h2 : x ∉ crepVarProgHOLExact c2 := fun hm => hx (by simp [crepVarProgHOLExact, hm])
  rw [evalCrepSemHOLProgExact_ite] at h
  split at h
  · split at h
    · exact ih1 s r s' x h h1 hc
    · exact ih2 s r s' x h h2 hc
  · nv_close

private theorem nv_while {width : Nat} [NeZero width] {σ : Type} (e : CrepExpHOL width)
    (c : CrepProgHOL width) (ihc : ∀ u : CrepSemHOLState width σ, nvMotive c u) :
    ∀ s : CrepSemHOLState width σ, nvMotive (.while e c) s := by
  have step : ∀ s : CrepSemHOLState width σ,
      (∀ s1 : CrepSemHOLState width σ, s1.clock < s.clock → nvMotive (.while e c) s1) →
      nvMotive (.while e c) s := by
    intro s ih r s' x h hx hc
    have hxc : x ∉ crepVarProgHOLExact c := fun hm => hx (by simp [crepVarProgHOLExact, hm])
    rw [evalCrepSemHOLProgExact_while_holShape] at h
    split at h
    · split at h
      · split at h
        · nv_close
        · rename_i hck
          rcases hb : evalCrepSemHOLProgExact (decClockCrepSemHOL s) c with ⟨r0, s1⟩
          rw [hb] at h
          dsimp only at h
          have hlt : s1.clock < s.clock := by
            have hle := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) c
            rw [hb] at hle
            simp only [decClockCrepSemHOL_clock'] at hle
            omega
          have hbody : contRes r0 → s1.locals.lookup x = s.locals.lookup x := fun hc0 =>
            ihc (decClockCrepSemHOL s) r0 s1 x hb hxc hc0
          rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
          · rw [ih s1 hlt r s' x h hx hc, hbody trivial]
          · simp only [exitLoopCrepResult] at h; nv_close
          · simp only [exitLoopCrepResult] at h; nv_close
          · cases n with
            | zero => obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hbody trivial
            | succ n =>
                simp only [exitLoopCrepResult] at h
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hbody trivial
          · cases n with
            | zero => rw [ih s1 hlt r s' x h hx hc, hbody trivial]
            | succ n =>
                simp only [exitLoopCrepResult] at h
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hbody trivial
          · simp only [exitLoopCrepResult] at h; nv_close
          · simp only [exitLoopCrepResult] at h; nv_close
          · simp only [exitLoopCrepResult] at h; nv_close
      · nv_close
    · nv_close
  have main : ∀ (n : Nat) (s : CrepSemHOLState width σ), s.clock ≤ n →
      nvMotive (.while e c) s := by
    intro n
    induction n with
    | zero => intro s hs; exact step s (fun s1 h1 => absurd h1 (by omega))
    | succ k ih => intro s hs; exact step s (fun s1 h1 => ih s1 (by omega))
  exact fun s => main s.clock s (Nat.le_refl _)

private theorem nv_call {width : Nat} [NeZero width] {σ : Type}
    (ri : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fn : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (ih : ∀ rts eid handler, ri = some (rts, some (eid, handler)) →
      ∀ u : CrepSemHOLState width σ, nvMotive handler u) :
    nvMotive (.call ri fn args) s := by
  intro r s' x h hx hc
  have hxr : ∀ rts hnd, ri = some (rts, hnd) → x ∉ rts := by
    rintro rts (_ | ⟨eid, hp⟩) rfl hm <;> exact hx (by simp [crepVarProgHOLExact, hm])
  rw [evalCrepSemHOLProgExact_call_holShape] at h
  split at h
  · split at h
    · split at h
      · nv_close
      · split at h
        · nv_close
        · split at h
          · nv_close
          · nv_close
          · nv_close
          · split at h
            · nv_close
            · split at h
              · nv_close
              · split at h
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                  exact lookup_updateListEq_zip_not_mem' _ _ _ _ (hxr _ _ rfl)
                · nv_close
          · split at h
            · nv_close
            · nv_close
            · split at h
              · have hh := ih _ _ _ rfl _ r s' x h
                  (fun hm => hx (by simp [crepVarProgHOLExact, hm])) hc
                exact hh
              · nv_close
          · nv_close
    · nv_close
  · nv_close

private theorem nv_all {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), nvMotive p s
  | .skip, s => nv_skip s
  | .break n, s => nv_break n s
  | .continue n, s => nv_continue n s
  | .tick, s => nv_tick s
  | .store a b, s => nv_store a b s
  | .store32 a b, s => nv_store32 a b s
  | .storeByte a b, s => nv_storeByte a b s
  | .storeGlob a b, s => nv_storeGlob a b s
  | .raise e, s => nv_raise e s
  | .assign n e, s => nv_assign n e s
  | .primitive names op args, s => nv_primitive names op args s
  | .extCall f a b c d, s => nv_extCall f a b c d s
  | .shMem op n a, s => nv_shMem op n a s
  | .return values, s => nv_return values s
  | .seq a b, s => nv_seq a b s (fun u => nv_all a u) (fun u => nv_all b u)
  | .ite cond a b, s => nv_ite cond a b s (fun u => nv_all a u) (fun u => nv_all b u)
  | .dec n e body, s => nv_dec n e body s (fun u => nv_all body u)
  | .while e c, s => nv_while e c (fun u => nv_all c u) s
  | .call none f args, s => nv_call none f args s (fun _ _ _ h => by cases h)
  | .call (some (rts, none)) f args, s => nv_call _ f args s (fun _ _ _ h => by simp at h)
  | .call (some (rts, some (eid, handler))) f args, s =>
      nv_call _ f args s (fun _ _ _ h => by
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl⟩ := h
        exact fun u => nv_all handler u)
termination_by p => sizeOf p

/-- Exact HOL `not_var_prog_flookup_eqn` (`crep_inlineProofScript.sml:814-824`):
    `¬MEM x (var_prog p)` is `x ∉ crepVarProgHOLExact p`, HOL's
    `(case r of ...) = T` is the displayed `match` proposition, and `FLOOKUP` is
    `lookup` on the finite-support locals. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_var_prog_flookup_eqn"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem notVarProgFlookupEqnExact {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ) (x : Nat) :
      evalCrepSemHOLProgExact s p = (r, s') ∧
        x ∉ crepVarProgHOLExact p ∧
        (match (generalizing := false) r with
         | none => True
         | some (.break _) => True
         | some (.continue _) => True
         | _ => False) →
      s'.locals.lookup x = s.locals.lookup x := by
  intro ⟨h, hx, hc⟩
  exact nv_all p s r s' x h hx hc

end Flapjack.CrepInlineExact
