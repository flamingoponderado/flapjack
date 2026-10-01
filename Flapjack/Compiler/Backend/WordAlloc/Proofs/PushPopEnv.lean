import Flapjack.Compiler.Backend.WordAlloc.Proofs.EnvFrame
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackEq

/-!
# Word allocation `push_env`/`pop_env` frame lemmas

Counterpart of `word_allocProofScript.sml:515-563, 596-617, 710-722, 892-904`:
the stack-swap facts consumed by the `Call`/`Alloc` cases of
`evaluate_apply_colour`, stated with wordProps `s_key_eq`/`s_val_eq`.
-/

namespace Flapjack.WordAlloc

open WordSemStackEq

namespace PushPopEnvWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end PushPopEnvWitnesses

open PushPopEnvWitnesses

/-- Exact HOL `push_env_s_val_eq` (`word_allocProofScript.sml:515-563`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "push_env_s_val_eq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnvSValEq {width : Nat} [NeZero width] {C F : Type}
    (st cst : WordSemStateFiniteExact width C F) (x x' y y' : Spt (WordLocW width))
    (f : Nat → Nat) (b b' : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    ∀ tperm : Nat → Nat → Nat,
      st.handler = cst.handler ∧
      st.stack = cst.stack ∧
      st.localsSize = cst.localsSize ∧
      sptDomain y = (fun key => ∃ source, sptDomain x source ∧ f source = key) ∧
      (∀ a c, sptDomain x a → sptDomain x c → f a = f c → a = c) ∧
      sptDomain y' = (fun key => ∃ source, sptDomain x' source ∧ f source = key) ∧
      (∀ a c, sptDomain x' a → sptDomain x' c → f a = f c → a = c) ∧
      strongLocalsRel f (sptDomain x) x y ∧
      (match b with
        | none => b' = none
        | some (_w, _h, l1, l2) =>
            match b' with
            | none => False
            | some (_a, _b, c, d) => c = l1 ∧ d = l2) →
      ∃ perm,
        (let (l, _permute) := wordSemEnvToList y cst.permute
         let (l', permute') := wordSemEnvToList x perm
         permute' = tperm ∧ l'.map (fun (a, b) => (f a, b)) = l ∧
           ∀ a c, a ∈ l'.map Prod.fst ∧ c ∈ l'.map Prod.fst ∧ f a = f c → a = c) ∧
        sValEq (WordSemStateFiniteExact.pushEnv (x', x) b { st with permute := perm }).stack
          (WordSemStateFiniteExact.pushEnv (y', y) b' cst).stack := by
  rintro tperm ⟨hh, hs, hls, hdom, hinj, -, -, hrel, hb⟩
  have hperm := envToListPerm y x f cst.permute tperm ⟨hdom, hinj, hrel⟩
  rcases hy : wordSemEnvToList y cst.permute with ⟨l, pm⟩
  rw [hy] at hperm
  obtain ⟨perm', hperm'⟩ := hperm
  rcases hx : wordSemEnvToList x perm' with ⟨l', pm'⟩
  rw [hx] at hperm'
  obtain ⟨htp, hmap⟩ := hperm'
  have hkeys := envToListKeys x perm'
  rw [hx] at hkeys
  have hx' := hx
  simp only [wordSemEnvToList, Prod.mk.injEq] at hx'
  obtain ⟨hl', hpm'⟩ := hx'
  refine ⟨perm', ⟨by simpa only [hpm'] using htp, by simpa only [hl'] using hmap, ?_⟩, ?_⟩
  · rintro a c ⟨ha, hc, hac⟩
    rw [hl'] at ha hc
    have ha' : sptDomain x a := by rw [← hkeys]; exact ha
    have hc' : sptDomain x c := by rw [← hkeys]; exact hc
    exact hinj a c ha' hc' hac
  · have hsnd : l'.map Prod.snd = l.map Prod.snd := by
      rw [← hmap, List.map_map]; rfl
    cases b with
    | none =>
        subst hb
        simp only [WordSemStateFiniteExact.pushEnv, hx, hy]
        refine ⟨by rw [hs]; exact of_eq_true (sValEqRefl _), ?_⟩
        exact (sFrameValEqDef2 _ _ _ _ _ _ _ _).mpr ⟨hsnd, rfl, hls⟩
    | some bb =>
        obtain ⟨w, h, l1, l2⟩ := bb
        cases b' with
        | none => exact absurd hb (by simp)
        | some bb' =>
            obtain ⟨a', b'', c, d⟩ := bb'
            obtain ⟨rfl, rfl⟩ := hb
            simp only [WordSemStateFiniteExact.pushEnv, hx, hy]
            refine ⟨by rw [hs]; exact of_eq_true (sValEqRefl _), ?_⟩
            exact (sFrameValEqDef2 _ _ _ _ _ _ _ _).mpr ⟨hsnd, by rw [hh], hls⟩

private theorem zipFstSnd {α β : Type} (e : List (α × β)) :
    (e.map Prod.fst).zip (e.map Prod.snd) = e := by
  induction e with
  | nil => rfl
  | cons p e ih => simp [ih]

/-- Exact HOL `s_key_eq_val_eq_pop_env` (`word_allocProofScript.sml:596-617`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "s_key_eq_val_eq_pop_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem sKeyEqValEqPopEnv {width : Nat} [NeZero width] {C F : Type}
    (s s' : WordSemStateFiniteExact width C F) (n : Option Nat)
    (lsz ls : List (Nat × WordLocW width)) (opt : Option (Nat × Nat × Nat))
    (keys vals : List (WordSemStackFrame width)) :
    WordSemStateFiniteExact.popEnv s = some s' ∧
      sKeyEq s.stack (.stackFrame n lsz ls opt :: keys) ∧
      sValEq s.stack vals →
    ∃ lsz' ls' rest,
      vals = .stackFrame n lsz' ls' opt :: rest ∧
      s'.locals = sptUnion (sptFromAList ((ls.map Prod.fst).zip (ls'.map Prod.snd)))
        (sptFromAList lsz) ∧
      sKeyEq s'.stack keys ∧
      sValEq s'.stack rest ∧
      (match opt with
        | none => s'.handler = s.handler
        | some (h, _l1, _l2) => s'.handler = h) := by
  rintro ⟨hpop, hk, hv⟩
  unfold WordSemStateFiniteExact.popEnv at hpop
  cases hst : s.stack with
  | nil => rw [hst] at hk; exact absurd hk (by simp [sKeyEq])
  | cons fr rest0 =>
      rw [hst] at hk hv hpop
      rcases fr with ⟨m, e0, e, h0⟩
      obtain ⟨hkrest, hkf⟩ := hk
      rw [sFrameKeyEqDef2] at hkf
      obtain ⟨hfst, rfl, rfl, rfl⟩ := hkf
      cases vals with
      | nil => exact absurd hv (by simp [sValEq])
      | cons v rest =>
          obtain ⟨hvrest, hvf⟩ := hv
          rcases v with ⟨n'', x1, x2, y''⟩
          rw [sFrameValEqDef2] at hvf
          obtain ⟨hsnd, rfl, rfl⟩ := hvf
          have he : e = (ls.map Prod.fst).zip (x2.map Prod.snd) := by
            rw [← hfst, ← hsnd, zipFstSnd]
          refine ⟨x1, x2, rest, rfl, ?_⟩
          cases h0 with
          | none =>
              simp only [Option.some.injEq] at hpop
              subst hpop
              exact ⟨by rw [he], hkrest, hvrest, rfl⟩
          | some hh =>
              obtain ⟨h1, l1, l2⟩ := hh
              simp only [Option.some.injEq] at hpop
              subst hpop
              exact ⟨by rw [he], hkrest, hvrest, rfl⟩

/-- Exact HOL `pop_env_frame` (`word_allocProofScript.sml:710-722`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "pop_env_frame"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem popEnvFrame {width : Nat} [NeZero width] {C F : Type}
    (r' y' y'' : WordSemStateFiniteExact width C F) (st' : List (WordSemStackFrame width)) :
    sValEq r'.stack st' ∧
      sKeyEq y'.stack y''.stack ∧
      WordSemStateFiniteExact.popEnv { r' with stack := st' } = some y'' ∧
      WordSemStateFiniteExact.popEnv r' = some y' →
    wordStateEqRel y' y'' := by
  rintro ⟨hv, hk, hpop2, hpop1⟩
  unfold WordSemStateFiniteExact.popEnv at hpop1 hpop2
  cases hst : r'.stack with
  | nil => rw [hst] at hpop1; cases hpop1
  | cons fr rest =>
      rw [hst] at hv hpop1
      cases st' with
      | nil => exact absurd hv (by simp [sValEq])
      | cons fr2 rest2 =>
          obtain ⟨hvrest, hvf⟩ := hv
          rcases fr with ⟨m, e0, e, h0⟩
          rcases fr2 with ⟨m2, e02, e2, h2⟩
          rw [sFrameValEqDef2] at hvf
          obtain ⟨-, rfl, rfl⟩ := hvf
          simp only at hpop2
          cases h0 with
          | none =>
              simp only [Option.some.injEq] at hpop1 hpop2
              subst hpop1 hpop2
              have hrest := sValAndKeyEq rest rest2 ⟨hvrest, hk⟩
              subst hrest
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl⟩
          | some hh =>
              obtain ⟨hn, l1, l2⟩ := hh
              simp only [Option.some.injEq] at hpop1 hpop2
              subst hpop1 hpop2
              have hrest := sValAndKeyEq rest rest2 ⟨hvrest, hk⟩
              subst hrest
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `s_key_eq_push_env_imp_MAP_FST` (`word_allocProofScript.sml:892-904`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "s_key_eq_push_env_imp_MAP_FST"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem sKeyEqPushEnvImpMapFst {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (x' x'' : Spt (WordLocW width))
    (o0 : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (n' : Option Nat) (bb l : List (Nat × WordLocW width)) (opt : Option (Nat × Nat × Nat))
    (ls : List (WordSemStackFrame width)) (ll : List (Nat × WordLocW width))
    (res : Nat → Nat → Nat) :
    sKeyEq (WordSemStateFiniteExact.pushEnv (x', x'') o0 s).stack
        (.stackFrame n' bb l opt :: ls) ∧
      wordSemEnvToList x'' s.permute = (ll, res) →
    ll.map Prod.fst = l.map Prod.fst ∧
      (fun k => k ∈ bb.map Prod.fst) = sptDomain x' := by
  rintro ⟨hk, he⟩
  have hdom : (fun k => k ∈ (sptToAList x').map Prod.fst) = sptDomain x' := by
    funext k
    apply propext
    simp only [List.mem_map, sptDomain]
    constructor
    · rintro ⟨⟨a, v⟩, hm, rfl⟩
      simp [(sptToAList_mem_iff_lookup x' a v).mp hm]
    · intro hk'
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk'
      exact ⟨(k, v), (sptToAList_mem_iff_lookup x' k v).mpr hv, rfl⟩
  cases o0 with
  | none =>
      simp only [WordSemStateFiniteExact.pushEnv, he] at hk
      obtain ⟨-, hf⟩ := hk
      rw [sFrameKeyEqDef2] at hf
      obtain ⟨hfst, -, rfl, -⟩ := hf
      exact ⟨hfst, hdom⟩
  | some o =>
      obtain ⟨_, _, l1, l2⟩ := o
      simp only [WordSemStateFiniteExact.pushEnv, he] at hk
      obtain ⟨-, hf⟩ := hk
      rw [sFrameKeyEqDef2] at hf
      obtain ⟨hfst, -, rfl, -⟩ := hf
      exact ⟨hfst, hdom⟩

end Flapjack.WordAlloc
