import Flapjack.HolRef
import Flapjack.Misc.LprefixLub
import Flapjack.Pancake.Semantics.PanSem.Semantics
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockIoEventsMono

/-!
# pan_globals: `LUB_IMAGE_SUC` (the `semantics_init_call` group)

Counterpart of `cakeml/pancake/proofs/pan_globalsProofScript.sml:2663-2710`
(bead `flapjack-pxn.18.5.2.22.3.2.3`), the LUB helper of `semantics_init_call`, and `semantics_init_call`
(`:2712-2799`, bead `flapjack-pxn.18.5.2.22.3.2.4`).
HOL's `LUB` is the `lprefix_lub` overload of `build_lprefix_lub`
(`lprefix_lubScript.sml:560`), rendered as `HolLList.buildLprefixLub`.  A set
`IMAGE f 𝕌(:num)` is the predicate `fun l => ∃ k, l = f k`, exactly as in the
tagged panSem `semantics_def`.
-/

namespace Flapjack

open HolLList

/-- Exact HOL `LUB_IMAGE_SUC[local]` (`pan_globalsProofScript.sml:2663-2665`):
    `(∀x. LPREFIX (f x) (f (SUC x))) ⇒
     LUB (IMAGE f 𝕌(:num)) = LUB (IMAGE (f o SUC) 𝕌(:num))`.
    HOL's proof: `IMP_build_lprefix_lub_EQ` with both images `lprefix_chain`s
    (by `LPREFIX_TRANS` along the monotone sequence) and both `lprefix_rel`
    directions. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "LUB_IMAGE_SUC"]
theorem lubImageSuc {α : Type} (f : Nat → HolLList α)
    (h : ∀ x, lprefix (f x) (f (Nat.succ x))) :
    buildLprefixLub (fun l => ∃ k, l = f k) =
      buildLprefixLub (fun l => ∃ k, l = (f ∘ Nat.succ) k) := by
  have mono : ∀ i d, lprefix (f i) (f (i + d)) := by
    intro i d
    induction d with
    | zero => exact lprefix_refl _
    | succ d ih => exact lprefix_trans ih (h (i + d))
  have cmp : ∀ i j, lprefix (f i) (f j) ∨ lprefix (f j) (f i) := by
    intro i j
    rcases Nat.le_total i j with hij | hji
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact Or.inl (mono i d)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
      exact Or.inr (mono j d)
  apply IMP_build_lprefix_lub_EQ
  · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact cmp i j
  · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact cmp (i + 1) (j + 1)
  · rintro _ ⟨k, rfl⟩; exact ⟨f (k + 1), ⟨k, rfl⟩, h k⟩
  · rintro _ ⟨k, rfl⟩; exact ⟨f (k + 1), ⟨k + 1, rfl⟩, lprefix_refl _⟩

open Flapjack.Pancake.PanLang (MlS ProgHOL ShapeHOL)
open PanSemStateFiniteExact

namespace SemInitSupport
/-- Same-module canonical witness for the finite-map qualifier of
    `semanticsInitCall`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness


theorem finmap_ext {α β : Type} {m n : HolFiniteMapExact α β} (h : m.lookup = n.lookup) :
    m = n := by
  cases m; cases n; cases h; rfl

/-- The code field is preserved by `evaluate` (HOL `evaluate_invariants`). -/
theorem eval_code {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (p : ProgHOL width) :
    (evaluateHOLFiniteState s p).2.code = s.code := by
  classical
  have h := evaluateInvariantsHOLFinite p (PanPropsEvalStateFiniteExact.ofPanSemFinite s)
    _ _ rfl
  have hc := h.2.2.2.2.2.2.1
  simp only [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at hc
  exact hc

/-- A tail call never ends in `NONE`, `Break` or `Continue`, and a `Return`
    value has the callee's declared return shape. -/
theorem callNone_result {width : Nat} {σ : Type} [NeZero width]
    (u : PanSemStateFiniteExact width σ) (f : MlS) (args : List (Pancake.PanLang.ExpHOL width)) :
    (evaluateHOLFiniteState u (.call none f args)).1 ≠ none ∧
    (evaluateHOLFiniteState u (.call none f args)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.call none f args)).1 ≠ some .continue ∧
    (∀ v, (evaluateHOLFiniteState u (.call none f args)).1 = some (.returned v) →
      ∃ ps b rs, u.code.lookup f = some (ps, b, rs) ∧
        shapeEqHOL (shapeOfHOLExact v) rs = true) := by
  classical
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · rename_i values _
    split
    · simp
    · rename_i body callee rshape hlk
      have hex := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hlk
      have hcode : ∃ ps, u.code.lookup f = some (ps, body, rshape) := by
        unfold lookupCodeHOLExact at hex
        split at hex
        · simp at hex
        · rename_i ps b rs hc
          split at hex
          · simp only [Option.some.injEq, Prod.mk.injEq] at hex
            obtain ⟨rfl, -, rfl⟩ := hex
            exact ⟨ps, hc⟩
          · simp at hex
      obtain ⟨ps, hps⟩ := hcode
      split
      · simp
      · split <;> (try split) <;> simp_all
        exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, by assumption⟩

theorem lookup_init {width : Nat} [NeZero width]
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (f : MlS) (b : ProgHOL width) (rs : ShapeHOL)
    (h : code.lookup f = some ([], b, rs)) :
    lookupCodeHOLFinite code.lookup f [] = some (b, HolFiniteMapExact.empty, rs) := by
  unfold lookupCodeHOLFinite
  split
  · rename_i hn
    simp [lookupCodeHOLExact, h] at hn
  · rename_i b' c' r' hs
    simp only [lookupCodeHOLExact, h] at hs
    simp at hs
    obtain ⟨rfl, hc, rfl⟩ := hs
    congr
    exact hc.symm

/-- One clock tick of the initial call: running `start` from `s` at clock
    `c + 1` agrees in result and FFI with running `start'` from `s'` at `c`. -/
theorem step {width : Nat} {σ : Type} [NeZero width]
    (s s' : PanSemStateFiniteExact width σ) (start start' : MlS)
    (body body' : ProgHOL width) (args' : List (MlS × ShapeHOL)) (rshape : ShapeHOL)
    (h1 : s.code.lookup start = some ([], .seq body (.call none start' []), rshape))
    (h2 : s.code.lookup start' = some (args', body', rshape))
    (h3 : ∀ k, evaluateHOLFiniteState { s with locals := HolFiniteMapExact.empty, clock := k } body =
      (none, { s' with clock := k }))
    (c : Nat) :
    (evaluateHOLFiniteState { s with clock := c + 1 } (.call none start [])).1 =
        (evaluateHOLFiniteState { s' with clock := c } (.call none start' [])).1 ∧
      (evaluateHOLFiniteState { s with clock := c + 1 } (.call none start [])).2.ffi =
        (evaluateHOLFiniteState { s' with clock := c } (.call none start' [])).2.ffi := by
  classical
  have hcode' : s'.code = s.code := by
    have := eval_code { s with locals := HolFiniteMapExact.empty, clock := 0 } body
    rw [h3 0] at this
    exact this
  have hB := callNone_result { s' with clock := c } start' []
  have hentry : callEntryStateHOLFinite { s with clock := c + 1 } HolFiniteMapExact.empty =
      { s with locals := HolFiniteMapExact.empty, clock := c } := rfl
  have hinner : evaluateHOLFiniteState
      (callEntryStateHOLFinite { s with clock := c + 1 } HolFiniteMapExact.empty)
      (.seq body (.call none start' [])) =
      evaluateHOLFiniteState { s' with clock := c } (.call none start' []) := by
    rw [hentry, evaluateHOLFiniteState_seq_line780, h3 c]
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite { s with clock := c + 1 }
      (h := fun address => Classical.propDecidable (({ s with clock := c + 1 } :
        PanSemStateFiniteExact width σ).memaddrs address)) [] = some [] := by
    simp [evalListHOLFinite, evalListHOLExact]
  rw [hargs]
  dsimp only
  rw [lookup_init _ start _ _ h1]
  dsimp only
  rw [if_neg (by simp), hinner]
  rcases hBe : evaluateHOLFiniteState { s' with clock := c } (.call none start' []) with ⟨r, st⟩
  rw [hBe] at hB
  obtain ⟨hn, hb, hc, hret⟩ := hB
  rcases r with _ | ⟨_ | _ | _ | _ | v | ⟨e, v⟩ | ev⟩
  · exact absurd rfl hn
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd rfl hb
  · exact absurd rfl hc
  · obtain ⟨ps, b, rs, hl, hsh⟩ := hret v rfl
    have : rs = rshape := by
      rw [hcode'] at hl
      rw [h2] at hl
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      exact hl.2.2.symm
    subst this
    simp [hsh, emptyLocalsHOLFinite]
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem step0 {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (start : MlS) (b : ProgHOL width) (rshape : ShapeHOL)
    (h1 : s.code.lookup start = some ([], b, rshape)) :
    (evaluateHOLFiniteState { s with clock := 0 } (.call none start [])).1 = some .timeOut ∧
      (evaluateHOLFiniteState { s with clock := 0 } (.call none start [])).2.ffi = s.ffi := by
  classical
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite { s with clock := 0 }
      (h := fun address => Classical.propDecidable (({ s with clock := 0 } :
        PanSemStateFiniteExact width σ).memaddrs address)) [] = some [] := by
    simp [evalListHOLFinite, evalListHOLExact]
  rw [hargs]
  dsimp only
  rw [lookup_init _ start _ _ h1]
  simp [emptyLocalsHOLFinite]

theorem sem_tail_congr {P Q : HolBehaviour → Prop} {x y : HolLList HolIoEvent}
    (hPQ : P = Q) (hxy : x = y) :
    (match holOptionSome P with
     | some r => r
     | none => HolBehaviour.diverge x) =
    (match holOptionSome Q with
     | some r => r
     | none => HolBehaviour.diverge y) := by
  subst hPQ; subst hxy; rfl

end SemInitSupport

open SemInitSupport HolLList in
/-- Exact HOL `semantics_init_call` (`pan_globalsProofScript.sml:2712-2718`):

    ```
    FLOOKUP s.code start = SOME ([],Seq body (TailCall start' []),rshape) ∧
    FLOOKUP s.code start' = SOME (args', body', rshape) ∧
    (∀k. evaluate (body,s with <| locals := FEMPTY; clock := k|>) =
         (NONE,s' with clock := k)) ∧
    s'.ffi.io_events = s.ffi.io_events
    ⇒ semantics s start = semantics s' start'
    ```

    The free HOL variables are bound in order of occurrence.  `FLOOKUP` is
    `.lookup` on the finite-support `code`, `TailCall` is the panLang overload
    `Call NONE` (`panLangScript.sml:127`), `FEMPTY` is `HolFiniteMapExact.empty`,
    `evaluate` is `evaluateHOLFiniteState`, and `semantics` is the tagged panSem
    `semantics_def`.  The proof (untagged `SemInitSupport.step`) shows that
    running `start` from `s` at clock `k + 1` agrees in result and FFI with
    running `start'` from `s'` at clock `k`.  The `Fail`, `Terminate` and
    `Diverge` branches of `semantics` then follow; the last uses the tagged
    `LUB_IMAGE_SUC` with the tagged `evaluate_add_clock_io_events_mono`.  As in
    the Lean proof, HOL's io-event hypothesis is retained but not needed. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "semantics_init_call"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem semanticsInitCall {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (start : MlS) (body : ProgHOL width) (start' : MlS)
    (rshape : ShapeHOL) (args' : List (MlS × ShapeHOL)) (body' : ProgHOL width)
    (s' : PanSemStateFiniteExact width σ) :
    s.code.lookup start = some ([], .seq body (.call none start' []), rshape) ∧
      s.code.lookup start' = some (args', body', rshape) ∧
      (∀ k, evaluateHOLFiniteState { s with locals := HolFiniteMapExact.empty, clock := k } body =
        (none, { s' with clock := k })) ∧
      s'.ffi.ioEvents = s.ffi.ioEvents →
    semantics s start = semantics s' start' := by
  classical
  rintro ⟨h1, h2, h3, _h4⟩
  have hS := step s s' start start' body body' args' rshape h1 h2 h3
  have h0 := step0 s start _ rshape h1
  let A : Nat → _ := fun k => evaluateHOLFiniteState { s with clock := k } (.call none start [])
  let B : Nat → _ := fun k => evaluateHOLFiniteState { s' with clock := k } (.call none start' [])
  -- Fail condition
  let good : Option (PanSemResultExact width) → Prop := fun r => match r with
      | some .timeOut => False
      | some (.finalFfi _) => False
      | some (.returned _) => False
      | _ => True
  have hgood0 : ¬ good (A 0).1 := by
    show ¬ good (evaluateHOLFiniteState { s with clock := 0 } (.call none start [])).1
    rw [h0.1]; exact id
  have hcond : (∃ k, good (A k).1) ↔ (∃ k, good (B k).1) := by
    constructor
    · rintro ⟨k, hk⟩
      cases k with
      | zero => exact absurd hk hgood0
      | succ k =>
          refine ⟨k, ?_⟩
          have e := (hS k).1
          change good (evaluateHOLFiniteState { s' with clock := k } (.call none start' [])).1
          rw [← e]; exact hk
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      have e := (hS k).1
      change good (evaluateHOLFiniteState { s with clock := k + 1 } (.call none start [])).1
      rw [e]; exact hk
  -- Diverge LUB
  have hmono : ∀ x, lprefix (fromList (A x).2.ffi.ioEvents) (fromList (A (x + 1)).2.ffi.ioEvents) := by
    intro x
    rw [lprefix_fromList]
    exact panPropsEvaluateAddClockIoEventsMono (.call none start []) { s with clock := x } 1
  have hlub : buildLprefixLub (fun l => ∃ k, l = fromList (A k).2.ffi.ioEvents) =
      buildLprefixLub (fun l => ∃ k, l = fromList (B k).2.ffi.ioEvents) := by
    rw [lubImageSuc (fun k => fromList (A k).2.ffi.ioEvents) hmono]
    congr
    funext l
    apply propext
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, by simp only [Function.comp]; rw [(hS k).2]⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, by simp only [Function.comp]; rw [(hS k).2]⟩
  unfold semantics
  dsimp only
  split
  · rename_i hA
    rw [if_pos]
    exact hcond.mp hA
  · rename_i hA
    rw [if_neg]
    rotate_left
    · exact fun h => hA (hcond.mpr h)
    refine sem_tail_congr ?_ hlub
    funext res
    apply propext
    constructor
    · rintro ⟨k, t, r, outcome, hk, hm, hres⟩
      cases k with
      | zero =>
          have e := h0.1
          rw [hk] at e
          subst e
          exact (hm : False).elim
      | succ k =>
          obtain ⟨e1, e2⟩ := hS k
          rw [hk] at e1 e2
          refine ⟨k, (evaluateHOLFiniteState { s' with clock := k } (.call none start' [])).2,
            r, outcome, Prod.ext e1.symm rfl, hm, ?_⟩
          rw [hres, e2]
    · rintro ⟨k, t, r, outcome, hk, hm, hres⟩
      obtain ⟨e1, e2⟩ := hS k
      rw [hk] at e1 e2
      refine ⟨k + 1, (evaluateHOLFiniteState { s with clock := k + 1 } (.call none start [])).2,
        r, outcome, Prod.ext e1 rfl, hm, ?_⟩
      rw [hres, e2]


end Flapjack
