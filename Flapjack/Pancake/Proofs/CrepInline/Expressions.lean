import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExact

/-- Flapjack-specific list infrastructure: transport a successful mapM using
only elementwise successful-result preservation, not equality on failures. -/
theorem mapMSuccessTransport {α β : Type} (f g : α → Option β)
    (xs : List α) (ys : List β)
    (ih : ∀ x ∈ xs, ∀ y, f x = some y → g x = some y)
    (h : xs.mapM f = some ys) : xs.mapM g = some ys := by
  induction xs generalizing ys with
  | nil => simpa using h
  | cons x xs ihxs =>
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, hx, ht] at h
      | some tail =>
        have hg := ih x (by simp) y hx
        have htail := ihxs tail (fun x hx => ih x (by simp [hx])) ht
        simpa only [List.mapM_cons, hg, htail, hx, ht] using h

namespace ExpressionLocalsSupport
/-- Flapjack-specific canonical state roundtrip re-export. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end ExpressionLocalsSupport

/-- Successful exact expression evaluation survives a SUBMAP extension of
locals. This is the original success-only HOL statement, not evaluator equality. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_original_extend_locals"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code, locals])
  (words_as_type_indexed_bitvec)]
theorem evalOriginalExtendLocalsExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (e : CrepExpHOL width) (wl : HolWordLab width)
    (locals : HolFiniteMapExact Nat (HolWordLab width))
    (heval : evalCrepSemHOLExp s e = some wl)
    (hsub : ∀ key value, s.locals.lookup key = some value → locals.lookup key = some value) :
    evalCrepSemHOLExp {s with locals := locals} e = some wl := by
  classical
  induction e using evalCrepSemHOLExp.induct generalizing wl with
  | case1 value => simpa only [evalCrepSemHOLExp] using heval
  | case2 name =>
    simp only [evalCrepSemHOLExp] at heval ⊢
    exact hsub name wl heval
  | case3 address ih =>
    simp only [evalCrepSemHOLExp] at heval ⊢
    cases ha : evalCrepSemHOLExp s address with
    | none => simp [ha] at heval
    | some value => simpa only [ih value ha, ha] using heval
  | case4 address ih =>
    simp only [evalCrepSemHOLExp] at heval ⊢
    cases ha : evalCrepSemHOLExp s address with
    | none => simp [ha] at heval
    | some value => simpa only [ih value ha, ha] using heval
  | case5 address ih =>
    simp only [evalCrepSemHOLExp] at heval ⊢
    cases ha : evalCrepSemHOLExp s address with
    | none => simp [ha] at heval
    | some value => simpa only [ih value ha, ha] using heval
  | case6 address => simpa only [evalCrepSemHOLExp] using heval
  | case7 operator expressions ih =>
    simp only [evalCrepSemHOLExp] at heval ⊢
    cases hm : expressions.mapM (evalCrepSemHOLExp s) with
    | none => simp [hm] at heval
    | some values =>
      have ht := mapMSuccessTransport (evalCrepSemHOLExp s)
        (evalCrepSemHOLExp {s with locals := locals}) expressions values ih hm
      simpa only [ht, hm] using heval
  | case8 operator expressions ih =>
    simp only [evalCrepSemHOLExp] at heval ⊢
    cases hm : expressions.mapM (evalCrepSemHOLExp s) with
    | none => simp [hm] at heval
    | some values =>
      have ht := mapMSuccessTransport (evalCrepSemHOLExp s)
        (evalCrepSemHOLExp {s with locals := locals}) expressions values ih hm
      simpa only [ht, hm] using heval
  | case9 operator left right ihl ihr =>
    simp only [evalCrepSemHOLExp] at heval ⊢
    cases hl : evalCrepSemHOLExp s left with
    | none => simp [hl] at heval
    | some lv =>
      cases hr : evalCrepSemHOLExp s right with
      | none => simp [hl,hr] at heval
      | some rv => simpa only [ihl lv hl, ihr rv hr, hl, hr] using heval
  | case10 operator left right ihl ihr =>
    simp only [evalCrepSemHOLExp] at heval ⊢
    cases hl : evalCrepSemHOLExp s left with
    | none => simp [hl] at heval
    | some lv =>
      cases hr : evalCrepSemHOLExp s right with
      | none => simp [hl,hr] at heval
      | some rv => simpa only [ihl lv hl, ihr rv hr, hl, hr] using heval
  | case11 => simpa only [evalCrepSemHOLExp] using heval
  | case12 => simpa only [evalCrepSemHOLExp] using heval

end Flapjack.CrepInlineExact
