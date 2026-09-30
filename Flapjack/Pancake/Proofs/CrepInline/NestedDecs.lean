import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExact
namespace NestedDecsSupport

/-- Flapjack-specific re-export of the canonical state carrier roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end NestedDecsSupport

/-- HOL single_dec_evaluate: scope restoration changes only locals, which
state_rel intentionally excludes. The successful expression, updated-locals
body evaluation and non-Error premises are exactly the original premises;
the target declaration evaluation and related state are constructed. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "single_dec_evaluate"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem singleDecEvaluateExact {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (v : Nat) (e : CrepExpHOL width) (value : HolWordLab width)
    (he : evalCrepSemHOLExp s e = some value)
    (hp : evalCrepSemHOLProgExact
      {s with locals := s.locals.updateEq (v,value)} p = (r,s'))
    (_hnotError : r ≠ some .error) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact s (.dec v e p) = (r,t') ∧
      crepInlineStateRelExact s' t' := by
  refine ⟨{s' with locals := s'.locals.resVarEq (v,s.locals.lookup v)}, ?_, ?_⟩
  · rw [evalCrepSemHOLProgExact_dec_holShape, he]
    simp only [hp]
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- HOL nested_decs_evaluate, by induction on the declaration names.
Freshness transfers each remaining expression evaluation across the head
local update; singleDecEvaluateExact constructs the outer scoped evaluation. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "nested_decs_evaluate"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem nestedDecsEvaluateExact {width : Nat} [NeZero width] {σ : Type}
    (vs : List Nat) (es : List (CrepExpHOL width)) (p : CrepProgHOL width)
    (s : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (s' : CrepSemHOLState width σ) (vals : List (HolWordLab width))
    (he : es.mapM (evalCrepSemHOLExp s) = some vals)
    (hlen : vs.length = es.length) (hdist : vs.Pairwise (· ≠ ·))
    (hfresh : ∀ v ∈ vs, ∀ e ∈ es, v ∉ crepExpVarsHOL e)
    (hp : evalCrepSemHOLProgExact
      {s with locals := s.locals.updateListEq (vs.zip vals)} p = (r,s'))
    (hnotError : r ≠ some .error) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact s (nestedDecsHOL vs es p) = (r,t') ∧
      crepInlineStateRelExact s' t' := by
  induction vs generalizing es s vals with
  | nil =>
      have hes : es = [] := by cases es <;> simp_all
      subst es
      have hm : s.locals.updateListEq [] = s.locals := by
        apply HolFiniteMapExact.ext
        funext k
        rfl
      simp only [List.zip_nil_left, hm] at hp
      refine ⟨s', ?_, ?_⟩
      · simpa [nestedDecsHOL] using hp
      · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | cons v vs ih =>
      cases es with
      | nil => simp at hlen
      | cons e es =>
          cases hv : evalCrepSemHOLExp s e with
          | none => simp [List.mapM_cons, hv] at he
          | some value =>
              cases ht : es.mapM (evalCrepSemHOLExp s) with
              | none => simp [List.mapM_cons, hv, ht] at he
              | some values =>
                  have hvals : vals = value :: values := by
                    simpa [List.mapM_cons, hv, ht] using he.symm
                  subst vals
                  let u : CrepSemHOLState width σ :=
                    {s with locals := s.locals.updateEq (v,value)}
                  have htail : es.mapM (evalCrepSemHOLExp u) = some values := by
                    rw [OPT_MMAP_ALL_EQ (evalCrepSemHOLExp u)
                      (evalCrepSemHOLExp s) es]
                    · exact ht
                    · intro x hx
                      exact evalCrepSemHOLExp_updateLocals_eq_of_not_vars
                        s x v value (hfresh v (by simp) x (by simp [hx]))
                  have hm : s.locals.updateListEq ((v,value) :: vs.zip values) =
                      (s.locals.updateEq (v,value)).updateListEq (vs.zip values) := by
                    apply HolFiniteMapExact.ext
                    funext k
                    rfl
                  have hbody : evalCrepSemHOLProgExact
                      {u with locals := u.locals.updateListEq (vs.zip values)} p = (r,s') := by
                    simpa only [List.zip_cons_cons, hm] using hp
                  obtain ⟨t, htEval, htRel⟩ := ih es u values htail
                    (by simpa using hlen) hdist.tail
                    (fun n hn x hx => hfresh n (by simp [hn]) x (by simp [hx])) hbody
                  obtain ⟨out, hout, houtRel⟩ := singleDecEvaluateExact
                    (nestedDecsHOL vs es p) s r t v e value hv htEval hnotError
                  refine ⟨out, ?_, ?_⟩
                  · simpa only [nestedDecsHOL] using hout
                  · rcases htRel with ⟨a,b,c,d,e,f,g,h,i,j⟩
                    rcases houtRel with ⟨a',b',c',d',e',f',g',h',i',j'⟩
                    exact ⟨a.trans a',b.trans b',c.trans c',d.trans d',e.trans e',
                      f.trans f',g.trans g',h.trans h',i.trans i',j.trans j'⟩

end Flapjack.CrepInlineExact
