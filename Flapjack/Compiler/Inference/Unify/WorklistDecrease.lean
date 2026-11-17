module

public import Flapjack.Compiler.Inference.Unify.WorklistRelation
public import Flapjack.Compiler.Inference.Unify.ComputationalWf.Step
public import Flapjack.Compiler.Inference.Unify.ComputationalWalk.Range
public import Flapjack.Compiler.Inference.Unify.ComputationalWalk.Order
public import Flapjack.HOL.Transfer.Fmsp.Operations
public import Flapjack.HOL.Unification.TcallUnif.SubstVars

@[expose] public section

/-! Source unifier step decreases its paired-worklist relation. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

private theorem replaceBag {α : Type} (r : α → α → Prop) (base rep : Bag α) (e : α)
    (hb : finiteBag base) (hr : finiteBag rep) (h : ∀ x, bagIn x rep → r x e) :
    bagMultisetStep r (bagUnion rep base) (bagInsert e base) := by
  refine ⟨finiteBagUnion rep hr base hb, finiteBagInsert base hb e, e, rep, base, rfl, ?_, h⟩
  funext x
  by_cases hx : x = e <;> simp [bagUnion, bagInsert, emptyBag, hx]

private theorem replaceTwo {α : Type} (r : α → α → Prop) (base left right : Bag α) (a b : α)
    (hb : finiteBag base) (hl : finiteBag left) (hr : finiteBag right)
    (ha : ∀ x, bagIn x left → r x a) (hc : ∀ x, bagIn x right → r x b) :
    Relation.TransGen (bagMultisetStep r)
      (bagUnion left (bagUnion right base)) (bagInsert a (bagInsert b base)) := by
  have one := replaceBag r (bagUnion right base) left a (finiteBagUnion right hr base hb) hl ha
  have two := replaceBag r base right b hb hr hc
  have context : bagMultisetStep r (bagInsert a (bagUnion right base))
      (bagInsert a (bagInsert b base)) := by
    rcases two with ⟨_, _, e, rep, res, he1, he2, hrep⟩
    refine ⟨finiteBagInsert _ (finiteBagUnion right hr base hb) a,
      finiteBagInsert _ (finiteBagInsert base hb b) a, e, rep, bagInsert a res, ?_, ?_, hrep⟩
    · rw [he1]
      funext x
      by_cases hx : x = a <;> simp [bagUnion, bagInsert, hx, Nat.add_assoc]
    · rw [he2]
      funext x
      by_cases hx : x = a
      · subst x
        simp [bagUnion, bagInsert, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [bagUnion, bagInsert, hx]
  have h := (Relation.TransGen.single one).tail context
  simpa [(bagUnionInsert a left (bagUnion right base)).1] using h

private theorem appBag (s : Spt InferT) (a b : InferT) (left right xs ys : List InferT)
    (rest : List (List InferT × List InferT)) (x y : Nat)
    (hw : cwfs s) (ha : tcwalkModel s a = .app xs x) (hb : tcwalkModel s b = .app ys y) :
    Relation.TransGen (bagMultisetStep (walkstarR (sp2fm (sptMap encodeInferT s))))
      (pflat ((xs, ys) :: (left, right) :: rest))
      (pflat ((a :: left, b :: right) :: rest)) := by
  let rel : Term Atom → Term Atom → Prop := walkstarR (sp2fm (sptMap encodeInferT s))
  have hleft : ∀ t, bagIn t (bagOfList (xs.map encodeInferT)) → rel t (encodeInferT a) := by
    intro t ht
    rw [bagInBagOfList, List.mem_map] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact walkstarOpthModel s a i xs x ⟨hw, ha, hi⟩
  have hright : ∀ t, bagIn t (bagOfList (ys.map encodeInferT)) → rel t (encodeInferT b) := by
    intro t ht
    rw [bagInBagOfList, List.mem_map] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact walkstarOpthModel s b i ys y ⟨hw, hb, hi⟩
  rw [pflatEqn, pflat, pflatCons2]
  exact replaceTwo rel _ _ _ _ _ (finitePflat _) (finiteBagOfList _) (finiteBagOfList _) hleft hright

private theorem encodedInsert (s : Spt InferT) (v : Nat) (t : InferT) :
    (sp2fm (sptInsert v t s)).map2 (fun p => encodeInferT p.2) =
      ((sp2fm s).map2 (fun p => encodeInferT p.2)).updateEq (v, encodeInferT t) := by
  apply HolFiniteMapExact.ext_lookup
  intro k
  by_cases h : k = v
  · subst k
    simp [HolFiniteMapExact.lookup_map2, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, sp2fm, sptLookup_sptInsert_same]
  · simp [HolFiniteMapExact.lookup_map2, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, sp2fm, sptLookup_sptInsert_ne, h]

private theorem insertSubstVars (s : Spt InferT) (v : Nat) (t : InferT)
    (fresh : ¬ sptDomain s v) :
    substVars ((sp2fm (sptInsert v t s)).map2 (fun p => encodeInferT p.2)) =
      substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) ∪ {v} ∪ vars (encodeInferT t) := by
  rw [encodedInsert, substVarsFupdate]
  congr 1
  congr 1
  have hnone : sptLookup v s = none := by
    cases h : sptLookup v s with
    | none => rfl
    | some x => exact (fresh ((sptDomain_iff_lookup s v).2 ⟨x, h⟩)).elim
  congr 1
  apply HolFiniteMapExact.ext_lookup
  intro k
  by_cases h : k = v
  · subst k
    simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, HolFiniteMapExact.lookup_map2, sp2fm, hnone]
  · simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]

private theorem walkVarsBound (s : Spt InferT) (input output : InferT)
    (hw : cwfs s) (he : tcwalkModel s input = output) :
    Set.Subset (vars (encodeInferT output))
      (Set.union (substVars ((sp2fm s).map2 (fun p => encodeInferT p.2))) (vars (encodeInferT input))) := by
  intro key hk
  rcases tcwalkRangeVarsModel s input output ⟨hw, he⟩ hk with hr | hi
  · exact Or.inl (Or.inr hr)
  · exact Or.inr hi

private theorem tailsRelation (s s' : Spt InferT) (a b : InferT) (left right : List InferT)
    (rest : List (List InferT × List InferT)) (hw : cwfs s) (hw' : cwfs s')
    (sub : (sp2fm s).submap (sp2fm s'))
    (bound : Set.Subset (substVars ((sp2fm s').map2 (fun p => encodeInferT p.2)))
      (Set.union (substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)))
        (cplistVars ((a :: left, b :: right) :: rest)))) :
    worklistR (s', (left, right) :: rest) (s, (a :: left, b :: right) :: rest) := by
  refine ⟨hw', hw, sub, ?_, Or.inl ?_⟩
  · intro k hk
    rcases hk with hk | hk
    · exact bound hk
    · right
      change ((isvars left k ∨ isvars right k) ∨ cplistVars rest k) at hk
      change (((vars (encodeInferT a) k ∨ isvars left k) ∨
        (vars (encodeInferT b) k ∨ isvars right k)) ∨ cplistVars rest k)
      tauto
  · rw [pflat, pflatCons2]
    exact mltBagInsert2 _ _ _ _ (finitePflat _)

private theorem insertSubmap (s : Spt InferT) (v : Nat) (t : InferT)
    (fresh : ¬ sptDomain s v) : (sp2fm s).submap (sp2fm (sptInsert v t s)) := by
  intro k value found
  by_cases eq : k = v
  · subst k
    exact (fresh ((sptDomain_iff_lookup s v).2 ⟨value, found⟩)).elim
  · change sptLookup k (sptInsert v t s) = some value
    change sptLookup k s = some value at found
    simpa [sptLookup_sptInsert_ne v k t s eq] using found

private theorem insertBound (s : Spt InferT) (v : Nat) (t a b : InferT)
    (left right : List InferT) (rest : List (List InferT × List InferT))
    (hw : cwfs s) (ha : tcwalkModel s a = .uvar v) (hb : tcwalkModel s b = t) :
    Set.Subset (substVars ((sp2fm (sptInsert v t s)).map2 (fun p => encodeInferT p.2)))
      (Set.union (substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)))
        (cplistVars ((a :: left, b :: right) :: rest))) := by
  have fresh := (tcwalkEqInferTuvarModel s a v ⟨hw, ha⟩).1
  have av := walkVarsBound s a (.uvar v) hw ha
  have bv := walkVarsBound s b t hw hb
  rw [insertSubstVars s v t fresh]
  intro k hk
  change ((substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨ k = v) ∨ vars (encodeInferT t) k) at hk
  change substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨
    (((vars (encodeInferT a) k ∨ isvars left k) ∨
      (vars (encodeInferT b) k ∨ isvars right k)) ∨ cplistVars rest k)
  have hvar : vars (encodeInferT (.uvar v)) v := by simp [encodeInferT, vars]
  have h1 := av hvar
  have h2 := bv
  rcases hk with (old | eq) | ht
  · exact Or.inl old
  · subst k
    exact h1.elim Or.inl (fun h => Or.inr (Or.inl (Or.inl (Or.inl h))))
  · exact (h2 ht).elim Or.inl (fun h => Or.inr (Or.inl (Or.inr (Or.inl h))))

private theorem insertBoundSwap (s : Spt InferT) (v : Nat) (t a b : InferT)
    (left right : List InferT) (rest : List (List InferT × List InferT))
    (hw : cwfs s) (ha : tcwalkModel s a = t) (hb : tcwalkModel s b = .uvar v) :
    Set.Subset (substVars ((sp2fm (sptInsert v t s)).map2 (fun p => encodeInferT p.2)))
      (Set.union (substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)))
        (cplistVars ((a :: left, b :: right) :: rest))) := by
  intro k hk
  have bound := insertBound s v t b a right left rest hw hb ha hk
  change substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨
    (((vars (encodeInferT b) k ∨ isvars right k) ∨
      (vars (encodeInferT a) k ∨ isvars left k)) ∨ cplistVars rest k) at bound
  change substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨
    (((vars (encodeInferT a) k ∨ isvars left k) ∨
      (vars (encodeInferT b) k ∨ isvars right k)) ∨ cplistVars rest k)
  tauto

private theorem tailsSame (s : Spt InferT) (a b : InferT) (left right : List InferT)
    (rest : List (List InferT × List InferT)) (hw : cwfs s) :
    worklistR (s, (left, right) :: rest) (s, (a :: left, b :: right) :: rest) := by
  apply tailsRelation s s a b left right rest hw hw (HolFiniteMapExact.submap_refl _)
  intro k hk
  exact Or.inl hk

private theorem insertRel (s : Spt InferT) (v : Nat) (t a b : InferT)
    (left right : List InferT) (rest : List (List InferT × List InferT))
    (hw : cwfs s) (hw' : cwfs (sptInsert v t s))
    (ha : tcwalkModel s a = .uvar v) (hb : tcwalkModel s b = t) :
    worklistR (sptInsert v t s, (left, right) :: rest) (s, (a :: left, b :: right) :: rest) := by
  apply tailsRelation s _ a b left right rest hw hw'
  · exact insertSubmap s v t (tcwalkEqInferTuvarModel s a v ⟨hw, ha⟩).1
  · exact insertBound s v t a b left right rest hw ha hb

private theorem insertRelSwap (s : Spt InferT) (v : Nat) (t a b : InferT)
    (left right : List InferT) (rest : List (List InferT × List InferT))
    (hw : cwfs s) (hw' : cwfs (sptInsert v t s))
    (ha : tcwalkModel s a = t) (hb : tcwalkModel s b = .uvar v) :
    worklistR (sptInsert v t s, (left, right) :: rest) (s, (a :: left, b :: right) :: rest) := by
  apply tailsRelation s _ a b left right rest hw hw'
  · exact insertSubmap s v t (tcwalkEqInferTuvarModel s b v ⟨hw, hb⟩).1
  · exact insertBoundSwap s v t a b left right rest hw ha hb

private theorem appsRelation (s : Spt InferT) (a b : InferT) (left right xs ys : List InferT)
    (rest : List (List InferT × List InferT)) (x y : Nat)
    (hw : cwfs s) (ha : tcwalkModel s a = .app xs x) (hb : tcwalkModel s b = .app ys y) :
    worklistR (s, (xs, ys) :: (left, right) :: rest) (s, (a :: left, b :: right) :: rest) := by
  refine ⟨hw, hw, HolFiniteMapExact.submap_refl _, ?_, Or.inl (appBag s a b left right xs ys rest x y hw ha hb)⟩
  have va := walkVarsBound s a (.app xs x) hw ha
  have vb := walkVarsBound s b (.app ys y) hw hb
  intro k hk
  change substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨
    (((isvars xs k ∨ isvars ys k) ∨ ((isvars left k ∨ isvars right k) ∨ cplistVars rest k))) at hk
  change substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨
    (((vars (encodeInferT a) k ∨ isvars left k) ∨
      (vars (encodeInferT b) k ∨ isvars right k)) ∨ cplistVars rest k)
  have va' : isvars xs k →
      substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨ vars (encodeInferT a) k := by
    intro hi
    apply va
    change vars (encodeInferT (.app xs x)) k
    simpa [encodeInferT, vars, varsEncodeInferTs] using hi
  have vb' : isvars ys k →
      substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨ vars (encodeInferT b) k := by
    intro hi
    apply vb
    change vars (encodeInferT (.app ys y)) k
    simpa [encodeInferT, vars, varsEncodeInferTs] using hi
  tauto

private theorem stepDecreases : ∀ x y,
    (fun p : Spt InferT × List (List InferT × List InferT) => cwfs p.1) x ∧
      cunifyCodeModel x = .inl y → worklistR y x := by
  rintro ⟨s, work⟩ ⟨out, next⟩ ⟨hw, step⟩
  have hw' : cwfs out := kcunifywlPreservesPrecondModel (s, work) (out, next) ⟨hw, step⟩
  cases work with
  | nil => simp [cunifyCodeModel] at step
  | cons pair rest =>
    obtain ⟨left, right⟩ := pair
    cases left with
    | nil =>
      cases right with
      | nil =>
        simp [cunifyCodeModel] at step
        rcases step with ⟨rfl, rfl⟩
        refine ⟨hw, hw, HolFiniteMapExact.submap_refl _, ?_, Or.inr ⟨?_, ?_⟩⟩
        · intro k hk
          change substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨ cplistVars rest k at hk
          change substVars ((sp2fm s).map2 (fun p => encodeInferT p.2)) k ∨
            ((False ∨ False) ∨ cplistVars rest k)
          tauto
        · simp [pflat]
        · simp
      | cons b bs => simp [cunifyCodeModel] at step
    | cons a as' =>
      cases right with
      | nil => simp [cunifyCodeModel] at step
      | cons b bs =>
        cases ha : tcwalkModel s a <;> cases hb : tcwalkModel s b <;>
          simp only [cunifyCodeModel, ha, hb] at step
        case varDb.varDb =>
          split at step
          · simp only [Sum.inl.injEq, Prod.mk.injEq] at step
            rcases step with ⟨rfl, rfl⟩
            exact tailsSame s a b as' bs rest hw
          · simp at step
        case app.app =>
          split at step
          · simp only [Sum.inl.injEq, Prod.mk.injEq] at step
            rcases step with ⟨rfl, rfl⟩
            exact appsRelation s a b as' bs _ _ rest _ _ hw ha hb
          · simp at step
        case varDb.app | app.varDb => simp at step
        case varDb.uvar =>
          rename_i db v
          simp only [Sum.inl.injEq, Prod.mk.injEq] at step
          rcases step with ⟨rfl, rfl⟩
          exact insertRelSwap s v (.varDb db) a b as' bs rest hw hw' ha hb
        case uvar.varDb =>
          rename_i v db
          simp only [Sum.inl.injEq, Prod.mk.injEq] at step
          rcases step with ⟨rfl, rfl⟩
          exact insertRel s v (.varDb db) a b as' bs rest hw hw' ha hb
        case app.uvar =>
          rename_i ts tc v
          cases ho : tcocwlModel s v [ts] <;> simp only [ho, Bool.false_eq_true, ↓reduceIte,
            Sum.inl.injEq, Prod.mk.injEq] at step
          · rcases step with ⟨rfl, rfl⟩
            exact insertRelSwap s v (.app ts tc) a b as' bs rest hw hw' ha hb
          · simp at step
        case uvar.app =>
          rename_i v ts tc
          cases ho : tcocwlModel s v [ts] <;> simp only [ho, Bool.false_eq_true, ↓reduceIte,
            Sum.inl.injEq, Prod.mk.injEq] at step
          · rcases step with ⟨rfl, rfl⟩
            exact insertRel s v (.app ts tc) a b as' bs rest hw hw' ha hb
          · simp at step
        case uvar.uvar =>
          rename_i v1 v2
          by_cases eq : v1 = v2
          · simp [eq] at step
            rcases step with ⟨rfl, rfl⟩
            exact tailsSame s a b as' bs rest hw
          · simp [eq] at step
            rcases step with ⟨rfl, rfl⟩
            exact insertRel s v1 (.uvar v2) a b as' bs rest hw hw' ha hb


/- The relation is expanded to expose the reviewed finite-map producer.
   The selected step agrees with HOL's step under the original cwfs guard. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "kcunifywl_ensures_decrease"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem kcunifywlEnsuresDecreaseModel
    (y : Spt InferT × List (List InferT × List InferT)) : ∀ x,
    (fun p : Spt InferT × List (List InferT × List InferT) => cwfs p.1) x ∧
      cunifyCodeModel x = .inl y →
    cwfs y.1 ∧ cwfs x.1 ∧ (sp2fm x.1).submap (sp2fm y.1) ∧
      Set.Subset
        (Set.union (substVars ((sp2fm y.1).map2 (fun p => encodeInferT p.2)))
          (cplistVars y.2))
        (Set.union (substVars ((sp2fm x.1).map2 (fun p => encodeInferT p.2)))
          (cplistVars x.2)) ∧
      (Relation.TransGen
          (bagMultisetStep (walkstarR (sp2fm (sptMap encodeInferT y.1))))
          (pflat y.2) (pflat x.2) ∨
        (pflat y.2 = pflat x.2 ∧ y.2.length < x.2.length)) := by
  intro x h
  exact stepDecreases x y h

end Flapjack.Compiler.Inference.Unify
