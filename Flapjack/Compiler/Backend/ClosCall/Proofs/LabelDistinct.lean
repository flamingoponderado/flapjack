module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelOrigins

@[expose] public section

/-! Distinctness of direct-call auxiliary labels. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

/-- None of the successor labels of these input locations is already emitted. -/
def LabelsFresh (locations : List Nat) (state : State) : Prop :=
  ∀ loc ∈ locations, loc + 1 ∉ state.2.map Prod.fst

private theorem fresh_subset {xs ys : List Nat} {state : State}
    (fresh : LabelsFresh ys state) (sub : ∀ x ∈ xs, x ∈ ys) : LabelsFresh xs state := by
  intro x mem
  exact fresh x (sub x mem)

private theorem fresh_after {xs ys : List Nat} {s0 s1 : State}
    (distinct : (xs ++ ys).Nodup) (fresh : LabelsFresh (xs ++ ys) s0)
    (bound : LabelsBound s0 s1 xs) : LabelsFresh ys s1 := by
  intro loc inYs member
  rcases bound (loc + 1) member with old | ⟨origin, inXs, equal⟩
  · exact fresh loc (List.mem_append_right _ inYs) old
  · have unequal := (List.nodup_append.mp distinct).2.2 origin inXs loc inYs
    exact unequal (Nat.add_right_cancel equal.symm)

/-- Compose two successful traversals over disjoint closure-location lists. -/
private theorem distinct_sequence {xs ys : List Nat} {s0 s1 s2 : State}
    (distinct : (xs ++ ys).Nodup) (fresh : LabelsFresh (xs ++ ys) s0)
    (initial : (s0.2.map Prod.fst).Nodup) (bound : LabelsBound s0 s1 xs)
    (first : xs.Nodup → LabelsFresh xs s0 → (s0.2.map Prod.fst).Nodup →
      (s1.2.map Prod.fst).Nodup)
    (second : ys.Nodup → LabelsFresh ys s1 → (s1.2.map Prod.fst).Nodup →
      (s2.2.map Prod.fst).Nodup) : (s2.2.map Prod.fst).Nodup := by
  apply second (List.Nodup.of_append_right distinct) (fresh_after distinct fresh bound)
  apply first (List.Nodup.of_append_left distinct)
  · exact fresh_subset fresh (fun _ member => List.mem_append_left _ member)
  · exact initial

private theorem bound_sequence {xs ys : List Nat} {s0 s1 s2 : State}
    (first : LabelsBound s0 s1 xs) (second : LabelsBound s1 s2 ys) :
    LabelsBound s0 s2 (xs ++ ys) := by
  intro label member
  rcases second label member with middle | ⟨loc, inY, eq⟩
  · rcases first label middle with old | ⟨loc, inX, eq⟩
    · exact Or.inl old
    · exact Or.inr ⟨loc, List.mem_append_left _ inX, eq⟩
  · exact Or.inr ⟨loc, List.mem_append_right _ inY, eq⟩

mutual
/-- A successful traversal preserves distinct emitted labels when its input
closure locations are distinct and their successors are fresh. This theorem
is specific to the fuel-bounded executable pass. -/
private theorem callsFuel_labelsDistinct (fuel : Nat) (e : Exp) (initial final : State) (out : Exp)
    (run : callsFuel fuel e initial = some (out, final))
    (distinct : (codeLocationsExp e).Nodup) (fresh : LabelsFresh (codeLocationsExp e) initial)
    (oldDistinct : (initial.2.map Prod.fst).Nodup) : (final.2.map Prod.fst).Nodup := by
  cases fuel with
  | zero => simp [callsFuel] at run
  | succ fuel =>
    cases e with
    | var tr n => simp [callsFuel] at run; obtain ⟨_, rfl⟩ := run; exact oldDistinct
    | ifThenElse tr x y z =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, ⟨z', s3⟩, hz, _, rfl⟩ := run
      simp only [codeLocationsExp] at distinct fresh
      apply distinct_sequence distinct fresh oldDistinct
        (bound_sequence (callsFuel_labelsBound fuel x initial s1 x' hx)
          (callsFuel_labelsBound fuel y s1 s2 y' hy))
      · intro d f old
        exact distinct_sequence d f old (callsFuel_labelsBound fuel x initial s1 x' hx)
          (callsFuel_labelsDistinct fuel x initial s1 x' hx)
          (callsFuel_labelsDistinct fuel y s1 s2 y' hy)
      · exact callsFuel_labelsDistinct fuel z s2 s3 z' hz
    | «let» tr xs body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨body', s2⟩, hb, _, rfl⟩ := run
      exact distinct_sequence distinct fresh oldDistinct
        (callsListFuel_labelsBound fuel xs initial s1 xs' hx)
        (callsListFuel_labelsDistinct fuel xs initial s1 xs' hx)
        (callsFuel_labelsDistinct fuel body s1 s2 body' hb)
    | raise tr x | tick tr x =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, _, rfl⟩ := run
      exact callsFuel_labelsDistinct fuel x initial s1 x' hx distinct fresh oldDistinct
    | handle tr x y =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, _, rfl⟩ := run
      exact distinct_sequence distinct fresh oldDistinct
        (callsFuel_labelsBound fuel x initial s1 x' hx)
        (callsFuel_labelsDistinct fuel x initial s1 x' hx)
        (callsFuel_labelsDistinct fuel y s1 s2 y' hy)
    | call tr ticks dest xs | op tr dest xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, _, rfl⟩ := run
      exact callsListFuel_labelsDistinct fuel xs initial s1 xs' hx distinct fresh oldDistinct
    | app tr loc x xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨x', s2⟩, hy, rest⟩ := run
      have endState : s2 = final := by
        cases loc <;> simp only at rest
        all_goals repeat' split at rest
        all_goals simp_all only [Option.some.injEq, Prod.mk.injEq]
      subst final
      have dis : (codeLocations xs ++ codeLocationsExp x).Nodup := by
        exact List.nodup_append_comm.mp distinct
      have fr : LabelsFresh (codeLocations xs ++ codeLocationsExp x) initial := by
        intro n member
        apply fresh n
        simpa [codeLocationsExp, List.mem_append, or_comm] using member
      exact distinct_sequence dis fr oldDistinct
        (callsListFuel_labelsBound fuel xs initial s1 xs' hx)
        (callsListFuel_labelsDistinct fuel xs initial s1 xs' hx)
        (callsFuel_labelsDistinct fuel x s1 s2 x' hy)
    | fn name loc ws arity body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨body', s1⟩, hb, closed, _, rest⟩ := run
      simp only [codeLocationsExp] at distinct fresh
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body'', s2⟩, hb', _, rfl⟩ := rest
        apply callsFuel_labelsDistinct fuel body initial s2 body'' hb'
          (List.Nodup.of_append_left distinct)
        · exact fresh_subset fresh (fun _ h => List.mem_append_left _ h)
        · exact oldDistinct
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, rfl⟩ := rest
        have bound : LabelsBound initial s1 (codeLocationsExp body) := by
          simpa only [LabelsBound, insertEach] using
            callsFuel_labelsBound fuel body (insertEach (loc.getD 0) 1 initial) s1 body' hb
        have before : (s1.2.map Prod.fst).Nodup := by
          apply callsFuel_labelsDistinct fuel body (insertEach (loc.getD 0) 1 initial) s1 body' hb
            (List.Nodup.of_append_left distinct)
          · simpa only [LabelsFresh, insertEach] using
              (fresh_subset fresh (fun _ h => List.mem_append_left _ h) :
                LabelsFresh (codeLocationsExp body) initial)
          · simpa only [insertEach] using oldDistinct
        have afterFresh := fresh_after distinct fresh bound
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨afterFresh (loc.getD 0) (by simp), before⟩
    | letrec names loc ws fns body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨bodies, s1⟩, hb, closed, _, rest⟩ := run
      simp only [codeLocationsExp, List.append_assoc] at distinct fresh
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨bodies', s2⟩, hb', ⟨body', s3⟩, he, _, rfl⟩ := rest
        have d : (codeLocationsFuns fns ++ codeLocationsExp body).Nodup := by
          have all := List.nodup_append.mp distinct
          have right := List.nodup_append.mp all.2.1
          apply List.nodup_append.mpr
          refine ⟨all.1, right.2.1, ?_⟩
          intro a ha b hb
          exact all.2.2 a ha b (List.mem_append_right _ hb)
        have f : LabelsFresh (codeLocationsFuns fns ++ codeLocationsExp body) initial := by
          apply fresh_subset fresh
          intro n member
          simp only [List.mem_append] at member ⊢
          aesop
        apply distinct_sequence d f oldDistinct
        · simpa only [← codeLocationsFuns_map] using
            callsListFuel_labelsBound fuel (fns.map Prod.snd) initial s2 bodies' hb'
        · intro d f old
          exact callsListFuel_labelsDistinct fuel (fns.map Prod.snd) initial s2 bodies' hb'
            (by simpa only [← codeLocationsFuns_map] using d)
            (by simpa only [← codeLocationsFuns_map] using f) old
        · exact callsFuel_labelsDistinct fuel body s2 s3 body' he
      | true =>
        simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at rest
        obtain ⟨⟨body', s2⟩, he, _, rfl⟩ := rest
        have bound : LabelsBound initial s1 (codeLocationsFuns fns) := by
          simpa only [LabelsBound, insertEach, ← codeLocationsFuns_map] using
            callsListFuel_labelsBound fuel (fns.map Prod.snd)
              (insertEach (loc.getD 0) fns.length initial) s1 bodies hb
        have d1 : (s1.2.map Prod.fst).Nodup := by
          apply callsListFuel_labelsDistinct fuel (fns.map Prod.snd)
            (insertEach (loc.getD 0) fns.length initial) s1 bodies hb
          · simpa only [← codeLocationsFuns_map] using List.Nodup.of_append_left distinct
          · simpa only [LabelsFresh, insertEach, ← codeLocationsFuns_map] using
              (fresh_subset fresh (fun _ h => List.mem_append_left _ h) :
                LabelsFresh (codeLocationsFuns fns) initial)
          · simpa only [insertEach] using oldDistinct
        have remaining := fresh_after distinct fresh bound
        have dRemaining := List.Nodup.of_append_right distinct
        have convertedLength := convertedFunctions_length fuel fns
          (insertEach (loc.getD 0) fns.length initial) s1 bodies hb
        have genBound := codeList_bound (loc.getD 0) ((fns.map Prod.fst).zip bodies) s1
        rw [convertedLength] at genBound
        have groupDistinct :
            ((codeList (loc.getD 0) ((fns.map Prod.fst).zip bodies) s1).2.map Prod.fst).Nodup := by
          apply codeList_labels_nodup _ _ _ d1
          intro i bound
          have inRemaining : loc.getD 0 + 2 * i ∈
              (List.range fns.length).map (fun i => loc.getD 0 + 2 * i) ++
                codeLocationsExp body := by
            simp only [List.mem_append, List.mem_map, List.mem_range]
            left
            exact ⟨i, by simpa only [convertedLength] using bound, rfl⟩
          simpa only [Nat.mul_comm 2 i] using remaining _ inRemaining
        have bodyFresh := fresh_after dRemaining remaining genBound
        exact callsFuel_labelsDistinct fuel body _ s2 body' he
          (List.Nodup.of_append_right dRemaining) bodyFresh groupDistinct
termination_by fuel

/-- The list traversal preserves distinctness under the same conditions. -/
private theorem callsListFuel_labelsDistinct (fuel : Nat) (es : List Exp) (initial final : State)
    (out : List Exp) (run : callsListFuel fuel es initial = some (out, final))
    (distinct : (codeLocations es).Nodup) (fresh : LabelsFresh (codeLocations es) initial)
    (oldDistinct : (initial.2.map Prod.fst).Nodup) : (final.2.map Prod.fst).Nodup := by
  cases es with
  | nil => simp [callsListFuel] at run; obtain ⟨_, rfl⟩ := run; exact oldDistinct
  | cons e es =>
    cases fuel with
    | zero => simp [callsListFuel] at run
    | succ fuel =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, he, ⟨es', s2⟩, hs, _, rfl⟩ := run
      exact distinct_sequence distinct fresh oldDistinct
        (callsFuel_labelsBound fuel e initial s1 e' he)
        (callsFuel_labelsDistinct fuel e initial s1 e' he)
        (callsListFuel_labelsDistinct fuel es s1 s2 es' hs)
termination_by fuel
end

/-- The production retry wrapper preserves label distinctness. -/
theorem callsListBounded_labelsDistinct (fuel : Nat) (es : List Exp) (initial final : State)
    (out : List Exp) (run : callsListBounded fuel es initial = some (out, final))
    (distinct : (codeLocations es).Nodup) (fresh : LabelsFresh (codeLocations es) initial)
    (oldDistinct : (initial.2.map Prod.fst).Nodup) : (final.2.map Prod.fst).Nodup := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | some result =>
    simp only [first, Option.some.injEq] at run
    subst result
    exact callsListFuel_labelsDistinct fuel es initial final out first distinct fresh oldDistinct
  | none =>
    simp only [first] at run
    exact callsListFuel_labelsDistinct _ es initial final out run distinct fresh oldDistinct

end Flapjack.Compiler.Backend.ClosCall
