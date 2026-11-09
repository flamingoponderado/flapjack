module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.Domain
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Suffix
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelDistinct
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Total

@[expose] public section

/-! Origins of newly known locations in direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- A known output location was either already known or has its successor
in the output auxiliary code. -/
def KnownBound (initial final : State) : Prop :=
  ∀ key, sptDomain final.1 key →
    sptDomain initial.1 key ∨ key + 1 ∈ final.2.map Prod.fst

private theorem knownBound_refl (state : State) : KnownBound state state := by
  intro _ member
  exact Or.inl member

private theorem label_persists {first last : State} (suffix : first.2 <:+ last.2)
    {label : Nat} (member : label ∈ first.2.map Prod.fst) : label ∈ last.2.map Prod.fst := by
  obtain ⟨front, eq⟩ := suffix
  rw [← eq, List.map_append]
  exact List.mem_append_right _ member

/-- Composing known-location bounds preserves newly emitted labels when the
intermediate code remains a suffix. This is Flapjack-specific infrastructure. -/
theorem knownBound_trans {first middle last : State}
    (left : KnownBound first middle) (right : KnownBound middle last)
    (suffix : middle.2 <:+ last.2) : KnownBound first last := by
  intro key member
  rcases right key member with old | generated
  · rcases left key old with original | generated
    · exact Or.inl original
    · exact Or.inr (label_persists suffix generated)
  · exact Or.inr generated

mutual
/-- Successful direct-call conversion accounts for every newly known
location by an emitted auxiliary label. The success premise reflects the
bounded executable traversal. -/
theorem callsFuel_knownBound (fuel : Nat) (e : ClosLang.Exp) (initial final : State)
    (out : ClosLang.Exp) (run : callsFuel fuel e initial = some (out, final)) :
    KnownBound initial final := by
  cases fuel with
  | zero => simp [callsFuel] at run
  | succ fuel =>
    cases e with
    | var tr n => simp [callsFuel] at run; obtain ⟨_, rfl⟩ := run; exact knownBound_refl _
    | ifThenElse tr x y z =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, ⟨z', s3⟩, hz, _, rfl⟩ := run
      exact knownBound_trans (callsFuel_knownBound fuel x initial s1 x' hx)
        (knownBound_trans (callsFuel_knownBound fuel y s1 s2 y' hy)
          (callsFuel_knownBound fuel z s2 s3 z' hz) (callsFuel_suffix fuel z s2 s3 z' hz))
        ((callsFuel_suffix fuel y s1 s2 y' hy).trans (callsFuel_suffix fuel z s2 s3 z' hz))
    | «let» tr xs body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨body', s2⟩, hb, _, rfl⟩ := run
      exact knownBound_trans (callsListFuel_knownBound fuel xs initial s1 xs' hx)
        (callsFuel_knownBound fuel body s1 s2 body' hb) (callsFuel_suffix fuel body s1 s2 body' hb)
    | raise tr x | tick tr x =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, _, rfl⟩ := run
      exact callsFuel_knownBound fuel x initial s1 x' hx
    | handle tr x y =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, _, rfl⟩ := run
      exact knownBound_trans (callsFuel_knownBound fuel x initial s1 x' hx)
        (callsFuel_knownBound fuel y s1 s2 y' hy) (callsFuel_suffix fuel y s1 s2 y' hy)
    | call tr ticks dest xs | op tr dest xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, _, rfl⟩ := run
      exact callsListFuel_knownBound fuel xs initial s1 xs' hx
    | app tr loc x xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨x', s2⟩, hy, rest⟩ := run
      have endState : s2 = final := by
        cases loc <;> simp only at rest
        all_goals repeat' split at rest
        all_goals simp_all only [Option.some.injEq, Prod.mk.injEq]
      subst final
      exact knownBound_trans (callsListFuel_knownBound fuel xs initial s1 xs' hx)
        (callsFuel_knownBound fuel x s1 s2 x' hy) (callsFuel_suffix fuel x s1 s2 x' hy)
    | fn name loc ws arity body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨body', s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body'', s2⟩, hb', _, rfl⟩ := rest
        exact callsFuel_knownBound fuel body initial s2 body'' hb'
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, rfl⟩ := rest
        intro key member
        rcases callsFuel_knownBound fuel body _ s1 body' hb key member with old | generated
        · rcases (insertEach_domain (loc.getD 0) 1 initial key).mp old with original | ⟨i, hi, eq⟩
          · exact Or.inl original
          · right
            have keyEq : key = loc.getD 0 := by omega
            simp [List.map_cons, keyEq]
        · right
          exact List.mem_cons_of_mem _ generated
    | letrec names loc ws fns body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨bodies, s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨bodies', s2⟩, hb', ⟨body', s3⟩, he, _, rfl⟩ := rest
        exact knownBound_trans (callsListFuel_knownBound fuel _ initial s2 bodies' hb')
          (callsFuel_knownBound fuel body s2 s3 body' he) (callsFuel_suffix fuel body s2 s3 body' he)
      | true =>
        simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at rest
        obtain ⟨⟨body', s2⟩, he, _, rfl⟩ := rest
        intro key member
        rcases callsFuel_knownBound fuel body _ s2 body' he key member with known | generated
        · simp only [codeList] at known
          rcases callsListFuel_knownBound fuel _ _ s1 bodies hb key known with old | generated
          · rcases (insertEach_domain (loc.getD 0) fns.length initial key).mp old with original | ⟨i, hi, eq⟩
            · exact Or.inl original
            · right
              apply label_persists (callsFuel_suffix fuel body _ s2 body' he)
              rw [convertedFunctions_labels fuel (loc.getD 0) fns
                (insertEach (loc.getD 0) fns.length initial) s1 bodies hb]
              simp only [List.mem_append, List.mem_reverse, List.mem_map, List.mem_range]
              left
              refine ⟨i, hi, ?_⟩
              omega
          · right
            apply label_persists (callsFuel_suffix fuel body _ s2 body' he)
            exact label_persists (codeList_suffix _ _ _) generated
        · exact Or.inr generated
termination_by fuel

/-- The list traversal accounts for newly known locations in the same way. -/
theorem callsListFuel_knownBound (fuel : Nat) (es : List ClosLang.Exp) (initial final : State)
    (out : List ClosLang.Exp) (run : callsListFuel fuel es initial = some (out, final)) :
    KnownBound initial final := by
  cases es with
  | nil => simp [callsListFuel] at run; obtain ⟨_, rfl⟩ := run; exact knownBound_refl _
  | cons e es =>
    cases fuel with
    | zero => simp [callsListFuel] at run
    | succ fuel =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, he, ⟨es', s2⟩, hs, _, rfl⟩ := run
      exact knownBound_trans (callsFuel_knownBound fuel e initial s1 e' he)
        (callsListFuel_knownBound fuel es s1 s2 es' hs) (callsListFuel_suffix fuel es s1 s2 es' hs)
termination_by fuel
end

/-- Successful list conversion preserves full direct-call state
well-formedness when input locations are distinct and fresh. This is a
fuel-aware executable counterpart of the total HOL pass theorem. -/
theorem callsListFuel_wellFormed (fuel : Nat) (es : List ClosLang.Exp)
    (initial final : State) (out : List ClosLang.Exp)
    (run : callsListFuel fuel es initial = some (out, final))
    (distinct : (ClosProps.codeLocations es).Nodup)
    (fresh : LabelsFresh (ClosProps.codeLocations es) initial)
    (well : wellFormed initial) : wellFormed final := by
  have weak := callsListFuel_weaklyWellFormed fuel es initial final out run (wellFormed_weak initial well)
  have origins := callsListFuel_knownBound fuel es initial final out run
  have suffix := callsListFuel_suffix fuel es initial final out run
  constructor
  · apply Set.Subset.antisymm weak
    intro label member
    obtain ⟨key, known, eq⟩ := member
    rcases origins key known with original | generated
    · have oldLabel : key + 1 ∈ initial.2.map Prod.fst := by
        have member : key + 1 ∈ Set.image Nat.succ (sptDomain initial.1) :=
          ⟨key, original, by omega⟩
        rw [← well.1] at member
        exact member
      have later := label_persists suffix oldLabel
      have same : key + 1 = label := by omega
      simpa [same] using later
    · have same : key + 1 = label := by omega
      simpa [same] using generated
  · exact callsListFuel_labelsDistinct fuel es initial final out run distinct fresh well.2

/-- The production retry wrapper preserves full direct-call state
well-formedness under the same conditions. -/
theorem callsListBounded_wellFormed (fuel : Nat) (es : List ClosLang.Exp)
    (initial final : State) (out : List ClosLang.Exp)
    (run : callsListBounded fuel es initial = some (out, final))
    (distinct : (ClosProps.codeLocations es).Nodup)
    (fresh : LabelsFresh (ClosProps.codeLocations es) initial)
    (well : wellFormed initial) : wellFormed final := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | some result =>
    simp only [first, Option.some.injEq] at run
    subst result
    exact callsListFuel_wellFormed fuel es initial final out first distinct fresh well
  | none =>
    simp only [first] at run
    exact callsListFuel_wellFormed _ es initial final out run distinct fresh well

end Flapjack.Compiler.Backend.ClosCall
