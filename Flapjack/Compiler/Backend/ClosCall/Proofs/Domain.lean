import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
import Flapjack.Compiler.Backend.ClosCall.Proofs.Length

/-! Domain accounting for the executable direct-call state. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

private theorem sptDomain_insert {A : Type} (key inserted : Nat) (value : A) (tree : Spt A) :
    sptDomain (sptInsert inserted value tree) key ↔ key = inserted ∨ sptDomain tree key := by
  by_cases equal : key = inserted
  · subst key
    simp [sptDomain, sptLookup_sptInsert_same]
  · simp [sptDomain, sptLookup_sptInsert_ne inserted key value tree equal, equal]

private theorem fold_insert_domain (loc : Nat) (indices : List Nat) (tree : NumSet) (key : Nat) :
    sptDomain (indices.foldl (fun s i => sptInsert (loc + 2 * i) () s) tree) key ↔
      sptDomain tree key ∨ ∃ i ∈ indices, key = loc + 2 * i := by
  induction indices generalizing tree with
  | nil => simp
  | cons i indices ih =>
    simp only [List.foldl_cons, ih, sptDomain_insert, List.mem_cons]
    aesop

/-- The production insertion loop adds exactly the input range to the known
location domain and preserves every previous location. -/
theorem insertEach_domain (loc count : Nat) (state : State) (key : Nat) :
    sptDomain (insertEach loc count state).1 key ↔
      sptDomain state.1 key ∨ ∃ i < count, key = loc + 2 * i := by
  simp only [insertEach, fold_insert_domain, List.mem_range]

/-- Adding known locations retains the one-sided code invariant. -/
theorem weaklyWellFormed_insertEach (loc count : Nat) (state : State)
    (well : weaklyWellFormed state) : weaklyWellFormed (insertEach loc count state) := by
  intro label member
  have old : label ∈ { x | x ∈ state.2.map Prod.fst } := by
    simpa [insertEach] using member
  obtain ⟨key, inOld, equal⟩ := well old
  exact ⟨key, (insertEach_domain loc count state key).mpr (Or.inl inOld), equal⟩

/-- Every known location in the first state remains known in the second. -/
def KnownExt (initial final : State) : Prop :=
  ∀ key, sptDomain initial.1 key → sptDomain final.1 key

private theorem knownExt_refl (state : State) : KnownExt state state := by
  intro _ h
  exact h

private theorem knownExt_trans {first middle last : State}
    (left : KnownExt first middle) (right : KnownExt middle last) : KnownExt first last := by
  intro key member
  exact right key (left key member)

private theorem knownExt_insertEach (loc count : Nat) (state : State) :
    KnownExt state (insertEach loc count state) := by
  intro key member
  exact (insertEach_domain loc count state key).mpr (Or.inl member)

mutual
/-- A successful executable direct-call traversal does not forget known
locations. HOL's traversal is total; this statement retains the executable
fuel-success premise. -/
theorem callsFuel_knownExt (fuel : Nat) (e : ClosLang.Exp) (initial final : State)
    (out : ClosLang.Exp) (run : callsFuel fuel e initial = some (out, final)) :
    KnownExt initial final := by
  cases fuel with
  | zero => simp [callsFuel] at run
  | succ fuel =>
    cases e with
    | var tr n => simp [callsFuel] at run; obtain ⟨_, rfl⟩ := run; exact knownExt_refl _
    | ifThenElse tr x y z =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, ⟨z', s3⟩, hz, _, rfl⟩ := run
      exact knownExt_trans (callsFuel_knownExt fuel x initial s1 x' hx)
        (knownExt_trans (callsFuel_knownExt fuel y s1 s2 y' hy)
          (callsFuel_knownExt fuel z s2 s3 z' hz))
    | «let» tr xs body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨body', s2⟩, hb, _, rfl⟩ := run
      exact knownExt_trans (callsListFuel_knownExt fuel xs initial s1 xs' hx)
        (callsFuel_knownExt fuel body s1 s2 body' hb)
    | raise tr x | tick tr x =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, _, rfl⟩ := run
      exact callsFuel_knownExt fuel x initial s1 x' hx
    | handle tr x y =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, _, rfl⟩ := run
      exact knownExt_trans (callsFuel_knownExt fuel x initial s1 x' hx)
        (callsFuel_knownExt fuel y s1 s2 y' hy)
    | call tr ticks dest xs | op tr dest xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, _, rfl⟩ := run
      exact callsListFuel_knownExt fuel xs initial s1 xs' hx
    | app tr loc x xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨x', s2⟩, hy, rest⟩ := run
      have endState : s2 = final := by
        cases loc <;> simp only at rest
        all_goals repeat' split at rest
        all_goals simp_all only [Option.some.injEq, Prod.mk.injEq]
      subst final
      exact knownExt_trans (callsListFuel_knownExt fuel xs initial s1 xs' hx)
        (callsFuel_knownExt fuel x s1 s2 x' hy)
    | fn name loc ws arity body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨body', s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body'', s2⟩, hb', _, rfl⟩ := rest
        exact callsFuel_knownExt fuel body initial s2 body'' hb'
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, rfl⟩ := rest
        exact knownExt_trans (knownExt_insertEach _ _ _)
          (callsFuel_knownExt fuel body _ s1 body' hb)
    | letrec names loc ws fns body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨bodies, s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨bodies', s2⟩, hb', ⟨body', s3⟩, he, _, rfl⟩ := rest
        exact knownExt_trans (callsListFuel_knownExt fuel _ initial s2 bodies' hb')
          (callsFuel_knownExt fuel body s2 s3 body' he)
      | true =>
        simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at rest
        obtain ⟨⟨body', s2⟩, he, _, rfl⟩ := rest
        have first := knownExt_trans (knownExt_insertEach (loc.getD 0) fns.length initial)
          (callsListFuel_knownExt fuel _ _ s1 bodies hb)
        have last := callsFuel_knownExt fuel body _ s2 body' he
        simpa only [KnownExt, codeList] using knownExt_trans first last
termination_by fuel

/-- The list traversal also retains every known location. -/
theorem callsListFuel_knownExt (fuel : Nat) (es : List ClosLang.Exp) (initial final : State)
    (out : List ClosLang.Exp) (run : callsListFuel fuel es initial = some (out, final)) :
    KnownExt initial final := by
  cases es with
  | nil => simp [callsListFuel] at run; obtain ⟨_, rfl⟩ := run; exact knownExt_refl _
  | cons e es =>
    cases fuel with
    | zero => simp [callsListFuel] at run
    | succ fuel =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, he, ⟨es', s2⟩, hs, _, rfl⟩ := run
      exact knownExt_trans (callsFuel_knownExt fuel e initial s1 e' he)
        (callsListFuel_knownExt fuel es s1 s2 es' hs)
termination_by fuel
end

/-- The production retry wrapper retains known locations. -/
theorem callsListBounded_knownExt (fuel : Nat) (es : List ClosLang.Exp) (initial final : State)
    (out : List ClosLang.Exp) (run : callsListBounded fuel es initial = some (out, final)) :
    KnownExt initial final := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | some result =>
    simp only [first, Option.some.injEq] at run
    subst result
    exact callsListFuel_knownExt fuel es initial final out first
  | none =>
    simp only [first] at run
    exact callsListFuel_knownExt _ es initial final out run

private theorem weaklyWellFormed_cons (loc arity : Nat) (body : ClosLang.Exp) (state : State)
    (well : weaklyWellFormed state) (known : sptDomain state.1 loc) :
    weaklyWellFormed (state.1, (loc + 1, arity, body) :: state.2) := by
  intro label member
  simp only [Set.mem_ofPred_eq, List.map_cons, List.mem_cons] at member
  rcases member with equal | old
  · exact ⟨loc, known, by omega⟩
  · exact well old

mutual
/-- The executable traversal preserves the one-sided correspondence between
generated labels and known locations whenever it succeeds. -/
theorem callsFuel_weaklyWellFormed (fuel : Nat) (e : ClosLang.Exp) (initial final : State)
    (out : ClosLang.Exp) (run : callsFuel fuel e initial = some (out, final))
    (well : weaklyWellFormed initial) : weaklyWellFormed final := by
  cases fuel with
  | zero => simp [callsFuel] at run
  | succ fuel =>
    cases e with
    | var tr n => simp [callsFuel] at run; obtain ⟨_, rfl⟩ := run; exact well
    | ifThenElse tr x y z =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, ⟨z', s3⟩, hz, _, rfl⟩ := run
      exact callsFuel_weaklyWellFormed fuel z s2 s3 z' hz
        (callsFuel_weaklyWellFormed fuel y s1 s2 y' hy
          (callsFuel_weaklyWellFormed fuel x initial s1 x' hx well))
    | «let» tr xs body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨body', s2⟩, hb, _, rfl⟩ := run
      exact callsFuel_weaklyWellFormed fuel body s1 s2 body' hb
        (callsListFuel_weaklyWellFormed fuel xs initial s1 xs' hx well)
    | raise tr x | tick tr x =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, _, rfl⟩ := run
      exact callsFuel_weaklyWellFormed fuel x initial s1 x' hx well
    | handle tr x y =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, _, rfl⟩ := run
      exact callsFuel_weaklyWellFormed fuel y s1 s2 y' hy
        (callsFuel_weaklyWellFormed fuel x initial s1 x' hx well)
    | call tr ticks dest xs | op tr dest xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, _, rfl⟩ := run
      exact callsListFuel_weaklyWellFormed fuel xs initial s1 xs' hx well
    | app tr loc x xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨x', s2⟩, hy, rest⟩ := run
      have endState : s2 = final := by
        cases loc <;> simp only at rest
        all_goals repeat' split at rest
        all_goals simp_all only [Option.some.injEq, Prod.mk.injEq]
      subst final
      exact callsFuel_weaklyWellFormed fuel x s1 s2 x' hy
        (callsListFuel_weaklyWellFormed fuel xs initial s1 xs' hx well)
    | fn name loc ws arity body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨body', s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body'', s2⟩, hb', _, rfl⟩ := rest
        exact callsFuel_weaklyWellFormed fuel body initial s2 body'' hb' well
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, rfl⟩ := rest
        apply weaklyWellFormed_cons
        · exact callsFuel_weaklyWellFormed fuel body _ s1 body' hb
            (weaklyWellFormed_insertEach _ _ _ well)
        · apply callsFuel_knownExt fuel body _ s1 body' hb
          apply (insertEach_domain (loc.getD 0) 1 initial (loc.getD 0)).mpr
          right
          exact ⟨0, by omega, by omega⟩
    | letrec names loc ws fns body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨bodies, s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨bodies', s2⟩, hb', ⟨body', s3⟩, he, _, rfl⟩ := rest
        exact callsFuel_weaklyWellFormed fuel body s2 s3 body' he
          (callsListFuel_weaklyWellFormed fuel _ initial s2 bodies' hb' well)
      | true =>
        simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at rest
        obtain ⟨⟨body', s2⟩, he, _, rfl⟩ := rest
        apply callsFuel_weaklyWellFormed fuel body _ s2 body' he
        apply weaklyWellFormed_codeList
        · exact callsListFuel_weaklyWellFormed fuel _ _ s1 bodies hb
            (weaklyWellFormed_insertEach _ _ _ well)
        · intro key member
          simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_range] at member
          obtain ⟨i, bound, rfl⟩ := member
          have size := convertedFunctions_length fuel fns
            (insertEach (loc.getD 0) fns.length initial) s1 bodies hb
          rw [size] at bound
          apply callsListFuel_knownExt fuel _ _ s1 bodies hb
          apply (insertEach_domain (loc.getD 0) fns.length initial _).mpr
          exact Or.inr ⟨i, bound, rfl⟩
termination_by fuel

/-- List traversal preserves the one-sided state invariant. -/
theorem callsListFuel_weaklyWellFormed (fuel : Nat) (es : List ClosLang.Exp)
    (initial final : State) (out : List ClosLang.Exp)
    (run : callsListFuel fuel es initial = some (out, final))
    (well : weaklyWellFormed initial) : weaklyWellFormed final := by
  cases es with
  | nil => simp [callsListFuel] at run; obtain ⟨_, rfl⟩ := run; exact well
  | cons e es =>
    cases fuel with
    | zero => simp [callsListFuel] at run
    | succ fuel =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, he, ⟨es', s2⟩, hs, _, rfl⟩ := run
      exact callsListFuel_weaklyWellFormed fuel es s1 s2 es' hs
        (callsFuel_weaklyWellFormed fuel e initial s1 e' he well)
termination_by fuel
end

/-- The production retry wrapper preserves the one-sided code invariant. -/
theorem callsListBounded_weaklyWellFormed (fuel : Nat) (es : List ClosLang.Exp)
    (initial final : State) (out : List ClosLang.Exp)
    (run : callsListBounded fuel es initial = some (out, final))
    (well : weaklyWellFormed initial) : weaklyWellFormed final := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | some result =>
    simp only [first, Option.some.injEq] at run
    subst result
    exact callsListFuel_weaklyWellFormed fuel es initial final out first well
  | none =>
    simp only [first] at run
    exact callsListFuel_weaklyWellFormed _ es initial final out run well

end Flapjack.Compiler.Backend.ClosCall
