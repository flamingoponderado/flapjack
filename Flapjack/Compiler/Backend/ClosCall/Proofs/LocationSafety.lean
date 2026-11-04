import Flapjack.Compiler.Backend.ClosCall.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosCall.Proofs.Length
import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

/-! Location bounds for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- Every location in an expression satisfies a supplied bound. -/
def ExprLocationsWithin (P : Nat → Prop) (e : ClosLang.Exp) : Prop :=
  ∀ loc ∈ codeLocationsExp e, P loc

/-- Every location in an expression list satisfies a supplied bound. -/
def ListLocationsWithin (P : Nat → Prop) (es : List ClosLang.Exp) : Prop :=
  ∀ loc ∈ codeLocations es, P loc

/-- Every location nested inside auxiliary bodies satisfies a supplied bound. -/
def AuxLocationsWithin (P : Nat → Prop) (state : State) : Prop :=
  ∀ name arity body, (name, arity, body) ∈ state.2 → ExprLocationsWithin P body

/-- Generated variable arguments contain no closure locations. -/
theorem variables_codeLocations (trace : BackendCommon.Tra) (arity : Nat) :
    codeLocations (ClosCall.variables trace arity) = [] := by
  have helper : ∀ values : List Nat, codeLocations (values.map (.var trace)) = [] := by
    intro values
    induction values with
    | nil => rfl
    | cons head tail ih => simp [codeLocations, codeLocationsExp, ih]
  exact helper (List.range arity)

/-- Generated direct-call stubs contain no closure locations. -/
theorem callsList_codeLocationsFuns (loc : Nat) (fns : List (Nat × ClosLang.Exp)) :
    codeLocationsFuns (callsList loc fns) = [] := by
  have helper : ∀ pairs : List ((Nat × ClosLang.Exp) × Nat),
      codeLocationsFuns (pairs.map (fun ((arity, _), i) =>
        (arity, .call .none 0 (loc + 2 * i + 1) (ClosCall.variables .none arity)))) = [] := by
    intro pairs
    induction pairs with
    | nil => rfl
    | cons pair rest ih =>
      obtain ⟨⟨arity, body⟩, index⟩ := pair
      simp [codeLocationsFuns, codeLocationsExp, variables_codeLocations, ih]
  exact helper (fns.zip (List.range fns.length))

/-- Generated direct-call stubs preserve the size of a function group. -/
theorem callsList_length (loc : Nat) (fns : List (Nat × ClosLang.Exp)) :
    (callsList loc fns).length = fns.length := by
  simp [callsList]

/-- Every location in zipped function bodies occurs in the body list. -/
theorem codeLocationsFuns_zip_subset (arities : List Nat) (bodies : List ClosLang.Exp) :
    codeLocationsFuns (arities.zip bodies) ⊆ codeLocations bodies := by
  induction arities generalizing bodies with
  | nil => simp [codeLocationsFuns]
  | cons arity rest ih =>
    cases bodies with
    | nil => simp [codeLocationsFuns, codeLocations]
    | cons body bodies =>
      simp only [List.zip_cons_cons, codeLocationsFuns, codeLocations]
      intro loc member
      rcases List.mem_append.mp member with head | tail
      · exact List.mem_append_left _ head
      · exact List.mem_append_right _ (ih bodies tail)

/-- The source-shaped auxiliary-code builder preserves a bound on nested
locations when each added body satisfies it. -/
theorem codeListSource_locationsWithin (P : Nat → Prop) (loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (state : State)
    (old : AuxLocationsWithin P state)
    (fresh : ∀ p ∈ fns, ExprLocationsWithin P p.2) :
    AuxLocationsWithin P (codeListSource loc fns state) := by
  induction fns generalizing loc state with
  | nil => simpa [codeListSource] using old
  | cons p rest ih =>
    obtain ⟨arity, body⟩ := p
    have bodyBound := fresh (arity, body) (by simp)
    have tailBound : ∀ p ∈ rest, ExprLocationsWithin P p.2 := by
      intro p member
      exact fresh p (by simp [member])
    have extended : AuxLocationsWithin P (state.1, (loc + 1, arity, body) :: state.2) := by
      intro name arity' body' member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl, rfl⟩ | previous
      · exact bodyBound
      · exact old name arity' body' previous
    simpa [codeListSource] using ih (loc + 2) _ extended tailBound

/-- The executed auxiliary-code builder preserves a bound on nested locations. -/
theorem codeList_locationsWithin (P : Nat → Prop) (loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (state : State)
    (old : AuxLocationsWithin P state) (fresh : ∀ p ∈ fns, ExprLocationsWithin P p.2) :
    AuxLocationsWithin P (codeList loc fns state) := by
  rw [codeList_eq_source]
  exact codeListSource_locationsWithin P loc fns state old fresh

/-- A list bound applies to each member. -/
theorem listLocationsWithin_member (P : Nat → Prop) (es : List ClosLang.Exp)
    (safe : ListLocationsWithin P es) (e : ClosLang.Exp) (member : e ∈ es) : ExprLocationsWithin P e := by
  intro loc inside
  apply safe loc
  exact (mem_codeLocations loc es).2 ⟨e, member, inside⟩


/-- Zipping any arities with bounded bodies preserves each body's bound. -/
theorem zip_bodies_locationsWithin (P : Nat → Prop) (arities : List Nat) (bodies : List ClosLang.Exp)
    (safe : ListLocationsWithin P bodies) : ∀ p ∈ arities.zip bodies, ExprLocationsWithin P p.2 := by
  induction arities generalizing bodies with
  | nil => simp
  | cons arity rest ih =>
    cases bodies with
    | nil => simp
    | cons body bodies =>
      intro p member
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact listLocationsWithin_member P (body :: bodies) safe body (by simp)
      · apply ih bodies ?_ p member
        intro loc inside
        apply safe loc
        simp [codeLocations, inside]

mutual
/-- A successful direct-call expression traversal cannot introduce nested
closure locations outside the supplied source bound. -/
theorem callsFuel_locationsWithin (P : Nat → Prop) (fuel : Nat) (e out : ClosLang.Exp) (initial final : State)
    (run : callsFuel fuel e initial = some (out, final))
    (safe : ExprLocationsWithin P e) (aux : AuxLocationsWithin P initial) :
    ExprLocationsWithin P out ∧ AuxLocationsWithin P final := by
  cases fuel with
  | zero => simp [callsFuel] at run
  | succ fuel =>
    cases e with
    | var trace index =>
      simp [callsFuel] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨safe, aux⟩
    | ifThenElse trace x y z =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, ⟨z', s3⟩, hz, rfl, rfl⟩ := run
      have sx : ExprLocationsWithin P x := by intro n h; apply safe n; simp [codeLocationsExp, h]
      have sy : ExprLocationsWithin P y := by intro n h; apply safe n; simp [codeLocationsExp, h]
      have sz : ExprLocationsWithin P z := by intro n h; apply safe n; simp [codeLocationsExp, h]
      obtain ⟨sx', a1⟩ := callsFuel_locationsWithin P fuel x x' initial s1 hx sx aux
      obtain ⟨sy', a2⟩ := callsFuel_locationsWithin P fuel y y' s1 s2 hy sy a1
      obtain ⟨sz', a3⟩ := callsFuel_locationsWithin P fuel z z' s2 s3 hz sz a2
      refine ⟨?_, a3⟩
      intro n h
      simp only [codeLocationsExp, List.mem_append] at h
      rcases h with (h | h) | h
      · exact sx' n h
      · exact sy' n h
      · exact sz' n h
    | «let» trace xs body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨body', s2⟩, hb, rfl, rfl⟩ := run
      have sx : ListLocationsWithin P xs := by intro n h; apply safe n; simp [codeLocationsExp, h]
      have sb : ExprLocationsWithin P body := by intro n h; apply safe n; simp [codeLocationsExp, h]
      obtain ⟨sx', a1⟩ := callsListFuel_locationsWithin P fuel xs xs' initial s1 hx sx aux
      obtain ⟨sb', a2⟩ := callsFuel_locationsWithin P fuel body body' s1 s2 hb sb a1
      refine ⟨?_, a2⟩
      intro n h
      simp only [codeLocationsExp, List.mem_append] at h
      exact h.elim (sx' n) (sb' n)
    | raise trace body | tick trace body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨body', s1⟩, hb, rfl, rfl⟩ := run
      simpa [ExprLocationsWithin, codeLocationsExp] using
        callsFuel_locationsWithin P fuel body body' initial s1 hb (by simpa [ExprLocationsWithin, codeLocationsExp] using safe) aux
    | handle trace body handler =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨body', s1⟩, hb, ⟨handler', s2⟩, hh, rfl, rfl⟩ := run
      have sb : ExprLocationsWithin P body := by intro n h; apply safe n; simp [codeLocationsExp, h]
      have sh : ExprLocationsWithin P handler := by intro n h; apply safe n; simp [codeLocationsExp, h]
      obtain ⟨sb', a1⟩ := callsFuel_locationsWithin P fuel body body' initial s1 hb sb aux
      obtain ⟨sh', a2⟩ := callsFuel_locationsWithin P fuel handler handler' s1 s2 hh sh a1
      refine ⟨?_, a2⟩
      intro n h
      simp only [codeLocationsExp, List.mem_append] at h
      exact h.elim (sb' n) (sh' n)
    | call trace ticks dest xs | op trace dest xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, rfl, rfl⟩ := run
      simpa [ExprLocationsWithin, ListLocationsWithin, codeLocationsExp] using
        callsListFuel_locationsWithin P fuel xs xs' initial s1 hx (by simpa [ExprLocationsWithin, ListLocationsWithin, codeLocationsExp] using safe) aux
    | app trace loc fn xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨fn', s2⟩, hf, rest⟩ := run
      have sx : ListLocationsWithin P xs := by intro n h; apply safe n; simp [codeLocationsExp, h]
      have sf : ExprLocationsWithin P fn := by intro n h; apply safe n; simp [codeLocationsExp, h]
      obtain ⟨sx', a1⟩ := callsListFuel_locationsWithin P fuel xs xs' initial s1 hx sx aux
      obtain ⟨sf', a2⟩ := callsFuel_locationsWithin P fuel fn fn' s1 s2 hf sf a1
      cases loc <;> simp only at rest
      all_goals repeat' split at rest
      all_goals simp only [Option.some.injEq, Prod.mk.injEq] at rest
      all_goals obtain ⟨rfl, rfl⟩ := rest
      all_goals refine ⟨?_, a2⟩
      all_goals intro n h
      all_goals simp only [codeLocationsExp, codeLocations_append, codeLocations, List.append_nil,
        variables_codeLocations, List.mem_append] at h
      all_goals aesop
    | fn name loc vars arity body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨body', s1⟩, hb, closed, _, rest⟩ := run
      have bodySafe : ExprLocationsWithin P body := by intro n h; apply safe n; simp [codeLocationsExp, h]
      have own : P (loc.getD 0) := by apply safe; simp [codeLocationsExp]
      have inserted : AuxLocationsWithin P (insertEach (loc.getD 0) 1 initial) := by simpa [AuxLocationsWithin, insertEach] using aux
      obtain ⟨bodySafe', aux1⟩ := callsFuel_locationsWithin P fuel body body' _ s1 hb bodySafe inserted
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body'', s2⟩, hb', rfl, rfl⟩ := rest
        obtain ⟨bodySafe'', aux2⟩ := callsFuel_locationsWithin P fuel body body'' initial s2 hb' bodySafe aux
        refine ⟨?_, aux2⟩
        intro n h
        simp only [codeLocationsExp, List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact bodySafe'' n h
        · exact own
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        have generated : AuxLocationsWithin P (s1.1, (loc.getD 0 + 1, arity, body') :: s1.2) := by
          intro n a b member
          simp only [List.mem_cons, Prod.mk.injEq] at member
          rcases member with ⟨rfl, rfl, rfl⟩ | old
          · exact bodySafe'
          · exact aux1 n a b old
        refine ⟨?_, generated⟩
        intro n h
        simp [codeLocationsExp, variables_codeLocations] at h
        simpa [h] using own
    | letrec names loc vars fns body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨bodies, s1⟩, hb, closed, _, rest⟩ := run
      have groupSafe : ListLocationsWithin P (fns.map Prod.snd) := by
        intro n h
        apply safe n
        simp only [codeLocationsExp, List.mem_append]
        exact Or.inl (Or.inl (by simpa [codeLocationsFuns_map] using h))
      have bodySafe : ExprLocationsWithin P body := by
        intro n h
        apply safe n
        simp only [codeLocationsExp, List.mem_append]
        exact Or.inr h
      have own : ∀ i ∈ List.range fns.length, P (loc.getD 0 + 2 * i) := by
        intro i hi
        apply safe
        simp only [codeLocationsExp, List.mem_append]
        exact Or.inl (Or.inr (List.mem_map.mpr ⟨i, hi, rfl⟩))
      have inserted : AuxLocationsWithin P (insertEach (loc.getD 0) fns.length initial) := by
        simpa [AuxLocationsWithin, insertEach] using aux
      obtain ⟨bodiesSafe, aux1⟩ := callsListFuel_locationsWithin P fuel (fns.map Prod.snd) bodies _ s1 hb groupSafe inserted
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨bodies', s2⟩, hb', ⟨body', s3⟩, he, rfl, rfl⟩ := rest
        obtain ⟨bodiesSafe', aux2⟩ := callsListFuel_locationsWithin P fuel (fns.map Prod.snd) bodies' initial s2 hb' groupSafe aux
        obtain ⟨bodySafe', aux3⟩ := callsFuel_locationsWithin P fuel body body' s2 s3 he bodySafe aux2
        have lengths : bodies'.length = fns.length := by
          simpa using callsListFuel_length fuel (fns.map Prod.snd) initial s2 bodies' hb'
        refine ⟨?_, aux3⟩
        intro n h
        simp only [codeLocationsExp, List.mem_append, List.mem_map, List.mem_range] at h
        rcases h with (nested | ⟨i, hi, rfl⟩) | bodyMember
        · exact bodiesSafe' n (codeLocationsFuns_zip_subset _ _ nested)
        · apply own i
          simp only [List.mem_range]
          simpa [lengths] using hi
        · exact bodySafe' n bodyMember
      | true =>
        simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body', s2⟩, he, rfl, rfl⟩ := rest
        have auxGenerated := codeList_locationsWithin P (loc.getD 0) ((fns.map Prod.fst).zip bodies) s1 aux1
          (zip_bodies_locationsWithin P _ _ bodiesSafe)
        obtain ⟨bodySafe', aux2⟩ := callsFuel_locationsWithin P fuel body body' _ s2 he bodySafe auxGenerated
        refine ⟨?_, aux2⟩
        intro n h
        simp only [codeLocationsExp, callsList_codeLocationsFuns, callsList_length, List.nil_append,
          List.mem_append, List.mem_map, List.mem_range] at h
        rcases h with ⟨i, hi, rfl⟩ | bodyMember
        · exact own i (List.mem_range.mpr hi)
        · exact bodySafe' n bodyMember
termination_by fuel

/-- A successful direct-call list traversal preserves source and auxiliary
nested-location bounds. -/
theorem callsListFuel_locationsWithin (P : Nat → Prop) (fuel : Nat) (es out : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel fuel es initial = some (out, final))
    (safe : ListLocationsWithin P es) (aux : AuxLocationsWithin P initial) :
    ListLocationsWithin P out ∧ AuxLocationsWithin P final := by
  cases es with
  | nil =>
    simp [callsListFuel] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨safe, aux⟩
  | cons e es =>
    cases fuel with
    | zero => simp [callsListFuel] at run
    | succ fuel =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, he, ⟨es', s2⟩, hs, rfl, rfl⟩ := run
      have head : ExprLocationsWithin P e := by intro n h; apply safe n; simp [codeLocations, h]
      have tail : ListLocationsWithin P es := by intro n h; apply safe n; simp [codeLocations, h]
      obtain ⟨se, a1⟩ := callsFuel_locationsWithin P fuel e e' initial s1 he head aux
      obtain ⟨ss, a2⟩ := callsListFuel_locationsWithin P fuel es es' s1 s2 hs tail a1
      refine ⟨?_, a2⟩
      intro n h
      simp only [codeLocations, List.mem_append] at h
      exact h.elim (se n) (ss n)
termination_by fuel
end


/-- The production retry traversal preserves nested-location bounds. -/
theorem callsListBounded_locationsWithin (P : Nat → Prop) (fuel : Nat)
    (es out : List ClosLang.Exp) (initial final : State)
    (run : callsListBounded fuel es initial = some (out, final))
    (safe : ListLocationsWithin P es) (aux : AuxLocationsWithin P initial) :
    ListLocationsWithin P out ∧ AuxLocationsWithin P final := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | none => exact callsListFuel_locationsWithin P _ es out initial final (by simpa [first] using run) safe aux
  | some result =>
    have eq : result = (out, final) := by simpa [first] using run
    subst result
    exact callsListFuel_locationsWithin P fuel es out initial final first safe aux

/-- The initial production pass keeps every nested location in its input. -/
theorem compileFuel_locationsWithin (P : Nat → Prop) (fuel : Nat) (es out : List ClosLang.Exp) (final : State)
    (run : compileFuel fuel true es = some (out, final)) (safe : ListLocationsWithin P es) :
    ListLocationsWithin P out ∧ AuxLocationsWithin P final := by
  apply callsListBounded_locationsWithin P fuel es out (.ln, []) final ?_ safe (by simp [AuxLocationsWithin])
  simpa [compileFuel] using run

/-- Incremental direct-call output and generated bodies retain the source
nested-location bound. -/
theorem compileIncFuel_locationsWithin (P : Nat → Prop) (fuel : Nat) (known nextKnown : NumSet)
    (program converted : ClosSem.Program)
    (run : compileIncFuel? fuel known program = some (nextKnown, converted))
    (safe : ListLocationsWithin P program.1) :
    ListLocationsWithin P converted.1 ∧ AuxLocationsWithin P (nextKnown, converted.2) := by
  simp only [compileIncFuel?, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨output, state⟩, traversal, knownEq, outputEq, auxEq⟩ := run
  subst nextKnown
  simpa using callsListBounded_locationsWithin P fuel program.1 output (known, []) state traversal safe (by simp [AuxLocationsWithin])

/-- Each transformed oracle entry keeps nested locations within the
corresponding source entry's locations. -/
theorem compileIncFuelOracle_locationsWithin {C : Type} (fuel : Nat)
    (oracle : ClosSem.CompileOracle (NumSet × C)) (index : Nat) :
    ListLocationsWithin (fun loc => loc ∈ codeLocations (oracle index).2.1)
        (compileIncFuelOracle fuel oracle index).2.1 ∧
      AuxLocationsWithin (fun loc => loc ∈ codeLocations (oracle index).2.1)
        ((compileIncFuelTotal fuel (oracle index).1.1 (oracle index).2).1,
          (compileIncFuelOracle fuel oracle index).2.2) := by
  obtain ⟨nextKnown, run, _⟩ := compileIncFuelOracle_entry fuel oracle index
  have result := compileIncFuel_locationsWithin (fun loc => loc ∈ codeLocations (oracle index).2.1)
    fuel (oracle index).1.1 nextKnown (oracle index).2 (compileIncFuelOracle fuel oracle index).2 run
    (by intro _ member; exact member)
  have nextEq : nextKnown = (compileIncFuelTotal fuel (oracle index).1.1 (oracle index).2).1 := by
    have total := compileIncFuel_eq_total fuel (oracle index).1.1 (oracle index).2
    rw [run] at total
    exact congrArg Prod.fst (Option.some.inj total)
  simpa [nextEq] using result

end Flapjack.Compiler.Backend.ClosCall
