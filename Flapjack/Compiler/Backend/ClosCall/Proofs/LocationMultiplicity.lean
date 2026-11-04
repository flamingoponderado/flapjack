import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationSafety

/-! Direct-call conversion does not duplicate nested closure locations. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

mutual
/-- A successful expression traversal does not increase any location count. -/
theorem callsFuel_locationCount (fuel : Nat) (e out : ClosLang.Exp) (initial final : State)
    (run : callsFuel fuel e initial = some (out, final)) (loc : Nat) :
    (codeLocationsExp out).count loc ≤ (codeLocationsExp e).count loc := by
  cases fuel with
  | zero => simp [callsFuel] at run
  | succ fuel =>
    cases e with
    | var tr n => simp [callsFuel] at run; obtain ⟨rfl, rfl⟩ := run; simp
    | ifThenElse tr x y z =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, ⟨z', s3⟩, hz, rfl, rfl⟩ := run
      have a := callsFuel_locationCount fuel x x' initial s1 hx loc
      have b := callsFuel_locationCount fuel y y' s1 s2 hy loc
      have c := callsFuel_locationCount fuel z z' s2 s3 hz loc
      simp only [codeLocationsExp, List.count_append]; omega
    | «let» tr xs body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨body', s2⟩, hb, rfl, rfl⟩ := run
      have a := callsListFuel_locationCount fuel xs xs' initial s1 hx loc
      have b := callsFuel_locationCount fuel body body' s1 s2 hb loc
      simp only [codeLocationsExp, List.count_append]; omega
    | raise tr body | tick tr body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨body', s1⟩, hb, rfl, rfl⟩ := run
      exact callsFuel_locationCount fuel body body' initial s1 hb loc
    | handle tr body handler =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨body', s1⟩, hb, ⟨handler', s2⟩, hh, rfl, rfl⟩ := run
      have a := callsFuel_locationCount fuel body body' initial s1 hb loc
      have b := callsFuel_locationCount fuel handler handler' s1 s2 hh loc
      simp only [codeLocationsExp, List.count_append]; omega
    | call tr ticks dest xs | op tr dest xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, rfl, rfl⟩ := run
      exact callsListFuel_locationCount fuel xs xs' initial s1 hx loc
    | app tr target fn xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨fn', s2⟩, hf, rest⟩ := run
      have a := callsListFuel_locationCount fuel xs xs' initial s1 hx loc
      have b := callsFuel_locationCount fuel fn fn' s1 s2 hf loc
      cases target <;> simp only at rest
      all_goals repeat' split at rest
      all_goals simp only [Option.some.injEq, Prod.mk.injEq] at rest
      all_goals obtain ⟨rfl, rfl⟩ := rest
      all_goals simp only [codeLocationsExp, codeLocations_append, codeLocations, List.append_nil,
        variables_codeLocations, List.count_append] at *
      all_goals omega
    | fn name target vars arity body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨body', s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body'', s2⟩, hb', rfl, rfl⟩ := rest
        have a := callsFuel_locationCount fuel body body'' initial s2 hb' loc
        simp only [codeLocationsExp, List.count_append]; omega
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        simp only [codeLocationsExp, variables_codeLocations, List.count_append, List.count_nil, Nat.zero_add]
        omega
    | letrec names target vars fns body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨bodies, s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨bodies', s2⟩, hb', ⟨body', s3⟩, he, rfl, rfl⟩ := rest
        have lengths : (fns.map Prod.fst).length = bodies'.length := by
          simpa using (callsListFuel_length fuel (fns.map Prod.snd) initial s2 bodies' hb').symm
        have lengthBodies : bodies'.length = fns.length := by simpa using lengths.symm
        have a := callsListFuel_locationCount fuel (fns.map Prod.snd) bodies' initial s2 hb' loc
        have b := callsFuel_locationCount fuel body body' s2 s3 he loc
        simp only [codeLocationsExp, codeLocationsFuns_zip_eq _ _ lengths, List.length_zip,
          lengths, Nat.min_self, lengthBodies, codeLocationsFuns_map, List.count_append]
        omega
      | true =>
        simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body', s2⟩, he, rfl, rfl⟩ := rest
        have b := callsFuel_locationCount fuel body body' _ s2 he loc
        simp only [codeLocationsExp, callsList_codeLocationsFuns, callsList_length,
          List.nil_append, List.count_append]
        omega
termination_by fuel

/-- A successful list traversal does not increase any location count. -/
theorem callsListFuel_locationCount (fuel : Nat) (es out : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel fuel es initial = some (out, final)) (loc : Nat) :
    (codeLocations out).count loc ≤ (codeLocations es).count loc := by
  cases es with
  | nil => simp [callsListFuel] at run; obtain ⟨rfl, rfl⟩ := run; simp
  | cons e es =>
    cases fuel with
    | zero => simp [callsListFuel] at run
    | succ fuel =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, he, ⟨es', s2⟩, hs, rfl, rfl⟩ := run
      have a := callsFuel_locationCount fuel e e' initial s1 he loc
      have b := callsListFuel_locationCount fuel es es' s1 s2 hs loc
      simp only [codeLocations, List.count_append]; omega
termination_by fuel
end

/-- The production retry wrapper does not increase a location count. -/
theorem callsListBounded_locationCount (fuel : Nat) (es out : List ClosLang.Exp)
    (initial final : State) (run : callsListBounded fuel es initial = some (out, final))
    (loc : Nat) : (codeLocations out).count loc ≤ (codeLocations es).count loc := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | none => exact callsListFuel_locationCount _ es out initial final (by simpa [first] using run) loc
  | some result =>
    have eq : result = (out, final) := by simpa [first] using run
    subst result
    exact callsListFuel_locationCount fuel es out initial final first loc

/-- Direct-call conversion preserves distinct main-expression locations. -/
theorem callsListBounded_locations_nodup (fuel : Nat) (es out : List ClosLang.Exp)
    (initial final : State) (run : callsListBounded fuel es initial = some (out, final))
    (distinct : (codeLocations es).Nodup) : (codeLocations out).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro loc
  exact (callsListBounded_locationCount fuel es out initial final run loc).trans
    (List.nodup_iff_count_le_one.mp distinct loc)

/-- The enabled initial pass preserves distinct main-expression locations. -/
theorem compileFuel_locations_nodup (fuel : Nat) (es out : List ClosLang.Exp) (final : State)
    (run : compileFuel fuel true es = some (out, final))
    (distinct : (codeLocations es).Nodup) : (codeLocations out).Nodup := by
  apply callsListBounded_locations_nodup fuel es out (.ln, []) final ?_ distinct
  simpa [compileFuel] using run

/-- Incremental conversion preserves distinct main-expression locations. -/
theorem compileIncFuel_locations_nodup (fuel : Nat) (known nextKnown : NumSet)
    (program converted : ClosSem.Program)
    (run : compileIncFuel? fuel known program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup) : (codeLocations converted.1).Nodup := by
  simp only [compileIncFuel?, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨output, state⟩, traversal, knownEq, outputEq, auxEq⟩ := run
  simpa using callsListBounded_locations_nodup fuel program.1 output (known, []) state traversal distinct

/-- Each incrementally converted oracle entry has distinct main-expression
locations when its source entry does. -/
theorem compileIncFuelOracle_locations_nodup {C : Type} (fuel : Nat)
    (oracle : ClosSem.CompileOracle (NumSet × C)) (index : Nat)
    (distinct : (codeLocations (oracle index).2.1).Nodup) :
    (codeLocations (compileIncFuelOracle fuel oracle index).2.1).Nodup := by
  obtain ⟨nextKnown, run, _⟩ := compileIncFuelOracle_entry fuel oracle index
  exact compileIncFuel_locations_nodup fuel (oracle index).1.1 nextKnown
    (oracle index).2 (compileIncFuelOracle fuel oracle index).2 run distinct

end Flapjack.Compiler.Backend.ClosCall
