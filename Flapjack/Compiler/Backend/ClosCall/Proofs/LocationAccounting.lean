import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMultiplicity

/-! Accounting for locations moved into generated auxiliary functions. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- Number of occurrences of a location in the bodies already emitted. -/
def auxLocationCount (state : State) (loc : Nat) : Nat :=
  (codeLocations (state.2.map (fun (_, _, body) => body))).count loc

/-- Emitting a function group moves exactly its body locations into the
auxiliary state. The order of the emitted bodies is immaterial for counts. -/
theorem codeList_auxLocationCount (base : Nat) (fns : List (Nat × ClosLang.Exp))
    (state : State) (loc : Nat) :
    auxLocationCount (codeList base fns state) loc =
      (codeLocationsFuns fns).count loc + auxLocationCount state loc := by
  rw [codeList_eq_source]
  induction fns generalizing base state with
  | nil => simp [codeListSource, codeLocationsFuns]
  | cons fn rest ih =>
    obtain ⟨arity, body⟩ := fn
    simp only [codeListSource, ih, codeLocationsFuns, List.count_append]
    simp only [auxLocationCount, List.map_cons, codeLocations, List.count_append]
    omega

mutual
/-- A successful traversal accounts for both retained and emitted locations. -/
theorem callsFuel_totalLocationCount (fuel : Nat) (e out : ClosLang.Exp) (initial final : State)
    (run : callsFuel fuel e initial = some (out, final)) (loc : Nat) :
    (codeLocationsExp out).count loc + auxLocationCount final loc ≤
      (codeLocationsExp e).count loc + auxLocationCount initial loc := by
  cases fuel with
  | zero => simp [callsFuel] at run
  | succ fuel =>
    cases e with
    | var tr n => simp [callsFuel] at run; obtain ⟨rfl, rfl⟩ := run; simp
    | ifThenElse tr x y z =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, ⟨z', s3⟩, hz, rfl, rfl⟩ := run
      have a := callsFuel_totalLocationCount fuel x x' initial s1 hx loc
      have b := callsFuel_totalLocationCount fuel y y' s1 s2 hy loc
      have c := callsFuel_totalLocationCount fuel z z' s2 s3 hz loc
      simp only [codeLocationsExp, List.count_append]; omega
    | «let» tr xs body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨body', s2⟩, hb, rfl, rfl⟩ := run
      have a := callsListFuel_totalLocationCount fuel xs xs' initial s1 hx loc
      have b := callsFuel_totalLocationCount fuel body body' s1 s2 hb loc
      simp only [codeLocationsExp, List.count_append]; omega
    | raise tr body | tick tr body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨body', s1⟩, hb, rfl, rfl⟩ := run
      exact callsFuel_totalLocationCount fuel body body' initial s1 hb loc
    | handle tr body handler =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨body', s1⟩, hb, ⟨handler', s2⟩, hh, rfl, rfl⟩ := run
      have a := callsFuel_totalLocationCount fuel body body' initial s1 hb loc
      have b := callsFuel_totalLocationCount fuel handler handler' s1 s2 hh loc
      simp only [codeLocationsExp, List.count_append]; omega
    | call tr ticks dest xs | op tr dest xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, rfl, rfl⟩ := run
      exact callsListFuel_totalLocationCount fuel xs xs' initial s1 hx loc
    | app tr target fn xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨fn', s2⟩, hf, rest⟩ := run
      have a := callsListFuel_totalLocationCount fuel xs xs' initial s1 hx loc
      have b := callsFuel_totalLocationCount fuel fn fn' s1 s2 hf loc
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
        have a := callsFuel_totalLocationCount fuel body body'' initial s2 hb' loc
        simp only [codeLocationsExp, List.count_append]; omega
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        have a := callsFuel_totalLocationCount fuel body body' _ s1 hb loc
        simp only [insertEach, auxLocationCount] at a
        simp only [codeLocationsExp, variables_codeLocations, List.count_append, List.count_nil, Nat.zero_add,
          auxLocationCount, List.map_cons, codeLocations]
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
        have a := callsListFuel_totalLocationCount fuel (fns.map Prod.snd) bodies' initial s2 hb' loc
        have b := callsFuel_totalLocationCount fuel body body' s2 s3 he loc
        simp only [codeLocationsExp, codeLocationsFuns_zip_eq _ _ lengths, List.length_zip,
          lengths, Nat.min_self, lengthBodies, codeLocationsFuns_map, List.count_append]
        omega
      | true =>
        simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body', s2⟩, he, rfl, rfl⟩ := rest
        have lengths : (fns.map Prod.fst).length = bodies.length := by
          simpa using (callsListFuel_length fuel (fns.map Prod.snd) _ s1 bodies hb).symm
        have a := callsListFuel_totalLocationCount fuel (fns.map Prod.snd) bodies _ s1 hb loc
        have b := callsFuel_totalLocationCount fuel body body' _ s2 he loc
        have stubs : codeLocations ((callsList (target.getD 0) fns).map Prod.snd) = [] := by
          rw [← codeLocationsFuns_map]
          exact callsList_codeLocationsFuns _ _
        simp only [insertEach, auxLocationCount] at a
        simp only [codeList_auxLocationCount, codeLocationsFuns_zip_eq _ _ lengths] at b
        simp only [codeLocationsExp, callsList_length, codeLocationsFuns_map, stubs,
          List.nil_append, List.count_append]
        simp only [auxLocationCount] at b ⊢
        omega
termination_by fuel

/-- List traversal accounts for both retained and emitted locations. -/
theorem callsListFuel_totalLocationCount (fuel : Nat) (es out : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel fuel es initial = some (out, final)) (loc : Nat) :
    (codeLocations out).count loc + auxLocationCount final loc ≤
      (codeLocations es).count loc + auxLocationCount initial loc := by
  cases es with
  | nil => simp [callsListFuel] at run; obtain ⟨rfl, rfl⟩ := run; simp
  | cons e es =>
    cases fuel with
    | zero => simp [callsListFuel] at run
    | succ fuel =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, he, ⟨es', s2⟩, hs, rfl, rfl⟩ := run
      have a := callsFuel_totalLocationCount fuel e e' initial s1 he loc
      have b := callsListFuel_totalLocationCount fuel es es' s1 s2 hs loc
      simp only [codeLocations, List.count_append]; omega
termination_by fuel
end

/-- The production retry wrapper retains the combined accounting bound. -/
theorem callsListBounded_totalLocationCount (fuel : Nat) (es out : List ClosLang.Exp)
    (initial final : State) (run : callsListBounded fuel es initial = some (out, final))
    (loc : Nat) : (codeLocations out).count loc + auxLocationCount final loc ≤
      (codeLocations es).count loc + auxLocationCount initial loc := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | none => exact callsListFuel_totalLocationCount _ es out initial final (by simpa [first] using run) loc
  | some result =>
    have eq : result = (out, final) := by simpa [first] using run
    subst result
    exact callsListFuel_totalLocationCount fuel es out initial final first loc

/-- With no incoming auxiliary bodies, conversion preserves distinctness
across the main expressions and all newly emitted bodies together. -/
theorem callsListBounded_all_locations_nodup (fuel : Nat) (es out : List ClosLang.Exp)
    (known : NumSet) (final : State)
    (run : callsListBounded fuel es (known, []) = some (out, final))
    (distinct : (codeLocations es).Nodup) :
    (codeLocations out ++ codeLocations (final.2.map (fun (_, _, body) => body))).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro loc
  have bound := callsListBounded_totalLocationCount fuel es out (known, []) final run loc
  simp only [auxLocationCount, List.map_nil, codeLocations, List.count_nil, Nat.add_zero] at bound
  rw [List.count_append]
  exact bound.trans (List.nodup_iff_count_le_one.mp distinct loc)

/-- Incremental direct-call conversion preserves combined location distinctness. -/
theorem compileIncFuel_all_locations_nodup (fuel : Nat) (known nextKnown : NumSet)
    (program converted : ClosSem.Program)
    (run : compileIncFuel? fuel known program = some (nextKnown, converted))
    (distinct : (codeLocations program.1).Nodup) :
    (codeLocations converted.1 ++ codeLocations (converted.2.map (fun (_, _, body) => body))).Nodup := by
  simp only [compileIncFuel?, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨output, state⟩, traversal, knownEq, outputEq, auxEq⟩ := run
  simpa using callsListBounded_all_locations_nodup fuel program.1 output known state traversal distinct

/-- Combined distinctness for each entry of an incremental oracle. -/
theorem compileIncFuelOracle_all_locations_nodup {C : Type} (fuel : Nat)
    (oracle : ClosSem.CompileOracle (NumSet × C)) (index : Nat)
    (distinct : (codeLocations (oracle index).2.1).Nodup) :
    (codeLocations (compileIncFuelOracle fuel oracle index).2.1 ++
      codeLocations ((compileIncFuelOracle fuel oracle index).2.2.map (fun (_, _, body) => body))).Nodup := by
  obtain ⟨nextKnown, run, _⟩ := compileIncFuelOracle_entry fuel oracle index
  exact compileIncFuel_all_locations_nodup fuel (oracle index).1.1 nextKnown
    (oracle index).2 (compileIncFuelOracle fuel oracle index).2 run distinct

end Flapjack.Compiler.Backend.ClosCall
