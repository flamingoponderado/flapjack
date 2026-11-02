import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CodeRelation

/-! Reserved labels produced by the executed data-to-word stubs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Mapping a successful stub lookup retains the requested labels in order. -/
private theorem mapM_stub_labels {α : Type} (locations : List Nat) (lookup : Nat → Option (Nat × α))
    (entries : List (Nat × Nat × α))
    (run : (locations.mapM fun loc => do
      let (arity, body) ← lookup loc
      pure (loc, arity, body)) = some entries) :
    entries.map Prod.fst = locations := by
  induction locations generalizing entries with
  | nil => simp at run; subst entries; rfl
  | cons loc rest ih =>
    cases found : lookup loc with
    | none => simp [List.mapM_cons, found] at run
    | some result =>
      obtain ⟨arity, body⟩ := result
      cases tail : (rest.mapM fun loc => do
        let (arity, body) ← lookup loc
        pure (loc, arity, body)) with
      | none =>
        simp only [List.mapM_cons, found, tail] at run
        contradiction
      | some restEntries =>
        have same : (loc, arity, body) :: restEntries = entries := by
          simp only [List.mapM_cons, found, tail] at run
          exact Option.some.inj run
        subst entries
        simp [ih restEntries tail]

/-- The fixed-prefix locations are independent of the data configuration. -/
theorem fixedStubs64_labels (conf : Config) :
    ((fixedStubs? (width := 64) conf).getD []).map Prod.fst =
      [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
       29, 30, 31, 33, 34, 35, 36, 37, 38, 24, 25, 26, 27, 28, 32] := by
  obtain ⟨entries, run⟩ := fixedStubs64_succeeds conf
  have labels := mapM_stub_labels _ (compileConfiguredStub? (width := 64) conf) entries run
  rw [run]
  simpa [fixedStubs?, fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
    replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation, divLocation,
    modLocation, compare1Location, compareLocation, equal1Location, equalLocation, longDiv1Location,
    longDivLocation, installLocation, installCodeLocation, installDataLocation, appendLocation,
    appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation, unusedLocation, stringCmpLoopLocation,
    memCopyLocation, byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
    dummyLocation, wordNumStubs, stackNumStubs] using labels

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1200000 in
/-- The generated 64-bit bignum program has the following entry labels. This
is kernel evaluation of the executed generator, not a HOL correspondence. -/
theorem bignumStubs64_labels :
    ((WordBignum.generateStubs 64 bignumLocation).getD []).map Prod.fst =
      [39, 61, 60, 59, 58, 54, 57, 56, 55, 53, 52, 51, 50, 49, 47, 48, 46, 45, 44, 43, 42, 41, 40] := by
  decide +kernel

/-- Every executed runtime stub has a unique label below the first source
function label reserved by the data-to-word backend. -/
theorem runtimeStubs64_labels (conf : Config) :
    ((runtimeStubs64 conf).map Prod.fst).Nodup ∧
      ∀ label ∈ (runtimeStubs64 conf).map Prod.fst, label < dataNumStubs := by
  simp only [runtimeStubs64, List.map_append, fixedStubs64_labels, bignumStubs64_labels]
  decide +kernel

/-- User functions with distinct labels outside the reserved stub range can
be appended to the generated stubs without collisions. -/
theorem runtimeStubs64_append_labels (conf : Config) (entries : List (Nat × Nat × DataLang.Prog))
    (distinct : (entries.map Prod.fst).Nodup)
    (above : ∀ label ∈ entries.map Prod.fst, dataNumStubs ≤ label) :
    ((runtimeStubs64 conf ++ entries.map (compilePart64 conf)).map Prod.fst).Nodup := by
  have names : (entries.map (compilePart64 conf)).map Prod.fst = entries.map Prod.fst := by
    rw [List.map_map]
    apply List.map_congr_left
    intro entry _
    obtain ⟨name, args, body⟩ := entry
    rfl
  rw [List.map_append, names, List.nodup_append]
  refine ⟨(runtimeStubs64_labels conf).1, distinct, ?_⟩
  intro left inStubs right inEntries equal
  subst right
  exact Nat.not_lt_of_ge (above left inEntries) ((runtimeStubs64_labels conf).2 left inStubs)

/-- BVI-to-data compilation preserves the entry labels and their order. -/
theorem bviToData_labels (entries : List (Nat × Nat × Bvi.Exp)) :
    (BviToData.compileProg entries).map Prod.fst = entries.map Prod.fst := by
  simp only [BviToData.compileProg, List.map_map]
  apply List.map_congr_left
  intro entry _
  obtain ⟨name, args, body⟩ := entry
  rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
