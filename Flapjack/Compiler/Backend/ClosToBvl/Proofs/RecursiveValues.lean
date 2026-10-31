import Flapjack.Compiler.Backend.ClosToBvl.Proofs.RecursiveInstalled
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ValueRelation

/-! Value relations for constructed mutually recursive closure groups. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The source functions paired with their even-spaced BVL code labels. -/
def recursiveEntries (functions : List (Nat × ClosLang.Exp)) (base : Nat) :
    List ((Nat × ClosLang.Exp) × Nat) :=
  functions.zipIdx.map (fun (entry, index) => (entry, base + 2 * index))

/-- The target closure blocks stored in the shared recursive environment. -/
def recursiveValues (entries : List ((Nat × ClosLang.Exp) × Nat)) (ptr : Nat) : List BvlSem.Value :=
  entries.map (fun ((arity, _), label) =>
    .block 30 [.codePtr label, .number (Int.ofNat (arity - 1)), .refPtr true ptr])

private instance : Nonempty BvlSem.Value := ⟨.number 0⟩

/-- Once the shared array and generated code are installed, each source
recursive closure is related to its corresponding target closure block.
This candidate is untagged pending review of the state and value carriers. -/
theorem recursiveValue_related (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (functions : List (Nat × ClosLang.Exp)) (label ptr index : Nat)
    (sourceValues : List ClosSem.Value) (targetValues : List BvlSem.Value)
    (valuesRel : List.Forall₂ (vRel maxApp f refs code) sourceValues targetValues)
    (fresh : ¬ ∃ r, f.lookup r = some ptr)
    (stored : refs.lookup ptr = some (.valueArray
      (recursiveValues (recursiveEntries functions (label + numStubs maxApp)) ptr ++ targetValues)))
    (length : 1 < functions.length) (bound : index < functions.length)
    (locations : ClosProps.everyFnLocationSome (functions.map Prod.snd))
    (varsAnnotated : ClosProps.everyFnVarsSome (functions.map Prod.snd))
    (installed : closureCodeInstalled maxApp code (recursiveEntries functions (label + numStubs maxApp)) sourceValues) :
    vRel maxApp f refs code (.recclosure (some label) [] sourceValues functions index)
      (Flapjack.holEl index (recursiveValues (recursiveEntries functions (label + numStubs maxApp)) ptr)) := by
  let entries := recursiveEntries functions (label + numStubs maxApp)
  let targets := recursiveValues entries ptr
  have projections := recursiveEntries_projections functions (label + numStubs maxApp)
  have firstProjection : functions = entries.map Prod.fst := projections.1.symm
  have positions : entries.map Prod.snd = (List.range entries.length).map
      (fun n => label + numStubs maxApp + 2 * n) := by
    simpa [entries, recursiveEntries] using projections.2
  have closureRel : clRel maxApp (fun p => ∃ r, f.lookup r = some p) refs code
      (sourceValues, targetValues) (.recclosure (some label) [] sourceValues functions index)
      (Flapjack.holEl index targets) := by
    exact .mutualRec firstProjection rfl positions rfl fresh stored length bound locations varsAnnotated installed
  have targetsLength : targets.length = functions.length := by simp [targets, recursiveValues, entries, recursiveEntries]
  have targetShape : Flapjack.holEl index targets =
      .block 30 [.codePtr (label + numStubs maxApp + 2 * index),
        .number (Int.ofNat (functions[index].1 - 1)), .refPtr true ptr] := by
    rw [Flapjack.holEl_eq_getElem index targets (by omega)]
    simp [targets, recursiveValues, entries, recursiveEntries, List.getElem_zipIdx]
  rw [targetShape] at closureRel ⊢
  exact .closure valuesRel closureRel

/-- The entire source recursive closure bundle is pointwise related to the
blocks in the installed shared target array. -/
theorem recursiveValues_related (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (functions : List (Nat × ClosLang.Exp)) (label ptr : Nat)
    (sourceValues : List ClosSem.Value) (targetValues : List BvlSem.Value)
    (valuesRel : List.Forall₂ (vRel maxApp f refs code) sourceValues targetValues)
    (fresh : ¬ ∃ r, f.lookup r = some ptr)
    (stored : refs.lookup ptr = some (.valueArray
      (recursiveValues (recursiveEntries functions (label + numStubs maxApp)) ptr ++ targetValues)))
    (length : 1 < functions.length)
    (locations : ClosProps.everyFnLocationSome (functions.map Prod.snd))
    (varsAnnotated : ClosProps.everyFnVarsSome (functions.map Prod.snd))
    (installed : closureCodeInstalled maxApp code (recursiveEntries functions (label + numStubs maxApp)) sourceValues) :
    List.Forall₂ (vRel maxApp f refs code)
      ((List.range functions.length).map (fun index => .recclosure (some label) [] sourceValues functions index))
      (recursiveValues (recursiveEntries functions (label + numStubs maxApp)) ptr) := by
  apply List.forall₂_of_length_eq_of_get
  · simp [recursiveValues, recursiveEntries]
  · intro index sourceBound targetBound
    have bound : index < functions.length := by simpa using sourceBound
    have related := recursiveValue_related maxApp f refs code functions label ptr index sourceValues targetValues
      valuesRel fresh stored length bound locations varsAnnotated installed
    rw [Flapjack.holEl_eq_getElem index _ targetBound] at related
    simpa using related

end Flapjack.Compiler.Backend.ClosToBvl
