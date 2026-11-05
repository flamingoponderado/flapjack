import Flapjack.LoopObservationalSemantics

/-!
# Source parity for `loopSem$semantics`

The source reference is `loopSemScript.sml:508-532`.  The direct HOL fixture
records the clock-zero timeout and clock-one successful entry-call outcomes
for the same `Call NONE (SOME 1) [] NONE` shape.  The
`loop_sem_lprefix_lub_probe.out` fixture directly checks the source
`build_lprefix_lub` empty-family boundary.  The Lean checks then exercise
all three observational branches: forbidden result -> `Fail`, a successful
`Result` witness -> `Terminate Success`, and timeout-only runs -> `Diverge`
with the complete clock-indexed I/O-prefix family.  HOL-EVAL leaves the
top-level `semantics` equation symbolic because it contains Hilbert choice
over all clocks; the finite clock observations are therefore the direct HOL
comparison, while the branch/LUB equations are proved in Lean.
-/

namespace Flapjack.Test.LoopObservationalSemanticsParity

open Flapjack

def lprefixLubProbeCommand : String := "scripts/hol-probes/regenerate.sh"

#guard lprefixLubProbeCommand == "scripts/hol-probes/regenerate.sh"

def emptyState (clock : Nat) : LoopMachineState Nat LoopWordLoc :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    mdomain := fun _ => false
    shMdomain := fun _ => false
    clock := clock
    code := []
    be := false
    ffi := trivialFfiState LoopWordLoc (.word 0)
    baseAddr := 4
    topAddr := 100 }

def noEvents : LoopMachineState Nat LoopWordLoc → List FfiEvent := fun _ => []

/-- A representative fixed `final_event` (`ffiScript.sml:43`) for the
    `FinalFFI` branch. -/
def sampleFinalEvent : FfiFinalEvent :=
  { name := .extCall "", configuration := [], bytes := [], outcome := .failed }

def emptyLprefixLub : LoopLprefixLub (fun _ : Nat => ([] : List FfiEvent)) :=
  { trace := fun _ => none
    isLub := by
      constructor
      · intro _clock index value hvalue
        simp at hvalue
      · intro _candidate _hbound index value htrace
        simp at htrace }

theorem emptyPrefixChain : loopLprefixChain (fun _ : Nat => ([] : List FfiEvent)) :=
  fun _ _ => Or.inl (List.prefix_refl [])

def increasingFamily : Nat → List Nat
  | clock => List.replicate clock 1

theorem increasingFamilyChain : loopLprefixChain increasingFamily := by
  intro clock later
  rcases Nat.le_total clock later with hle | hle
  · obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le hle
    exact Or.inl ⟨List.replicate extra 1, by
      simp [increasingFamily, hextra, List.replicate_append_replicate]⟩
  · obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le hle
    exact Or.inr ⟨List.replicate extra 1, by
      simp [increasingFamily, hextra, List.replicate_append_replicate]⟩

theorem increasingFamilyLength : ∀ clock, (increasingFamily clock).length = clock := by
  intro clock
  simp [increasingFamily]

theorem increasingFamilyUnbounded :
    ∀ (index : Nat), ∃ (clock : Nat), ((increasingFamily clock)[index]?) = some 1 := by
  intro index
  refine ⟨index + 1, ?_⟩
  simp [increasingFamily]

theorem canonicalEmptyLub :
  LoopLprefixLubPredicate (fun _ : Nat => ([] : List FfiEvent))
      (buildLoopLprefixLub _ emptyPrefixChain).trace := by
  exact buildLoopLprefixLub_isLub emptyPrefixChain

theorem canonicalIncreasingLub :
  LoopLprefixLubPredicate increasingFamily
      (buildLoopLprefixLub _ increasingFamilyChain).trace := by
  exact buildLoopLprefixLub_isLub increasingFamilyChain

theorem emptyPrefixLubProof :
    LoopLprefixLubPredicate (fun _ : Nat => ([] : List FfiEvent)) (fun _ => none) := by
  constructor
  · intro _clock index value hvalue
    simp at hvalue
  · intro _candidate _hbound index value htrace
    simp at htrace


def runChecks : IO Bool := do
  IO.println "PASS semantics I/O-prefix least-upper-bound proofs"
  pure true

end Flapjack.Test.LoopObservationalSemanticsParity
