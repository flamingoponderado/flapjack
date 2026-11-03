import Flapjack.RiscV.CorrectnessSsa
import Flapjack.RiscV.CorrectnessColour

/-!
# SSA-renaming to colouring boundary

CakeML's SSA pass gives each assignment a fresh destination, while the
colouring pass applies one fixed name map to a whole program.  These are the
same transformation for a straight-line assignment when its RHS does not
read the destination.  This module records that equation and immediately
feeds it into the executable colouring simulation.
-/

namespace Flapjack.RiscV

def ssaAssignmentColour (ssa : WordSsaState) (name : Nat) : Nat → Nat :=
  fun current => if current = name then (wordSsaFresh ssa name).2
    else wordSsaRead ssa current

theorem lookupNatInfo_filter_ne (entries : NatInfoMap α) (current name : Nat)
    (hne : current ≠ name) :
    lookupNatInfo current (entries.filter (fun entry => entry.1 != name)) =
      lookupNatInfo current entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      by_cases hcurrent : entry.1 = current
      · have hentryName : entry.1 ≠ name := by
          intro heq
          exact hne (hcurrent.symm.trans heq)
        rw [show (entry :: entries).filter (fun entry => entry.1 != name) =
            entry :: entries.filter (fun entry => entry.1 != name) by
          simp [hentryName]]
        simp [lookupNatInfo, hcurrent]
      · by_cases hentry : entry.1 = name
        · have hnameCurrent : name ≠ current := Ne.symm hne
          simp [List.filter, lookupNatInfo, hentry, hnameCurrent, ih]
        · simp [lookupNatInfo, hcurrent, hentry, ih]

theorem ssaAssignmentColour_eq_wordSsaRead_fresh
    (ssa : WordSsaState) (name current : Nat) :
    ssaAssignmentColour ssa name current =
      wordSsaRead (wordSsaFresh ssa name).1 current := by
  by_cases hcurrent : current = name
  · subst current
    simp only [ssaAssignmentColour]
    rw [wordSsaRead_fresh_name]
    rfl
  · simp only [ssaAssignmentColour,if_neg hcurrent]
    exact (wordSsaRead_fresh_of_ne ssa name current hcurrent).symm

theorem wordSsaRenameProgram_assign_state
    (ssa : WordSsaState) (name : Nat) (value : WordExp (Word width))
    (hprogram : WordVarStraightLine width (.assign name value)) :
    (wordSsaRenameProgram ssa (.assign name value)).1 =
      (wordSsaFresh ssa name).1 := by
  cases hprogram with
  | assign name source hname hsource =>
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        wordSsaFresh, wordSsaRenameExp]

  | assignConst name value hname =>
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        wordSsaFresh, wordSsaRenameExp]
  | assignBinary operator name left right hname hleft hright =>
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        wordSsaFresh, wordSsaRenameExp]
  | assignImmediate operator name source value hname hsource =>
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        wordSsaFresh, wordSsaRenameExp]
  | assignShift operator name left right hoperator hname hleft hright =>
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        wordSsaFresh, wordSsaRenameExp]
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        wordSsaFresh, wordSsaRenameExp]

theorem wordSsaRenameProgram_seq [OfNat α 0]
    (ssa : WordSsaState) (first second : WordProg α) :
    wordSsaRenameProgram ssa (.seq first second) =
      let (ssaFirst, renamedFirst) := wordSsaRenameProgram ssa first
      let (ssaSecond, renamedSecond) :=
        wordSsaRenameProgram ssaFirst second
      (ssaSecond, .seq renamedFirst renamedSecond) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops]

/-! Before an SSA assignment, the destination's old value need not satisfy the
    eventual colouring relation: the generated code overwrites it. -/

theorem ssaRenameAssign_eq_applyColour
    [NeZero width] (ssa : WordSsaState) (name : Nat)
    (value : WordExp (Word width))
    (hprogram : WordVarStraightLine width (.assign name value))
    (hnot : name ∉ wordExpReadVars value) :
    (wordSsaRenameProgram ssa (.assign name value)).2 =
      wordApplyColour (ssaAssignmentColour ssa name)
        (.assign name value) := by
  cases hprogram with
  | assign name source hname hsource =>
      have hne : name ≠ source := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hne' : source ≠ name := Ne.symm hne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hne']
  | assignConst name value hname =>
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp]
  | assignBinary operator name left right hname hleft hright =>
      have hleft_ne : name ≠ left := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hright_ne : name ≠ right := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hleft_ne' : left ≠ name := Ne.symm hleft_ne
      have hright_ne' : right ≠ name := Ne.symm hright_ne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hleft_ne', hright_ne']
  | assignImmediate operator name source value hname hsource =>
      have hne : name ≠ source := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hne' : source ≠ name := Ne.symm hne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hne']
  | assignShift operator name left right hoperator hname hleft hright =>
      have hleft_ne : name ≠ left := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hright_ne : name ≠ right := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hleft_ne' : left ≠ name := Ne.symm hleft_ne
      have hright_ne' : right ≠ name := Ne.symm hright_ne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hleft_ne', hright_ne']
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      have hne : name ≠ left := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hne' : left ≠ name := Ne.symm hne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hne']

end Flapjack.RiscV
