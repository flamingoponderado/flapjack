import Flapjack.RiscV.AllocatorCorrectness
import Flapjack.RiscV.CorrectnessBackend

/-!
Correctness of applying a register colouring to a small, executable Word
fragment. This is the first whole-program simulation statement for allocator
output: it covers straight-line programs made from `skip`, variable-to-
variable assignments, and sequencing.
-/

namespace Flapjack.RiscV

def wordColourValid (colour : Nat → Nat) : Prop :=
  ∀ name, name < 32 → colour name < 32

/-! The allocator's clash checker discharges the live-after no-alias premise
    for a single assignment.  The edge list is exactly the one-write
    interference relation generated from liveness; this remains untagged
    because it is a local consequence over Flapjack's list graph/checker, not
    HOL's full `colouring_ok` theorem over Word programs and live sets. -/
theorem wordColouringRespectsClashes_edge
    (colouring : NatInfoMap Nat) (left right : Nat)
    (edges : List (Nat × Nat))
    (hchecked : wordColouringRespectsClashes edges colouring = true)
    (hedge : (left, right) ∈ edges) :
    ∃ leftColour rightColour,
      lookupNatInfo left colouring = some leftColour ∧
      lookupNatInfo right colouring = some rightColour ∧
      leftColour ≠ rightColour := by
  induction edges with
  | nil => simp at hedge
  | cons edge rest ih =>
      rcases edge with ⟨edgeLeft, edgeRight⟩
      rcases List.mem_cons.mp hedge with hhead | htail
      · have hpair : left = edgeLeft ∧ right = edgeRight := by
          simpa [Prod.mk.injEq] using hhead
        rcases hpair with ⟨rfl, rfl⟩
        cases hleft : lookupNatInfo left colouring with
        | none => simp [wordColouringRespectsClashes, hleft] at hchecked
        | some leftColour =>
          cases hright : lookupNatInfo right colouring with
          | none => simp [wordColouringRespectsClashes, hleft, hright] at hchecked
          | some rightColour =>
            have hboth : (leftColour != rightColour) &&
                wordColouringRespectsClashes rest colouring = true := by
              simpa [wordColouringRespectsClashes, hleft, hright] using hchecked
            have hparts : (leftColour != rightColour) = true ∧
                decide (wordColouringRespectsClashes rest colouring = true) = true := by
              simpa only [Bool.and_eq_true] using hboth
            have hneq : leftColour ≠ rightColour := by
              simpa using hparts.1
            exact ⟨leftColour, rightColour, rfl, rfl, hneq⟩
      · cases hleft : lookupNatInfo edgeLeft colouring with
        | none => simp [wordColouringRespectsClashes, hleft] at hchecked
        | some edgeLeftColour =>
          cases hright : lookupNatInfo edgeRight colouring with
          | none => simp [wordColouringRespectsClashes, hleft, hright] at hchecked
          | some edgeRightColour =>
            have hboth : (edgeLeftColour != edgeRightColour) &&
                wordColouringRespectsClashes rest colouring = true := by
              simpa [wordColouringRespectsClashes, hleft, hright] using hchecked
            have hparts : (edgeLeftColour != edgeRightColour) = true ∧
                decide (wordColouringRespectsClashes rest colouring = true) = true := by
              simpa only [Bool.and_eq_true] using hboth
            have htailChecked : wordColouringRespectsClashes rest colouring = true :=
              of_decide_eq_true hparts.2
            exact ih htailChecked htail

theorem wordColouringRespectsClashes_singleWrite_liveAfter_noAlias
    (colouring : NatInfoMap Nat) (destination : Nat)
    (liveAfter : List Nat) (edges : List (Nat × Nat)) (colour : Nat → Nat)
    (hchecked : wordColouringRespectsClashes edges colouring = true)
    (hcontains : ∀ current, current ∈ liveAfter → current ≠ destination →
      (destination, current) ∈ edges)
    (hlookup : ∀ name, name = destination ∨ name ∈ liveAfter →
      lookupNatInfo name colouring = some (colour name))
    (current : Nat) (hcurrent : current ∈ liveAfter)
    (hdifferent : current ≠ destination) :
    colour current ≠ colour destination := by
  have hedge : (destination, current) ∈ edges := hcontains current hcurrent hdifferent
  obtain ⟨leftColour, rightColour, hleft, hright, hneq⟩ :=
    wordColouringRespectsClashes_edge colouring destination current
      edges hchecked hedge
  have hleft' : leftColour = colour destination := by
    rw [hlookup destination (Or.inl rfl)] at hleft
    injection hleft with heq
    exact heq.symm
  have hright' : rightColour = colour current := by
    rw [hlookup current (Or.inr hcurrent)] at hright
    injection hright with heq
    exact heq.symm
  simpa [hleft', hright'] using hneq.symm

/-! Local checker bridge for one write's live-after conflict row. The generated
    edge list directly connects the destination with each surviving live name,
    so callers no longer provide a separate edge-coverage premise. This is an
    executable list encoding of the relevant `colouring_ok` injectivity
    obligation, not a port of HOL's recursive `colouring_ok` or
    `evaluate_apply_colour`. -/
def wordSingleWriteClashEdges (destination : Nat) (liveAfter : List Nat) :
    List (Nat × Nat) :=
  liveAfter.map (fun current => (destination, current))

theorem wordColouringRespectsClashes_singleWrite_map_noAlias
    (destination : Nat) (liveAfter : List Nat) (colour : Nat → Nat)
    (colouring : NatInfoMap Nat)
    (hchecked : wordColouringRespectsClashes
      (wordSingleWriteClashEdges destination liveAfter) colouring = true)
    (hlookup : ∀ name, name = destination ∨ name ∈ liveAfter →
      lookupNatInfo name colouring = some (colour name))
    (current : Nat) (hcurrent : current ∈ liveAfter)
    (hdifferent : current ≠ destination) :
    colour current ≠ colour destination := by
  apply wordColouringRespectsClashes_singleWrite_liveAfter_noAlias
    colouring destination liveAfter (wordSingleWriteClashEdges destination liveAfter)
    colour hchecked (fun name hname _ => by
      simp [wordSingleWriteClashEdges, hname]) hlookup current hcurrent hdifferent

theorem wordAllocateVarsWithClashes_noAliasOnLiveAfter
    (slots : List Nat) (edges : List (Nat × Nat))
    (colouring : NatInfoMap Nat)
    (hallocated : wordAllocateVarsWithClashes slots edges = some colouring)
    (destination : Nat) (liveAfter : List Nat) (colour : Nat → Nat)
    (hcontains : ∀ current, current ∈ liveAfter → current ≠ destination →
      (destination, current) ∈ edges)
    (hlookup : ∀ name, name = destination ∨ name ∈ liveAfter →
      lookupNatInfo name colouring = some (colour name))
    (current : Nat) (hcurrent : current ∈ liveAfter)
    (hdifferent : current ≠ destination) :
    colour current ≠ colour destination := by
  have hchecked := (wordAllocateVarsWithClashes_sound slots edges colouring hallocated).2
  exact wordColouringRespectsClashes_singleWrite_liveAfter_noAlias colouring destination
    liveAfter edges colour hchecked hcontains hlookup current hcurrent hdifferent

/-! Live-scoped Const assignment support for the HOL colouring simulation.
    It avoids global colour injectivity: only the destination versus names
    remaining live after the write must not clash. The explicit equality of
    source/target register zero is a Lean `State` invariant absent from the HOL
    `word_state_eq_rel` statement as represented here; this remains untagged
    support, not an exact `evaluate_apply_colour` port. -/

inductive WordVarStraightLine (width : Nat) : WordProg (Word width) → Prop where
  | skip : WordVarStraightLine width .skip
  | moveOne (name source : Nat) (hname : name < 32) (hsource : source < 32)
      (hname31 : name ≠ 31) (hsource31 : source ≠ 31)
      (hne : name ≠ source) :
      WordVarStraightLine width (.move 1 [(name, source)])
  | moveTwo (destinationOne sourceOne destinationTwo sourceTwo : Nat)
      (hdestinationOne : destinationOne < 32) (hsourceOne : sourceOne < 32)
      (hdestinationTwo : destinationTwo < 32) (hsourceTwo : sourceTwo < 32)
      (hdestinationOne31 : destinationOne ≠ 31) (hsourceOne31 : sourceOne ≠ 31)
      (hdestinationTwo31 : destinationTwo ≠ 31) (hsourceTwo31 : sourceTwo ≠ 31)
      (hdestinations : destinationOne ≠ destinationTwo)
      (hsourceOneDestinationOne : sourceOne ≠ destinationOne)
      (hsourceOneDestinationTwo : sourceOne ≠ destinationTwo)
      (hsourceTwoDestinationOne : sourceTwo ≠ destinationOne)
      (hsourceTwoDestinationTwo : sourceTwo ≠ destinationTwo) :
      WordVarStraightLine width
        (.move 1 [(destinationOne, sourceOne), (destinationTwo, sourceTwo)])
  | assign (name source : Nat) (hname : name < 32) (hsource : source < 32) :
      WordVarStraightLine width (.assign name (.var source))
  | assignConst (name : Nat) (value : Word width) (hname : name < 32) :
      WordVarStraightLine width (.assign name (.const value))
  | assignBinary (operator : BinOp) (name left right : Nat)
      (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
      WordVarStraightLine width (.assign name (.op operator [.var left, .var right]))
  | assignImmediate (operator : BinOp) (name source : Nat) (value : Word width)
      (hname : name < 32) (hsource : source < 32) :
      WordVarStraightLine width (.assign name (.op operator [.var source, .const value]))
  | assignShift (operator : Shift) (name left right : Nat) (hoperator : operator ≠ .ror)
      (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
      WordVarStraightLine width (.assign name (.shift operator (.var left) (.var right)))
  | assignShiftImmediate (operator : Shift) (name left : Nat) (amount : Word width)
      (hoperator : operator ≠ .ror) (hname : name < 32) (hleft : left < 32) :
      WordVarStraightLine width (.assign name (.shift operator (.var left) (.const amount)))
  | seq {first second : WordProg (Word width)} :
      WordVarStraightLine width first → WordVarStraightLine width second →
      WordVarStraightLine width (.seq first second)

/-! Every coloured program in the restricted variable straight-line fragment
    is also accepted by the backend's structural straight-line contract.  The
    latter deliberately permits a wider set of leaves; this bridge lets the
    allocator simulation be composed with the generic Word-to-RISC-V soundness
    theorem without duplicating the backend grammar. -/

theorem wordVarStraightLine_to_wordRiscVStraightLine [NeZero width]
    (colour : Nat → Nat) (program : WordProg (Word width))
    (hprogram : WordVarStraightLine width program) :
    WordRiscVStraightLine (wordApplyColour colour program) := by
  induction hprogram with
  | skip => simpa [wordApplyColour] using (WordRiscVStraightLine.skip :
      WordRiscVStraightLine (.skip : WordProg (Word width)))
  | moveOne name source _ _ _ _ _ => simpa [wordApplyColour] using (WordRiscVStraightLine.move 1
      [(colour name, colour source)] : WordRiscVStraightLine
        (.move 1 [(colour name, colour source)]))
  | moveTwo destinationOne sourceOne destinationTwo sourceTwo _ _ _ _ _ _ _ _ _ _ _ =>
      simpa [wordApplyColour] using (WordRiscVStraightLine.move 1
      [(colour destinationOne, colour sourceOne),
       (colour destinationTwo, colour sourceTwo)] : WordRiscVStraightLine
        (.move 1 [(colour destinationOne, colour sourceOne),
          (colour destinationTwo, colour sourceTwo)]))
  | assign name source _ _ => simpa [wordApplyColour, wordApplyColourExp] using
      (WordRiscVStraightLine.assign
      (colour name) (WordExp.var (colour source)) : WordRiscVStraightLine
        (.assign (colour name) (.var (colour source))))
  | assignConst name value _ => simpa [wordApplyColour, wordApplyColourExp] using
      (WordRiscVStraightLine.assign
      (colour name) (WordExp.const value) : WordRiscVStraightLine
        (.assign (colour name) (.const value)))
  | assignBinary operator name left right _ _ _ =>
      simpa [wordApplyColour, wordApplyColourExp] using (WordRiscVStraightLine.assign
      (colour name) (WordExp.op operator [.var (colour left), .var (colour right)]) :
        WordRiscVStraightLine
          (.assign (colour name) (.op operator [.var (colour left), .var (colour right)])))
  | assignImmediate operator name source value _ _ =>
      simpa [wordApplyColour, wordApplyColourExp] using (WordRiscVStraightLine.assign
      (colour name) (WordExp.op operator [.var (colour source), .const value]) :
        WordRiscVStraightLine
          (.assign (colour name) (.op operator [.var (colour source), .const value])))
  | assignShift operator name left right _ _ _ _ =>
      simpa [wordApplyColour, wordApplyColourExp] using (WordRiscVStraightLine.assign
      (colour name) (WordExp.shift operator (.var (colour left)) (.var (colour right))) :
        WordRiscVStraightLine
          (.assign (colour name) (.shift operator (.var (colour left)) (.var (colour right)))))
  | assignShiftImmediate operator name left amount _ _ _ =>
      simpa [wordApplyColour, wordApplyColourExp] using
      (WordRiscVStraightLine.assign (colour name)
        (WordExp.shift operator (.var (colour left)) (.const amount)) :
        WordRiscVStraightLine
          (.assign (colour name) (.shift operator (.var (colour left)) (.const amount))))
  | seq _ _ ihFirst ihSecond => simpa [wordApplyColour] using
      (WordRiscVStraightLine.seq _ _ ihFirst ihSecond)

/-! The same machine boundary, lifted to the full-SSA graph allocator.  The
    allocator result remains explicit, while its colored output is connected
    to the backend grammar using the renamed full-SSA body witness. -/

theorem wordVarStraightLine_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour)
    (colourNoScratch : ∀ name, name < 31 → colour name ≠ 31)
    {program : WordProg (Word width)}
    (hprogram : WordVarStraightLine width program) :
    WordVarStraightLine width (wordApplyColour colour program) := by
  induction hprogram with
  | skip => simp [wordApplyColour]; exact .skip
  | moveOne name sourceName hname hsource hname31 hsource31 hne =>
      have hnameLT31 : name < 31 := by omega
      have hsourceLT31 : sourceName < 31 := by omega
      simpa [wordApplyColour] using
        (.moveOne (colour name) (colour sourceName)
          (valid name hname) (valid sourceName hsource)
          (colourNoScratch name hnameLT31)
          (colourNoScratch sourceName hsourceLT31)
          (by intro h; apply hne; exact injective h))
  | moveTwo destinationOne sourceOne destinationTwo sourceTwo
      hdestinationOne hsourceOne hdestinationTwo hsourceTwo
      hdestinationOne31 hsourceOne31 hdestinationTwo31 hsourceTwo31
      hdestinations hsourceOneDestinationOne hsourceOneDestinationTwo
      hsourceTwoDestinationOne hsourceTwoDestinationTwo =>
      have hdestinationOneLT31 : destinationOne < 31 := by omega
      have hsourceOneLT31 : sourceOne < 31 := by omega
      have hdestinationTwoLT31 : destinationTwo < 31 := by omega
      have hsourceTwoLT31 : sourceTwo < 31 := by omega
      simpa [wordApplyColour] using
        (.moveTwo (colour destinationOne) (colour sourceOne)
          (colour destinationTwo) (colour sourceTwo)
          (valid destinationOne hdestinationOne) (valid sourceOne hsourceOne)
          (valid destinationTwo hdestinationTwo) (valid sourceTwo hsourceTwo)
          (colourNoScratch destinationOne hdestinationOneLT31)
          (colourNoScratch sourceOne hsourceOneLT31)
          (colourNoScratch destinationTwo hdestinationTwoLT31)
          (colourNoScratch sourceTwo hsourceTwoLT31)
          (by intro h; apply hdestinations; exact injective h)
          (by intro h; apply hsourceOneDestinationOne; exact injective h)
          (by intro h; apply hsourceOneDestinationTwo; exact injective h)
          (by intro h; apply hsourceTwoDestinationOne; exact injective h)
          (by intro h; apply hsourceTwoDestinationTwo; exact injective h))
  | assign name sourceName hname hsource =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assign (colour name) (colour sourceName)
          (valid name hname) (valid sourceName hsource))
  | assignConst name value hname =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignConst (colour name) value (valid name hname))
  | assignBinary operator name left right hname hleft hright =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignBinary operator (colour name) (colour left) (colour right)
          (valid name hname) (valid left hleft) (valid right hright))
  | assignImmediate operator name sourceName value hname hsource =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignImmediate operator (colour name) (colour sourceName) value
          (valid name hname) (valid sourceName hsource))
  | assignShift operator name left right hoperator hname hleft hright =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignShift operator (colour name) (colour left) (colour right)
          hoperator (valid name hname) (valid left hleft) (valid right hright))
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignShiftImmediate operator (colour name) (colour left) amount
          hoperator (valid name hname) (valid left hleft))
  | @seq first second hfirst hsecond ihFirst ihSecond =>
      simpa [wordApplyColour] using .seq ihFirst ihSecond

end Flapjack.RiscV
