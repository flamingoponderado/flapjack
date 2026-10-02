import Flapjack.Compiler.Backend.WordToStack.ProductionScheduler
import Flapjack.Compiler.Backend.WordToStack.NativeMoves
import Flapjack.Compiler.Backend.StackLang.ProductionCodec
import Flapjack.Compiler.Backend.StackLang.MacroLeaves

/-! Flapjack implementation correspondence for actual move materialization.
There is no HOL declaration for this production AST projection. The existing
macro leaf projection supplies register arithmetic; the shared structural codec
supplies all other leaves. This does not change the executed compiler.
Identity suppression and normalized sequencing differ from literal wMoveAux;
caller-domain and semantic obligations remain before whole-route replacement.
-/
namespace Flapjack.ProductionMoves
open RiscV Compiler.Backend Compiler.Backend.StackLang Compiler.Encoders.Asm

/-- Expand arithmetic macro leaves using the existing emission-reviewed codec,
and recurse through move sequences. Other constructors retain the existing
partial structural codec, including all its rejection cases. -/
def project {width : Nat} [NeZero width] :
    StackProg (BitVec width) → Option (HolProg width)
  | .arith op d l r =>
      (MacroLeaves.project width (.arith op d l r)).bind productionToHolProg
  | .seq first second => do
      let first ← project first
      let second ← project second
      pure (.seq first second)
  | other => productionToHolProg other

/-- Exact actual move image, retaining production identity removal. -/
def locationMove {width : Nat} [NeZero width] (config : WordStackConfig)
    (destination source : WordLocation) : HolProg width :=
  match destination, source with
  | .register d, .register s =>
      if d = s then .skip else .inst (.arith (.binop .or d s (.reg s)))
  | .register d, .stack s => .stackLoad d (wordStackOffset config s)
  | .stack d, .register s => .stackStore s (wordStackOffset config d)
  | .stack d, .stack s =>
      if d = s then .skip else
        .seq (.stackLoad config.scratch (wordStackOffset config s))
          (.stackStore config.scratch (wordStackOffset config d))

/-- All actual location moves encode; no target-program or conversion-success
premise is required. Spill order and identity behavior are preserved. -/
theorem locationMove_project {width : Nat} [NeZero width]
    (config : WordStackConfig) (destination source : WordLocation) :
    (wordStackLocationMove (α := BitVec width) config destination source).bind project =
      some (locationMove config destination source) := by
  cases destination <;> cases source
  case register.register d s =>
    by_cases h : d = s <;>
      simp [wordStackLocationMove, locationMove, h, project, MacroLeaves.project,
        productionToHolProg, progFromProduction, progWToHolProg, Prog.map,
        wordLangInstToHOL, wordLangArithToHOL] <;> rfl
  case register.stack d s =>
    simp [wordStackLocationMove, locationMove, project,
      productionToHolProg, progFromProduction, progWToHolProg, Prog.map]
  case stack.register d s =>
    simp [wordStackLocationMove, locationMove, project,
      productionToHolProg, progFromProduction, progWToHolProg, Prog.map]
  case stack.stack d s =>
    by_cases h : d = s <;>
      simp [wordStackLocationMove, locationMove, h, project,
        productionToHolProg, progFromProduction, progWToHolProg, Prog.map]

/-- Actual temporary save image, including both reserved-register failures. -/
def toScratch {width : Nat} [NeZero width] (config : WordStackConfig) :
    WordLocation → Option (HolProg width)
  | .register r =>
      if r = config.scratch || r = config.addressScratch then none
      else some (.inst (.arith (.binop .or config.addressScratch r (.reg r))))
  | .stack slot => some (.stackLoad config.addressScratch (wordStackOffset config slot))

/-- Actual temporary restore image, retaining identical failure conditions. -/
def fromScratch {width : Nat} [NeZero width] (config : WordStackConfig) :
    WordLocation → Option (HolProg width)
  | .register r =>
      if r = config.scratch || r = config.addressScratch then none
      else some (.inst (.arith (.binop .or r config.addressScratch
        (.reg config.addressScratch))))
  | .stack slot => some (.stackStore config.addressScratch (wordStackOffset config slot))

theorem toScratch_project {width : Nat} [NeZero width]
    (config : WordStackConfig) (source : WordLocation) :
    (wordStackLocationMoveToScratch (α := BitVec width) config source).bind project =
      toScratch config source := by
  cases source with
  | register r =>
    by_cases h : (r = config.scratch || r = config.addressScratch) = true <;>
      simp [wordStackLocationMoveToScratch, toScratch, h, project, MacroLeaves.project,
        productionToHolProg, progFromProduction, progWToHolProg, Prog.map,
        wordLangInstToHOL, wordLangArithToHOL] <;> rfl
  | stack slot =>
    simp [wordStackLocationMoveToScratch, toScratch, project,
      productionToHolProg, progFromProduction, progWToHolProg, Prog.map]

theorem fromScratch_project {width : Nat} [NeZero width]
    (config : WordStackConfig) (destination : WordLocation) :
    (wordStackLocationMoveFromScratch (α := BitVec width) config destination).bind project =
      fromScratch config destination := by
  cases destination with
  | register r =>
    by_cases h : (r = config.scratch || r = config.addressScratch) = true <;>
      simp [wordStackLocationMoveFromScratch, fromScratch, h, project, MacroLeaves.project,
        productionToHolProg, progFromProduction, progWToHolProg, Prog.map,
        wordLangInstToHOL, wordLangArithToHOL] <;> rfl
  | stack slot =>
    simp [wordStackLocationMoveFromScratch, fromScratch, project,
      productionToHolProg, progFromProduction, progWToHolProg, Prog.map]

/-- Normalized production sequencing preserves codec acceptance. This is a
carrier fact; it does not equate normalized code with HOL's literal Seq tree. -/
theorem join_encodable {width : Nat} [NeZero width]
    (first second : StackProg (BitVec width))
    (hfirst : ∃ target, project first = some target)
    (hsecond : ∃ target, project second = some target) :
    ∃ target, project (wordStackJoin first second) = some target := by
  rcases hfirst with ⟨targetFirst, hfirst⟩
  rcases hsecond with ⟨targetSecond, hsecond⟩
  unfold wordStackJoin
  split
  · exact ⟨targetSecond, hsecond⟩
  · exact ⟨targetFirst, hfirst⟩
  · exact ⟨.seq targetFirst targetSecond, by simp [project, hfirst, hsecond]⟩

private theorem project_skip_iff {width : Nat} [NeZero width]
    (program : StackProg (BitVec width)) :
    project program = some .skip ↔ program = .skip := by
  cases program <;>
    simp [project, MacroLeaves.project, productionToHolProg, progFromProduction,
      progWToHolProg, Prog.map, wordLangInstToHOL, wordLangArithToHOL]
  case seq first second =>
    change ¬ Option.bind (project first) (fun first =>
      Option.bind (project second) (fun second => some (.seq first second : HolProg width))) =
        some (.skip : HolProg width)
    simp [Option.bind_eq_some_iff]
  case ite op condition right first second =>
    cases firstImage : progFromProduction first <;>
      cases secondImage : progFromProduction second <;>
        simp [progWToHolProg, Prog.map]
  case call returns target handler =>
    cases returns <;> cases handler <;> cases target <;>
      simp [progFromProduction, Prog.map, bind, pure, Option.bind_eq_some_iff]
    all_goals
      intro raw first _ second _ equal
      subst raw
      simp [Prog.map]

/-- Canonical image of the actual Skip-eliminating join. This normalization
is explicitly named; it is not HOL wMoveAux's literal constructor tree. -/
def join {width : Nat} [NeZero width] (first second : HolProg width) : HolProg width :=
  match first, second with
  | .skip, second => second
  | first, .skip => first
  | first, second => .seq first second

private theorem join_skip_right {width : Nat} [NeZero width] (program : HolProg width) :
    join program .skip = program := by cases program <;> rfl

/-- Projection commutes with the actual sequence normalization and preserves
failure. No caller success or desired image is assumed. -/
theorem join_project {width : Nat} [NeZero width]
    (first second : StackProg (BitVec width)) :
    project (wordStackJoin first second) = (do
      let first ← project first
      let second ← project second
      pure (join first second)) := by
  unfold wordStackJoin
  split
  · simp [project, productionToHolProg, progFromProduction, progWToHolProg, Prog.map, join]
  · simp [project, productionToHolProg, progFromProduction, progWToHolProg, Prog.map,
      join_skip_right]
  · rename_i excluded
    cases firstImage : project first with
    | none => simp [project, firstImage]
    | some targetFirst =>
      cases secondImage : project second with
      | none => simp [project, firstImage, secondImage]
      | some targetSecond =>
        have firstNotSkip : targetFirst ≠ .skip := by
          intro equal
          have original := (project_skip_iff first).mp (firstImage.trans (congrArg some equal))
          subst first
          simp_all
        have secondNotSkip : targetSecond ≠ .skip := by
          intro equal
          have original := (project_skip_iff second).mp (secondImage.trans (congrArg some equal))
          subst second
          simp_all
        simp only [project, firstImage, secondImage]
        change some (.seq targetFirst targetSecond : HolProg width) = some (join targetFirst targetSecond)
        congr 1
        unfold join
        first | rfl | split <;> simp_all

/-- Canonical materialization of actual optional locations, with precisely
the production's normalized sequencing and scratch rejection conditions.
It is not a redefinition of literal HOL wMoveAux. -/
def optionMoveList {width : Nat} [NeZero width] (config : WordStackConfig) :
    List (Option WordLocation × Option WordLocation) → Option (HolProg width)
  | [] => some .skip
  | (none, some source) :: moves => do
      let first ← toScratch config source
      let rest ← optionMoveList config moves
      pure (join first rest)
  | (some destination, some source) :: moves => do
      let rest ← optionMoveList config moves
      pure (join (locationMove config destination source) rest)
  | (some destination, none) :: moves => do
      let first ← fromScratch config destination
      let rest ← optionMoveList config moves
      pure (join first rest)
  | (none, none) :: _ => none

private theorem bind_join_project {width : Nat} [NeZero width]
    (first second : Option (StackProg (BitVec width))) :
    (do
      let first ← first
      let second ← second
      pure (wordStackJoin first second)).bind project = (do
        let first ← first.bind project
        let second ← second.bind project
        pure (join first second)) := by
  cases first <;> cases second <;> simp [bind, pure, join_project]

/-- Full actual optional-list projection, including every failure branch.
No accepted-result, conversion-success, native-result or evaluator premise.
This establishes the precise normalized image; native literal-tree and caller
domain obligations are still explicit rather than hidden in this equation. -/
theorem optionMoveList_project {width : Nat} [NeZero width]
    (config : WordStackConfig)
    (moves : List (Option WordLocation × Option WordLocation)) :
    (wordStackCakeOptionMoveList (α := BitVec width) config moves).bind project =
      optionMoveList config moves := by
  induction moves with
  | nil =>
    simp [wordStackCakeOptionMoveList, optionMoveList, project,
      productionToHolProg, progFromProduction, progWToHolProg, Prog.map]
  | cons move moves ih =>
    rcases move with ⟨destination, source⟩
    cases destination <;> cases source
    case none.none => simp [wordStackCakeOptionMoveList, optionMoveList]
    all_goals
      simp only [wordStackCakeOptionMoveList, optionMoveList]
      rw [bind_join_project]
      simp only [toScratch_project, fromScratch_project, locationMove_project, ih] <;> rfl

private theorem toScratch_isSome {width : Nat} [NeZero width]
    (config : WordStackConfig) (source : WordLocation) :
    (wordStackLocationMoveToScratch (α := BitVec width) config source).isSome =
      (toScratch (width := width) config source).isSome := by
  cases source with
  | register r =>
    by_cases h : (r = config.scratch || r = config.addressScratch) = true <;>
      simp [wordStackLocationMoveToScratch, toScratch, h]
  | stack slot => rfl

private theorem fromScratch_isSome {width : Nat} [NeZero width]
    (config : WordStackConfig) (destination : WordLocation) :
    (wordStackLocationMoveFromScratch (α := BitVec width) config destination).isSome =
      (fromScratch (width := width) config destination).isSome := by
  cases destination with
  | register r =>
    by_cases h : (r = config.scratch || r = config.addressScratch) = true <;>
      simp [wordStackLocationMoveFromScratch, fromScratch, h]
  | stack slot => rfl

private theorem toScratch_encodable {width : Nat} [NeZero width]
    (config : WordStackConfig) (source : WordLocation) (program : StackProg (BitVec width))
    (accepted : wordStackLocationMoveToScratch config source = some program) :
    ∃ target, project program = some target := by
  have present : (toScratch (width := width) config source).isSome = true := by
    rw [← toScratch_isSome, accepted]
    rfl
  cases result : toScratch (width := width) config source with
  | none => simp [result] at present
  | some target =>
    exact ⟨target, by simpa [accepted, result] using toScratch_project (width := width) config source⟩

private theorem fromScratch_encodable {width : Nat} [NeZero width]
    (config : WordStackConfig) (destination : WordLocation) (program : StackProg (BitVec width))
    (accepted : wordStackLocationMoveFromScratch config destination = some program) :
    ∃ target, project program = some target := by
  have present : (fromScratch (width := width) config destination).isSome = true := by
    rw [← fromScratch_isSome, accepted]
    rfl
  cases result : fromScratch (width := width) config destination with
  | none => simp [result] at present
  | some target =>
    exact ⟨target, by simpa [accepted, result] using fromScratch_project (width := width) config destination⟩

private theorem locationMove_encodable {width : Nat} [NeZero width]
    (config : WordStackConfig) (destination source : WordLocation)
    (program : StackProg (BitVec width))
    (accepted : wordStackLocationMove config destination source = some program) :
    ∃ target, project program = some target := by
  exact ⟨locationMove config destination source,
    by simpa [accepted] using locationMove_project (width := width) config destination source⟩

/-- Every accepted actual optional move list lies in the projection domain.
The premise is the actual materializer result, not a desired native program or
target evaluation. Rejections, including NONE/NONE and scratch conflicts, are
retained; literal native-tree correspondence remains a separate obligation. -/
theorem optionMoveList_encodable {width : Nat} [NeZero width]
    (config : WordStackConfig)
    (moves : List (Option WordLocation × Option WordLocation))
    (program : StackProg (BitVec width))
    (accepted : wordStackCakeOptionMoveList config moves = some program) :
    ∃ target, project program = some target := by
  induction moves generalizing program with
  | nil =>
    simp only [wordStackCakeOptionMoveList, Option.some.injEq] at accepted
    subst program
    exact ⟨.skip, by simp [project, productionToHolProg, progFromProduction,
      progWToHolProg, Prog.map]⟩
  | cons move moves ih =>
    rcases move with ⟨destination, source⟩
    cases destination <;> cases source
    case none.none => simp [wordStackCakeOptionMoveList] at accepted
    all_goals
      simp only [wordStackCakeOptionMoveList] at accepted
      change Option.bind _ (fun first => Option.bind
        (wordStackCakeOptionMoveList config moves)
        (fun rest => some (wordStackJoin first rest))) = some program at accepted
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at accepted
      rcases accepted with ⟨first, firstAccepted, rest, restAccepted, result⟩
      subst program
      apply join_encodable
      · first
        | exact toScratch_encodable config _ first firstAccepted
        | exact fromScratch_encodable config _ first firstAccepted
        | exact locationMove_encodable config _ _ first firstAccepted
      · exact ih rest restAccepted

/-- Interpret the already formatted native operands as actual locations. The
spill field is an offset, so natural subtraction is retained exactly. This map
is not claimed injective for arbitrary out-of-frame indices. -/
def formattedLocation (kf : Nat × Nat × Nat) : Sum Nat Nat → WordLocation
  | .inl register => .register register
  | .inr index => .stack (kf.2.1 - 1 - (index - kf.1))

/-- Native scratch and zero stack base for the single-move comparison. The
actual caller configuration discharges these fields in ProductionConfiguration;
this local record does not replace that full caller record. -/
def nativeMoveConfig (kf : Nat × Nat × Nat) : WordStackConfig :=
  { locations := [], scratch := kf.1, stackBase := 0 }

/-- Genuine nonidentity formatted moves agree with literal native wMoveSingle.
Distinct scalar inputs alone are insufficient: spill-offset saturation can
identify them. The actual scheduler-domain discharge remains open. -/
theorem locationMove_native {width : Nat} [NeZero width]
    (kf : Nat × Nat × Nat) (destination source : Sum Nat Nat)
    (different : formattedLocation kf destination ≠ formattedLocation kf source) :
    locationMove (width := width) (nativeMoveConfig kf)
      (formattedLocation kf destination) (formattedLocation kf source) =
      Compiler.Backend.WordToStack.Native.wMoveSingleNative (destination, source) kf := by
  cases destination <;> cases source <;>
    simp [formattedLocation, locationMove, nativeMoveConfig,
      wordStackOffset, Compiler.Backend.WordToStack.Native.wMoveSingleNative] at different ⊢
  all_goals simp [different]

end Flapjack.ProductionMoves
