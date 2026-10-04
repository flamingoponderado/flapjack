import Flapjack.Compiler.Backend.WordToStack.ProductionConfiguration
import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeSpillState
import Flapjack.Compiler.Backend.RegAlloc.ProductionExtraction

/-! Actual move-domain infrastructure. There is no standalone HOL declaration
for the production colouring carrier. Bounds are derived from emitted moves
and the real allocator frame formula, rather than assumed for a caller.
Whole production routing and call/ABI producer coverage remain separate. -/
namespace Flapjack.ProductionMoveDomain
open RiscV RiscV.CakeRegAlloc

private theorem fold_move_maximum (moves : List (Nat × Nat)) (initial : Nat) :
    initial ≤ moves.foldl (fun m p => max m (max p.1 p.2)) initial ∧
    ∀ p ∈ moves, p.1 ≤ moves.foldl (fun m p => max m (max p.1 p.2)) initial ∧
      p.2 ≤ moves.foldl (fun m p => max m (max p.1 p.2)) initial := by
  induction moves generalizing initial with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons]
    obtain ⟨floor, members⟩ := ih (max initial (max head.1 head.2))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) floor, ?_⟩
    intro p member
    rcases List.mem_cons.mp member with equal | member
    · subst p
      constructor <;> omega
    · exact members p member

/-- Both operands of every actual emitted Move are bounded by that program's
source-shaped maximum. No operand-bound premise is used. -/
theorem move_operands_le_maximum {α : Type} (priority : Nat)
    (moves : List (Nat × Nat)) (pair : Nat × Nat) (member : pair ∈ moves) :
    pair.1 ≤ wordProgCakeMaxVar (.move priority moves : WordProg α) ∧
    pair.2 ≤ wordProgCakeMaxVar (.move priority moves : WordProg α) := by
  simpa only [wordProgCakeMaxVar] using (fold_move_maximum moves 0).2 pair member

/-- Native scalar indices of emitted Move operands fit the real frame demand,
including the zero-frame case and arbitrary register count/argument area. -/
theorem move_operands_lt_frame {α : Type} (priority k : Nat)
    (moves : List (Nat × Nat)) (parameters : List Nat)
    (pair : Nat × Nat) (member : pair ∈ moves) :
    let maximum := wordProgCakeMaxVar (.move priority moves : WordProg α)
    let slots := max ((maximum / 2 + 1) - k) (parameters.length - k)
    pair.1 / 2 < k + slots ∧ pair.2 / 2 < k + slots := by
  have bounds := move_operands_le_maximum (α := α) priority moves pair member
  dsimp
  have first := Nat.div_le_div_right (c := 2) bounds.1
  have second := Nat.div_le_div_right (c := 2) bounds.2
  omega

/-- Occurrence in exactly the bodies lowered by the actual compiler. A tail
call's handler is erased, matching both the source maximum and accepted route
repair; it is deliberately absent from this occurrence relation. -/
inductive CompiledMove {α : Type} (pair : Nat × Nat) : WordProg α → Prop
  | move (priority : Nat) (moves : List (Nat × Nat)) (member : pair ∈ moves) :
      CompiledMove pair (.move priority moves)
  | seqLeft {first second} : CompiledMove pair first → CompiledMove pair (.seq first second)
  | seqRight {first second} : CompiledMove pair second → CompiledMove pair (.seq first second)
  | ifTrue {op condition right first second} :
      CompiledMove pair first → CompiledMove pair (.ite op condition right first second)
  | ifFalse {op condition right first second} :
      CompiledMove pair second → CompiledMove pair (.ite op condition right first second)
  | loop {liveIn body liveOut} : CompiledMove pair body →
      CompiledMove pair (.loop liveIn body liveOut)
  | mustTerminate {body} : CompiledMove pair body → CompiledMove pair (.mustTerminate body)
  | returnBody {values cutsets body returnLabel returnSection destination arguments handler} :
      CompiledMove pair body → CompiledMove pair
        (.call (some (values, cutsets, body, returnLabel, returnSection)) destination arguments handler)
  | handlerBody {values cutsets body returnLabel returnSection destination arguments
        exception handler handlerLabel handlerSection} :
      CompiledMove pair handler → CompiledMove pair
        (.call (some (values, cutsets, body, returnLabel, returnSection)) destination arguments
          (some (exception, handler, handlerLabel, handlerSection)))

/-- Every actually traversed Move occurrence fits the enclosing source-shaped
maximum. This includes nested return/exception code, without a blanket bound
on ignored tail handlers or unsupported instruction operands. -/
theorem compiledMove_operands_le_maximum {α : Type} {pair : Nat × Nat}
    {program : WordProg α} (occurs : CompiledMove pair program) :
    pair.1 ≤ wordProgCakeMaxVar program ∧ pair.2 ≤ wordProgCakeMaxVar program := by
  induction occurs with
  | move priority moves member => exact move_operands_le_maximum priority moves pair member
  | @returnBody values cutsets body returnLabel returnSection destination arguments handler occurrence ih =>
      cases handler with
      | none => simp only [wordProgCakeMaxVar]; omega
      | some entry =>
          rcases entry with ⟨exception, handlerBody, lab, sec⟩
          simp only [wordProgCakeMaxVar]
          omega
  | ifTrue _ ih =>
      cases ‹WordRegImm α› <;> simp_all only [wordProgCakeMaxVar] <;> omega
  | ifFalse _ ih =>
      cases ‹WordRegImm α› <;> simp_all only [wordProgCakeMaxVar] <;> omega
  | mustTerminate _ ih => simpa only [wordProgCakeMaxVar] using ih
  | _ => simp_all only [wordProgCakeMaxVar]; omega

/-- Actual nested scalar-domain bound, using the real enclosing maximum and
parameter-area floor. No frame-domain or injectivity premise is assumed. -/
theorem compiledMove_operands_lt_frame {α : Type} {pair : Nat × Nat}
    {program : WordProg α} (k : Nat) (parameters : List Nat)
    (occurs : CompiledMove pair program) :
    let slots := max ((wordProgCakeMaxVar program / 2 + 1) - k) (parameters.length - k)
    pair.1 / 2 < k + slots ∧ pair.2 / 2 < k + slots := by
  have bounds := compiledMove_operands_le_maximum occurs
  have first := Nat.div_le_div_right (c := 2) bounds.1
  have second := Nat.div_le_div_right (c := 2) bounds.2
  dsimp
  omega

/-- Concrete actual colouring/frame instance of the nested domain theorem.
The occurrence is in the real emitted coloured program, not a desired native
output; ABI-generated scheduler moves require their own producer discharge. -/
theorem colouredCompiledMove_operands_lt_frame {α : Type} (k : Nat)
    (parameters : List Nat) (program : WordProg α) (colouring : NatInfoMap Nat)
    (pair : Nat × Nat)
    (occurs : CompiledMove pair (wordApplyColour (CakeAlloc.totalColour colouring) program)) :
    pair.1 / 2 < k + (cakeColourFrameSlots k parameters program colouring).1 ∧
    pair.2 / 2 < k + (cakeColourFrameSlots k parameters program colouring).1 := by
  simpa only [cakeColourFrameSlots] using compiledMove_operands_lt_frame k parameters occurs

/-- Original even ABI names fit the argument-area floor by their actual range
construction. This does not assume that a general colouring fixes them. -/
theorem sourceAbiParameter_lt_frame (count k maximum name : Nat)
    (member : name ∈ wordSsaAbiParameters count) :
    name / 2 < k + max ((maximum / 2 + 1) - k) (count - k) := by
  obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp member
  have bounded := List.mem_range.mp inRange
  omega

/-- The actual shared SSA allocation result discharges frame occupancy for all
emitted nested moves. Success identifies the real result; no desired frame or
colouring equality is supplied by the caller. -/
theorem retainedConsumer_moveFrame {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (dead : WordProg α → WordProg α) (unreach : WordProg α → Option (WordProg α))
    (ssa : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label : Nat) (parameters : List Nat) (source : WordProg α)
    (output : CakeAllocationWithColour α)
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output)
    (pair : Nat × Nat) (occurs : CompiledMove pair output.colouredProgram) :
    pair.1 / 2 < cakeRiscVRegisterCount + output.allocation.nextSpill ∧
    pair.2 / 2 < cakeRiscVRegisterCount + output.allocation.nextSpill := by
  rw [WordAlloc.allocatorWithSsa_spillState dead unreach ssa label parameters source output produced]
  rw [cakeColourWordSpillState_nextSpill_eq_occupancy]
  exact compiledMove_operands_lt_frame cakeRiscVRegisterCount parameters occurs

private theorem lookup_member (entries : NatInfoMap Nat) (key value : Nat)
    (found : lookupNatInfo key entries = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp [lookupNatInfo] at found
  | cons entry rest ih =>
      rcases entry with ⟨other, stored⟩
      by_cases equal : other = key
      · subst other
        simp [lookupNatInfo] at found
        subst stored
        exact List.mem_cons_self
      · simp [lookupNatInfo, equal] at found
        exact List.mem_cons_of_mem _ (ih found)

/-- Actual initialized allocator output fixes every physical name, including
names absent from its clash-tree bijection. This covers explicit allocation
lookup and the real physical default separately, without a desired colour
premise or a bijection membership assumption. -/
theorem allocator_physicalColour (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fs : List Nat)
    (algorithm : CakeAlgorithm) (cost : Option (CakeNodeMap Nat)) (k : Nat)
    (moves : List (Nat × (Nat × Nat))) (output : NatInfoMap Nat) (name : Nat)
    (physical : name % 2 = 0)
    (allocated : cakeDoRegAllocFromState algorithm cost k moves (cakeMkBij tree)
      (cakeInitRaStateFromBij (cakeMkBij tree) tree forced fs) = some output) :
    CakeAlloc.totalColour output name = name := by
  obtain ⟨finalState, extracted, _⟩ :=
    regAllocFromState_preserves_fixed algorithm cost k moves (cakeMkBij tree) _ output allocated
  have lookup : lookupNatInfo name output =
      (lookupNatInfo name (cakeMkBij tree).toAllocator).map (cakeTagCol finalState) := by
    rw [extracted]
    exact RegAlloc.extractColor_lookup_all tree finalState name
  have decoded : CakeAlloc.spDefault output name = name / 2 := by
    rw [← spDefaultIndexed_corresponds]
    unfold cakeSpDefaultIndexed
    rw [spDefaultIndex_lookup]
    cases found : lookupNatInfo name (cakeMkBij tree).toAllocator with
    | none => simp [lookup, found, CakeAlloc.isPhyVar, physical]
    | some node =>
        have colour := regAlloc_physical_lookup tree forced fs algorithm cost k moves output
          name node (lookup_member _ _ _ found) physical allocated
        simp [colour]
  simp only [CakeAlloc.totalColour, decoded]
  omega

/-- Physical-name preservation for the real retained SSA consumer, for any
actual SSA/dead/unreachable producers. The observed successful allocation is
the only producer premise; no desired colour equality is assumed. -/
theorem retainedConsumer_physicalColour {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (dead : WordProg α → WordProg α) (unreach : WordProg α → Option (WordProg α))
    (ssa : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label : Nat) (parameters : List Nat) (source : WordProg α)
    (output : CakeAllocationWithColour α)
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output)
    (name : Nat) (physical : name % 2 = 0) :
    CakeAlloc.totalColour output.colouring name = name := by
  unfold cakeAllocateWordFunctionAfterDeadWithColourWithSsa at produced
  split at produced <;> simp_all
  cases ssaResult : ssa parameters.length source with
  | none => simp [ssaResult] at produced
  | some result =>
      rcases result with ⟨state, formals, body⟩
      simp only [ssaResult, Option.bind_some] at produced
      repeat' (split at produced <;> simp_all)
      all_goals rcases produced with ⟨_, _, _, rfl⟩
      all_goals apply allocator_physicalColour <;> assumption

/-- Actual ABI names after retained allocation fit the actual frame. This
combines the range producer, real physical colouring and spill-state producer;
there is no parameter-colour identity or arbitrary frame-domain premise. -/
theorem retainedConsumer_abiFrame {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (dead : WordProg α → WordProg α) (unreach : WordProg α → Option (WordProg α))
    (ssa : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label count : Nat) (source : WordProg α) (output : CakeAllocationWithColour α)
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa dead unreach ssa
      label (wordSsaAbiParameters count) source = some output)
    (name : Nat) (member : name ∈ wordSsaAbiParameters count) :
    CakeAlloc.totalColour output.colouring name / 2 <
      cakeRiscVRegisterCount + output.allocation.nextSpill := by
  have physical : name % 2 = 0 := by
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    omega
  rw [retainedConsumer_physicalColour dead unreach ssa label _ source output produced name physical]
  rw [WordAlloc.allocatorWithSsa_spillState dead unreach ssa label _ source output produced]
  rw [cakeColourWordSpillState_nextSpill_eq_occupancy]
  simpa only [cakeColourFrameSlots, CakeAllocationWithColour.colouredProgram,
    wordSsaAbiParameters, List.length_map, List.length_range] using
    sourceAbiParameter_lt_frame count cakeRiscVRegisterCount
      (wordProgCakeMaxVar output.colouredProgram) name member

/-- Actual nested Move identity suppression cannot conflate distinct native
scalar operands in its produced frame. Scalar equality is the native format
comparison; no arbitrary injectivity or frame-domain premise is retained. -/
theorem colouredMove_location_identity {α : Type} (k : Nat)
    (parameters : List Nat) (program : WordProg α) (colouring : NatInfoMap Nat)
    (pair : Nat × Nat)
    (occurs : CompiledMove pair (wordApplyColour (CakeAlloc.totalColour colouring) program))
    (equal : cakeColourLocation k (cakeColourFrameSlots k parameters program colouring).2 pair.1 =
      cakeColourLocation k (cakeColourFrameSlots k parameters program colouring).2 pair.2) :
    pair.1 / 2 = pair.2 / 2 := by
  have bounds := colouredCompiledMove_operands_lt_frame k parameters program colouring pair occurs
  have frame : (cakeColourFrameSlots k parameters program colouring).1 ≤
      (cakeColourFrameSlots k parameters program colouring).2 := by
    simp only [cakeColourFrameSlots]
    split <;> omega
  apply cakeColourLocation_even_injective k (cakeColourFrameSlots k parameters program colouring).2
  · omega
  · omega
  · simpa only [cakeColourLocation, Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using equal

/-- The actual tail-call register-argument producer (`take k`) emits only
indices below the register window, independently of the stack frame. -/
theorem registerArgument_index {α : Type} (arguments : List α) (k index : Nat)
    (member : index ∈ List.range (arguments.take k).length) : index < k := by
  have bound := List.mem_range.mp member
  rw [List.length_take] at bound
  omega

/-- The actual returning-call producer uses `take (k-1)` and ABI base one.
Every emitted destination is therefore below k, even with empty frames. -/
theorem valueArgument_index {α : Type} (arguments : List α) (k index : Nat)
    (member : index ∈ List.range (arguments.take (k - 1)).length) : 1 + index < k := by
  have bound := List.mem_range.mp member
  rw [List.length_take] at bound
  omega

/-- The four actual Cake FFI destinations at ABI base one are all in the real
RISC-V register window; hardware numbering remains a later encoding step. -/
theorem ffiDestination_register (index : Nat) (member : index ∈ List.range 4) :
    1 + index < cakeRiscVRegisterCount := by
  have bound := List.mem_range.mp member
  simp only [cakeRiscVRegisterCount]
  omega

private theorem fold_maximum_member (names : List Nat) (initial name : Nat)
    (member : name ∈ names) : name ≤ names.foldl max initial := by
  have floor : ∀ names : List Nat, ∀ initial : Nat, initial ≤ names.foldl max initial := by
    intro names
    induction names with
    | nil => simp
    | cons head tail ih => intro initial; simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
  induction names generalizing initial with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_trans (Nat.le_max_right _ _) (floor tail _)
      · exact ih _ member

/-- Every actual Return source operand (including the link value) fits the
literal maximum used by its coloured frame producer. -/
theorem returnSource_maximum {α : Type} (link : Nat) (values : List Nat) (name : Nat)
    (member : name ∈ link :: values) :
    name ≤ wordProgCakeMaxVar (.return link values : WordProg α) := by
  simp only [wordProgCakeMaxVar]
  rcases List.mem_cons.mp member with equal | member
  · subst name
    clear member
    have bound : link ≤ values.foldl max link := by
      induction values generalizing link with
      | nil => simp
      | cons head tail ih => simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
    exact bound
  · exact fold_maximum_member values link name member

/-- The actual Call argument sources are in the literal maximum for both
returning and tail calls; an erased tail handler is never consulted. -/
theorem callArgument_maximum {α : Type}
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat))
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordProg α × Nat × Nat)) (name : Nat)
    (member : name ∈ arguments) :
    name ≤ wordProgCakeMaxVar (.call returns target arguments handler) := by
  have bound := fold_maximum_member arguments 0 name member
  rcases returns with _ | ⟨values, cutsets, body, lab, sec⟩
  · simpa only [wordProgCakeMaxVar] using bound
  · rcases handler with _ | ⟨exception, body, lab, sec⟩
    all_goals simp only [wordProgCakeMaxVar]; omega

/-- All four actual FFI source operands fit the original maximum; live-cutset
bounds can only enlarge that maximum. -/
theorem ffiSource_maximum {α : Type} (function : FunName)
    (configuration configurationLength array arrayLength name : Nat)
    (live : List Nat × List Nat)
    (member : name ∈ [configuration, configurationLength, array, arrayLength]) :
    name ≤ wordProgCakeMaxVar
      (.ffi function configuration configurationLength array arrayLength live : WordProg α) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [wordProgCakeMaxVar]
  rcases member with rfl | rfl | rfl | rfl <;> omega

/-- Returning-call result destinations belong to the literal return maximum,
including source handlers; this is the producer of the actual return suffix. -/
theorem callDestination_maximum {α : Type} (values : List Nat)
    (cutsets : List Nat × List Nat) (body : WordProg α) (lab sec : Nat)
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordProg α × Nat × Nat)) (name : Nat)
    (member : name ∈ values) :
    name ≤ wordProgCakeMaxVar (.call (some (values, cutsets, body, lab, sec)) target arguments handler) := by
  have bound := fold_maximum_member values 0 name member
  rcases handler with _ | ⟨exception, handlerBody, handlerLab, handlerSec⟩
  all_goals simp only [wordProgCakeMaxVar]; omega

/-- Concrete scheduler operand roles, propagated only through code actually
compiled. No arbitrary bound or desired output is an occurrence constructor. -/
inductive SchedulerOperand {α : Type} (name : Nat) : WordProg α → Prop
  | move {pair program} : CompiledMove pair program → name ∈ [pair.1, pair.2] →
      SchedulerOperand name program
  | returnValue {link values} : name ∈ link :: values → SchedulerOperand name (.return link values)
  | callArgument {returns target arguments handler} : name ∈ arguments →
      SchedulerOperand name (.call returns target arguments handler)
  | callDestination {values cutsets body lab sec target arguments handler} : name ∈ values →
      SchedulerOperand name (.call (some (values, cutsets, body, lab, sec)) target arguments handler)
  | ffi {function configuration configurationLength array arrayLength live} :
      name ∈ [configuration, configurationLength, array, arrayLength] →
      SchedulerOperand name (.ffi function configuration configurationLength array arrayLength live)
  | seqLeft {first second} : SchedulerOperand name first → SchedulerOperand name (.seq first second)
  | seqRight {first second} : SchedulerOperand name second → SchedulerOperand name (.seq first second)
  | ifTrue {op condition right first second} : SchedulerOperand name first →
      SchedulerOperand name (.ite op condition right first second)
  | ifFalse {op condition right first second} : SchedulerOperand name second →
      SchedulerOperand name (.ite op condition right first second)
  | loop {liveIn body liveOut} : SchedulerOperand name body → SchedulerOperand name (.loop liveIn body liveOut)
  | mustTerminate {body} : SchedulerOperand name body → SchedulerOperand name (.mustTerminate body)
  | returnBody {values cutsets body lab sec target arguments handler} : SchedulerOperand name body →
      SchedulerOperand name (.call (some (values, cutsets, body, lab, sec)) target arguments handler)
  | handlerBody {values cutsets body lab sec target arguments exception handler handlerLab handlerSec} :
      SchedulerOperand name handler → SchedulerOperand name
        (.call (some (values, cutsets, body, lab, sec)) target arguments
          (some (exception, handler, handlerLab, handlerSec)))

/-- Every actual scheduler source/result operand occurrence fits the whole
program maximum, including nested return and exception bodies. -/
theorem schedulerOperand_maximum {α : Type} {name : Nat} {program : WordProg α}
    (occurs : SchedulerOperand name program) : name ≤ wordProgCakeMaxVar program := by
  induction occurs with
  | move occurs member =>
      have bounds := compiledMove_operands_le_maximum occurs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> omega
  | returnValue member => exact returnSource_maximum _ _ _ member
  | callArgument member => exact callArgument_maximum _ _ _ _ _ member
  | callDestination member => exact callDestination_maximum _ _ _ _ _ _ _ _ _ member
  | ffi member => exact ffiSource_maximum _ _ _ _ _ _ _ member
  | @returnBody values cutsets body lab sec target arguments handler occurrence ih =>
      cases handler with
      | none => simp only [wordProgCakeMaxVar]; omega
      | some entry =>
          rcases entry with ⟨exception, handlerBody, handlerLab, handlerSec⟩
          simp only [wordProgCakeMaxVar]
          omega
  | ifTrue _ ih => cases ‹WordRegImm α› <;> simp_all only [wordProgCakeMaxVar] <;> omega
  | ifFalse _ ih => cases ‹WordRegImm α› <;> simp_all only [wordProgCakeMaxVar] <;> omega
  | mustTerminate _ ih => simpa only [wordProgCakeMaxVar] using ih
  | _ => simp_all only [wordProgCakeMaxVar]; omega

/-- Actual nested scheduler occurrences fit the retained allocation's own frame;
success supplies the producer equation, not an assumed frame equality. -/
theorem retainedConsumer_schedulerFrame {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (dead : WordProg α → WordProg α) (unreach : WordProg α → Option (WordProg α))
    (ssa : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label : Nat) (parameters : List Nat) (source : WordProg α)
    (output : CakeAllocationWithColour α)
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output)
    (name : Nat) (occurs : SchedulerOperand name output.colouredProgram) :
    name / 2 < cakeRiscVRegisterCount + output.allocation.nextSpill := by
  have maximum := schedulerOperand_maximum occurs
  have divided := Nat.div_le_div_right (c := 2) maximum
  rw [WordAlloc.allocatorWithSsa_spillState dead unreach ssa label parameters source output produced]
  rw [cakeColourWordSpillState_nextSpill_eq_occupancy]
  simp only [cakeColourFrameSlots]
  change name / 2 < cakeRiscVRegisterCount +
    max ((wordProgCakeMaxVar output.colouredProgram / 2 + 1) - cakeRiscVRegisterCount)
      (parameters.length - cakeRiscVRegisterCount)
  omega

/-- Actual colouring preserves each compiled Move occurrence and maps both
operands with the same executed colour function. -/
theorem compiledMove_applyColour {α : Type} (colour : Nat → Nat)
    {pair : Nat × Nat} {program : WordProg α} (occurs : CompiledMove pair program) :
    CompiledMove (colour pair.1, colour pair.2) (wordApplyColour colour program) := by
  induction occurs with
  | move priority moves member =>
      simp only [wordApplyColour]
      apply CompiledMove.move
      exact List.mem_map.mpr ⟨pair, member, rfl⟩
  | seqLeft _ ih => simpa only [wordApplyColour] using CompiledMove.seqLeft ih
  | seqRight _ ih => simpa only [wordApplyColour] using CompiledMove.seqRight ih
  | ifTrue _ ih => simpa only [wordApplyColour] using CompiledMove.ifTrue ih
  | ifFalse _ ih => simpa only [wordApplyColour] using CompiledMove.ifFalse ih
  | loop _ ih => simpa only [wordApplyColour] using CompiledMove.loop ih
  | mustTerminate _ ih => simpa only [wordApplyColour] using CompiledMove.mustTerminate ih
  | @returnBody values cutsets body lab sec target arguments handler occurrence ih =>
      cases handler with
      | none => simp only [wordApplyColour]; exact CompiledMove.returnBody ih
      | some entry =>
          rcases entry with ⟨exception, handlerBody, handlerLab, handlerSec⟩
          simp only [wordApplyColour]
          exact CompiledMove.returnBody ih
  | handlerBody _ ih => simp only [wordApplyColour]; exact CompiledMove.handlerBody ih

/-- Actual colouring carries every scheduler operand role into the emitted
program. This is structural producer correspondence, not a post-state or
frame-bound premise. -/
theorem schedulerOperand_applyColour {α : Type} (colour : Nat → Nat)
    {name : Nat} {program : WordProg α} (occurs : SchedulerOperand name program) :
    SchedulerOperand (colour name) (wordApplyColour colour program) := by
  induction occurs with
  | move occurs member =>
      apply SchedulerOperand.move (compiledMove_applyColour colour occurs)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl <;> simp
  | returnValue member =>
      simp only [wordApplyColour]
      apply SchedulerOperand.returnValue
      simpa only [List.map_cons] using (List.mem_map (f := colour)).mpr ⟨name, member, rfl⟩
  | @callArgument returns target arguments handler member =>
      rcases returns with _ | ⟨values, cutsets, body, lab, sec⟩
      all_goals rcases handler with _ | ⟨exception, handlerBody, handlerLab, handlerSec⟩
      all_goals simp only [wordApplyColour]
      all_goals apply SchedulerOperand.callArgument
      all_goals exact List.mem_map.mpr ⟨name, member, rfl⟩
  | @callDestination values cutsets body lab sec target arguments handler member =>
      rcases handler with _ | ⟨exception, handlerBody, handlerLab, handlerSec⟩
      all_goals simp only [wordApplyColour]
      all_goals apply SchedulerOperand.callDestination
      all_goals exact List.mem_map.mpr ⟨name, member, rfl⟩
  | ffi member =>
      simp only [wordApplyColour]
      apply SchedulerOperand.ffi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl | rfl | rfl <;> simp
  | seqLeft _ ih => simpa only [wordApplyColour] using SchedulerOperand.seqLeft ih
  | seqRight _ ih => simpa only [wordApplyColour] using SchedulerOperand.seqRight ih
  | ifTrue _ ih => simpa only [wordApplyColour] using SchedulerOperand.ifTrue ih
  | ifFalse _ ih => simpa only [wordApplyColour] using SchedulerOperand.ifFalse ih
  | loop _ ih => simpa only [wordApplyColour] using SchedulerOperand.loop ih
  | mustTerminate _ ih => simpa only [wordApplyColour] using SchedulerOperand.mustTerminate ih
  | @returnBody values cutsets body lab sec target arguments handler occurrence ih =>
      cases handler with
      | none => simp only [wordApplyColour]; exact SchedulerOperand.returnBody ih
      | some entry =>
          rcases entry with ⟨exception, handlerBody, handlerLab, handlerSec⟩
          simp only [wordApplyColour]
          exact SchedulerOperand.returnBody ih
  | handlerBody _ ih => simp only [wordApplyColour]; exact SchedulerOperand.handlerBody ih

/-- Actual input scheduler occurrences supply their emitted coloured frame
bounds. Unlike the intermediate carrier lemma, the caller does not supply an
occurrence or bound in a desired coloured output. -/
theorem retainedConsumer_inputSchedulerFrame {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (dead : WordProg α → WordProg α) (unreach : WordProg α → Option (WordProg α))
    (ssa : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label : Nat) (parameters : List Nat) (source : WordProg α)
    (output : CakeAllocationWithColour α)
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output)
    (name : Nat) (occurs : SchedulerOperand name output.program) :
    CakeAlloc.totalColour output.colouring name / 2 <
      cakeRiscVRegisterCount + output.allocation.nextSpill := by
  apply retainedConsumer_schedulerFrame dead unreach ssa label parameters source output produced
  exact schedulerOperand_applyColour (CakeAlloc.totalColour output.colouring) occurs

/-- Every compiled Move operand occurs in the actual read/write inventory
used to construct allocation locations, including nested return/handler code. -/
theorem compiledMove_variables {α : Type} {pair : Nat × Nat} {program : WordProg α}
    (occurs : CompiledMove pair program) :
    pair.1 ∈ wordProgVariables program ∧ pair.2 ∈ wordProgVariables program := by
  induction occurs with
  | move priority moves member =>
      simp only [wordProgVariables, wordProgReadVars, wordProgWriteVars, List.mem_append]
      exact ⟨Or.inr (List.mem_map.mpr ⟨pair, member, rfl⟩),
        Or.inl (List.mem_map.mpr ⟨pair, member, rfl⟩)⟩
  | @returnBody values cutsets body lab sec target arguments handler occurrence ih =>
      cases handler with
      | none => simp_all [wordProgVariables, wordProgReadVars, wordProgWriteVars]; tauto
      | some entry =>
          rcases entry with ⟨exception, handlerBody, handlerLab, handlerSec⟩
          simp_all [wordProgVariables, wordProgReadVars, wordProgWriteVars]; tauto
  | _ => simp_all [wordProgVariables, wordProgReadVars, wordProgWriteVars] <;> tauto

/-- Actual scheduler source/result roles are in the concrete read/write
inventory used by the location-map producer. No map membership is assumed. -/
theorem schedulerOperand_variables {α : Type} {name : Nat} {program : WordProg α}
    (occurs : SchedulerOperand name program) : name ∈ wordProgVariables program := by
  induction occurs with
  | move occurs member =>
      have vars := compiledMove_variables occurs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact vars.1
      · exact vars.2
  | @callArgument returns target arguments handler member =>
      rcases returns with _ | ⟨values, cutsets, body, lab, sec⟩
      all_goals rcases handler with _ | ⟨exception, handlerBody, handlerLab, handlerSec⟩
      all_goals simp_all [wordProgVariables, wordProgReadVars, wordProgWriteVars]
  | @callDestination values cutsets body lab sec target arguments handler member =>
      rcases handler with _ | ⟨exception, handlerBody, handlerLab, handlerSec⟩
      all_goals simp_all [wordProgVariables, wordProgReadVars, wordProgWriteVars]
  | @returnBody values cutsets body lab sec target arguments handler occurrence ih =>
      cases handler with
      | none => simp_all [wordProgVariables, wordProgReadVars, wordProgWriteVars]; tauto
      | some entry =>
          rcases entry with ⟨exception, handlerBody, handlerLab, handlerSec⟩
          simp_all [wordProgVariables, wordProgReadVars, wordProgWriteVars]; tauto
  | _ => simp_all [wordProgVariables, wordProgReadVars, wordProgWriteVars] <;> tauto

/-- Concrete location lookup for an actual scheduler operand from the retained
SSA caller. Both success and domain membership come from the real producers;
no desired location result or arbitrary map-domain guard is assumed. -/
theorem retainedConsumer_schedulerLocation {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (dead : WordProg α → WordProg α) (unreach : WordProg α → Option (WordProg α))
    (ssa : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label : Nat) (parameters : List Nat) (source : WordProg α)
    (output : CakeAllocationWithColour α)
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output)
    (name : Nat) (occurs : SchedulerOperand name output.program) :
    lookupNatInfo name output.allocation.locations =
      some (cakeColourLocation cakeRiscVRegisterCount
        (cakeColourFrameSlots cakeRiscVRegisterCount parameters output.program output.colouring).2
        (CakeAlloc.totalColour output.colouring name)) := by
  rw [WordAlloc.allocatorWithSsa_spillState dead unreach ssa label parameters source output produced]
  rw [cakeColourWordSpillState_lookup]
  have member : name ∈ parameters ++ wordProgVariables output.program :=
    List.mem_append_right _ (schedulerOperand_variables occurs)
  simp only [member, if_pos]

/-- The real caller's argument floor is already included by the actual shared
allocator. The post-allocation program parameter is ignored by its frame API,
so removing MustTerminate cannot alter this equation. -/
theorem retainedConsumer_callerFrame {width : Nat} [NeZero width]
    (dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source lowered : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output) :
    cakeWordFrameSlots output.allocation parameters lowered = output.allocation.nextSpill := by
  have constructed := WordAlloc.allocatorWithSsa_spillState dead unreach ssa label parameters source output produced
  have occupancy := cakeColourWordSpillState_nextSpill_eq_occupancy
    cakeRiscVRegisterCount parameters output.program output.colouring
  rw [← constructed] at occupancy
  simp only [cakeWordFrameSlots, occupancy, cakeColourFrameSlots, Nat.max_assoc, Nat.max_self]

/-- Full actual caller operand contract: the produced source configuration
looks up the native SOME format, and the scalar fits its actual frame domain.
Neither a desired map result nor a bound is assumed. This is infrastructure
for production replacement, not a HOL simulation theorem or full route proof. -/
theorem retainedConsumer_formatOperand {width : Nat} [NeZero width]
    (dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source lowered : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output)
    (name : Nat) (occurs : SchedulerOperand name output.program) :
    let slots := cakeWordFrameSlots output.allocation parameters lowered
    let frame := if slots = 0 then 0 else slots + 1
    let scalar := CakeAlloc.totalColour output.colouring name / 2
    wordStackLocation (sourceWordStackConfig label output.allocation slots) name =
      some (match Compiler.Backend.WordToStackRegFormat.formatVar cakeRiscVRegisterCount (some scalar) with
        | .inl register => .register register
        | .inr slot => .stack (frame - 1 - (slot - cakeRiscVRegisterCount))) ∧
    scalar < cakeRiscVRegisterCount + slots := by
  have caller := retainedConsumer_callerFrame dead unreach ssa label parameters source lowered output produced
  have constructed := WordAlloc.allocatorWithSsa_spillState dead unreach ssa label parameters source output produced
  have occupancy := cakeColourWordSpillState_nextSpill_eq_occupancy
    cakeRiscVRegisterCount parameters output.program output.colouring
  rw [← constructed] at occupancy
  have location := retainedConsumer_schedulerLocation dead unreach ssa label parameters source output produced name occurs
  have bound := retainedConsumer_inputSchedulerFrame dead unreach ssa label parameters source output produced name occurs
  dsimp only
  rw [caller]
  refine ⟨?_, bound⟩
  change lookupNatInfo name output.allocation.locations = _
  rw [location, cakeColourLocation_formatVar]
  simp only [occupancy, cakeColourFrameSlots]
  rfl

end Flapjack.ProductionMoveDomain
