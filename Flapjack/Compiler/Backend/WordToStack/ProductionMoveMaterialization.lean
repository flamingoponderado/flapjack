import Flapjack.Compiler.Backend.WordToStack.ProductionMoveDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionMoves
import Flapjack.Compiler.Backend.WordToStack.ProductionScheduler
import Flapjack.Compiler.Backend.Parmove.DestinationWrapper
import Flapjack.Compiler.Backend.Parmove.SourceMembershipWrapper
import Flapjack.Compiler.Backend.Parmove.PmovDsteps
import Flapjack.Compiler.Backend.Parmove.Invariants.Preservation
import Flapjack.Compiler.Backend.Parmove.DStepStep
import Flapjack.Compiler.Backend.Parmove.MapInj
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Move

/-! Concrete formatting/materialization infrastructure, not a HOL theorem
port. Actual caller domain discharge is provided by ProductionMoveDomain;
complete scheduling, filtering and literal sequencing are derived below.
Whole executed compiler-route adoption remains a separate obligation. -/
namespace Flapjack.ProductionMoveMaterialization
open RiscV RiscV.CakeRegAlloc ProductionMoves
open Compiler.Backend.WordToStackRegFormat
open Compiler.Backend Compiler.Backend.StackLang Compiler.Encoders.Asm

/-- The actual formatted SOME location is exactly the allocator colour image. -/
theorem formattedSome (k frame slots index : Nat) :
    formattedLocation (k, frame, slots) (formatVar k (some index)) =
      cakeColourLocation k frame (2 * index) := by
  by_cases below : index < k <;>
    simp [formattedLocation, formatVar, cakeColourLocation, below]

/-- Full optional formatting is injective on the native caller scalar domain.
NONE's scheduler temporary (k+1) is kept distinct from every ordinary register
and spill; no equality/injectivity of the desired output is assumed. -/
theorem formattedOption_injective (k slots : Nat) (left right : Option Nat)
    (leftBound : ∀ i, left = some i → i < k + slots)
    (rightBound : ∀ i, right = some i → i < k + slots)
    (equal : formattedLocation (k, (if slots = 0 then 0 else slots + 1), slots) (formatVar k left) =
      formattedLocation (k, (if slots = 0 then 0 else slots + 1), slots) (formatVar k right)) :
    left = right := by
  have frame : slots ≤ (if slots = 0 then 0 else slots + 1) := by split <;> omega
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some r =>
          by_cases below : r < k
          · simp [formatVar, formattedLocation, below] at equal
            omega
          · simp [formatVar, formattedLocation, below] at equal
  | some l =>
      cases right with
      | none =>
          by_cases below : l < k
          · simp [formatVar, formattedLocation, below] at equal
            omega
          · simp [formatVar, formattedLocation, below] at equal
      | some r =>
          rw [formattedSome, formattedSome] at equal
          have leftFits := leftBound l rfl
          have rightFits := rightBound r rfl
          have same := cakeColourLocation_even_injective k
            (if slots = 0 then 0 else slots + 1) l r (by omega) (by omega) equal
          exact congrArg some same

/-- The actual source caller's full record supplies precisely the two fields
used by materialization: original k scratch and zero stack base. -/
theorem locationMove_sourceConfig {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState) (destination source : WordLocation) :
    locationMove (width := width) (sourceWordStackConfig label allocation slots) destination source =
      locationMove (nativeMoveConfig (cakeRiscVRegisterCount,
        (if slots = 0 then 0 else slots + 1), slots)) destination source := by
  cases destination <;> cases source <;>
    simp only [locationMove, sourceWordStackConfig, nativeMoveConfig, wordStackOffset]

/-- Full nonidentity optional single-move materialization for the real source
configuration. Scalar nonidentity is supplied by scheduling; scalar bounds
are discharged by the actual caller contracts, and location nonidentity is
proved here rather than assumed. Native literal code is the conclusion. -/
theorem optionMove_sourceConfig_native {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState) (destination source : Option Nat)
    (destinationBound : ∀ i, destination = some i → i < cakeRiscVRegisterCount + slots)
    (sourceBound : ∀ i, source = some i → i < cakeRiscVRegisterCount + slots)
    (different : destination ≠ source) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    locationMove (width := width) (sourceWordStackConfig label allocation slots)
      (formattedLocation kf (formatVar cakeRiscVRegisterCount destination))
      (formattedLocation kf (formatVar cakeRiscVRegisterCount source)) =
    Compiler.Backend.WordToStack.Native.wMoveSingleNative
      (formatVar cakeRiscVRegisterCount destination, formatVar cakeRiscVRegisterCount source) kf := by
  dsimp only
  rw [locationMove_sourceConfig]
  apply locationMove_native
  intro equal
  exact different (formattedOption_injective cakeRiscVRegisterCount slots
    destination source destinationBound sourceBound equal)

/-- Actual temporary save materializes native NONE/SOME for every scalar.
Formatting itself excludes the two reserved registers; no successful scratch
operation or caller safety predicate is assumed. -/
theorem toScratch_sourceNative {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState) (index : Nat) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    toScratch (width := width) (sourceWordStackConfig label allocation slots)
      (formattedLocation kf (formatVar cakeRiscVRegisterCount (some index))) =
      some (Compiler.Backend.WordToStack.Native.wMoveSingleNative
        (formatVar cakeRiscVRegisterCount none, formatVar cakeRiscVRegisterCount (some index)) kf) := by
  dsimp only
  by_cases below : index < cakeRiscVRegisterCount
  · simp only [cakeRiscVRegisterCount] at below
    have notScratch : index ≠ 22 := by omega
    have notTemporary : index ≠ 23 := by omega
    simp [formatVar, formattedLocation, toScratch, sourceWordStackConfig,
      Compiler.Backend.WordToStack.Native.wMoveSingleNative, below,
      cakeRiscVRegisterCount, notScratch, notTemporary]
  · simp only [cakeRiscVRegisterCount] at below
    simp [formatVar, formattedLocation, toScratch, sourceWordStackConfig,
      Compiler.Backend.WordToStack.Native.wMoveSingleNative, below, wordStackOffset,
      cakeRiscVRegisterCount]

/-- Actual temporary restore materializes native SOME/NONE for every scalar,
including spilled values and zero frames, with no assumed decoder success. -/
theorem fromScratch_sourceNative {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState) (index : Nat) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    fromScratch (width := width) (sourceWordStackConfig label allocation slots)
      (formattedLocation kf (formatVar cakeRiscVRegisterCount (some index))) =
      some (Compiler.Backend.WordToStack.Native.wMoveSingleNative
        (formatVar cakeRiscVRegisterCount (some index), formatVar cakeRiscVRegisterCount none) kf) := by
  dsimp only
  by_cases below : index < cakeRiscVRegisterCount
  · simp only [cakeRiscVRegisterCount] at below
    have notScratch : index ≠ 22 := by omega
    have notTemporary : index ≠ 23 := by omega
    simp [formatVar, formattedLocation, fromScratch, sourceWordStackConfig,
      Compiler.Backend.WordToStack.Native.wMoveSingleNative, below,
      cakeRiscVRegisterCount, notScratch, notTemporary]
  · simp only [cakeRiscVRegisterCount] at below
    simp [formatVar, formattedLocation, fromScratch, sourceWordStackConfig,
      Compiler.Backend.WordToStack.Native.wMoveSingleNative, below, wordStackOffset,
      cakeRiscVRegisterCount]

/-- Literal native single moves always emit an instruction, even for equal
locations. This structural fact justifies normalized production sequencing. -/
theorem nativeSingle_ne_skip {width : Nat} [NeZero width]
    (xy : Sum Nat Nat × Sum Nat Nat) (kf : Nat × Nat × Nat) :
    Compiler.Backend.WordToStack.Native.wMoveSingleNative (width := width) xy kf ≠ .skip := by
  rcases xy with ⟨destination, source⟩
  cases destination <;> cases source <;>
    simp [Compiler.Backend.WordToStack.Native.wMoveSingleNative]

/-- Native literal list lowering is skip precisely for the empty list. -/
theorem nativeAux_eq_skip_iff {width : Nat} [NeZero width]
    (moves : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    Compiler.Backend.WordToStack.Native.wMoveAuxNative (width := width) moves kf = .skip ↔
      moves = [] := by
  cases moves with
  | nil => simp [Compiler.Backend.WordToStack.Native.wMoveAuxNative]
  | cons move rest =>
      cases rest with
      | nil => simp [Compiler.Backend.WordToStack.Native.wMoveAuxNative, nativeSingle_ne_skip]
      | cons next rest => simp [Compiler.Backend.WordToStack.Native.wMoveAuxNative]

/-- Production's skip normalization agrees with literal native empty,
singleton and longer sequencing whenever the head is a native single move. -/
theorem join_nativeAux_cons {width : Nat} [NeZero width]
    (move : Sum Nat Nat × Sum Nat Nat)
    (rest : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    join (Compiler.Backend.WordToStack.Native.wMoveSingleNative (width := width) move kf)
      (Compiler.Backend.WordToStack.Native.wMoveAuxNative rest kf) =
    Compiler.Backend.WordToStack.Native.wMoveAuxNative (move :: rest) kf := by
  cases rest with
  | nil =>
      rcases move with ⟨destination, source⟩
      cases destination <;> cases source <;>
        simp [Compiler.Backend.WordToStack.Native.wMoveAuxNative,
          Compiler.Backend.WordToStack.Native.wMoveSingleNative, join]
  | cons next rest =>
      have head := nativeSingle_ne_skip (width := width) move kf
      have tail : Compiler.Backend.WordToStack.Native.wMoveAuxNative
          (width := width) (next :: rest) kf ≠ .skip := by
        simp [nativeAux_eq_skip_iff]
      unfold join
      split <;> simp_all [Compiler.Backend.WordToStack.Native.wMoveAuxNative]

/-- Complete optional-list correspondence on the caller's scalar domain.
The conditions concern scheduler operands and scalar identity only; the real
caller supplies bounds and the scheduler supplies nonidentity separately. -/
theorem optionMoveList_sourceNative {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState)
    (moves : List (Option Nat × Option Nat))
    (valid : ∀ move ∈ moves,
      (∀ i, move.1 = some i → i < cakeRiscVRegisterCount + slots) ∧
      (∀ i, move.2 = some i → i < cakeRiscVRegisterCount + slots) ∧ move.1 ≠ move.2) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    optionMoveList (width := width) (sourceWordStackConfig label allocation slots)
      (moves.map (fun move =>
        (move.1.map (fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i))),
         move.2.map (fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i)))))) =
      some (Compiler.Backend.WordToStack.Native.wMoveAuxNative
        (moves.map (fun move =>
          (formatVar cakeRiscVRegisterCount move.1, formatVar cakeRiscVRegisterCount move.2))) kf) := by
  dsimp only
  induction moves with
  | nil => simp [optionMoveList, Compiler.Backend.WordToStack.Native.wMoveAuxNative]
  | cons move rest ih =>
      have head := valid move (by simp)
      have tail := ih (fun next member => valid next (by simp [member]))
      rcases move with ⟨destination, source⟩
      cases destination with
      | none =>
          cases source with
          | none => exact False.elim (head.2.2 rfl)
          | some source =>
              simp only [List.map_cons, Option.map_none, Option.map_some,
                optionMoveList, toScratch_sourceNative, tail]
              simp only [bind, pure, Option.bind_some, join_nativeAux_cons]
      | some destination =>
          cases source with
          | none =>
              simp only [List.map_cons, Option.map_none, Option.map_some,
                optionMoveList, fromScratch_sourceNative, tail]
              simp only [bind, pure, Option.bind_some, join_nativeAux_cons]
          | some source =>
              have single := optionMove_sourceConfig_native (width := width)
                label slots allocation (some destination) (some source) head.1 head.2.1 head.2.2
              simp only [List.map_cons, Option.map_some, optionMoveList, tail, single]
              simp only [bind, pure, Option.bind_some, join_nativeAux_cons]

/-- Real scalar bounds are preserved by the actual native scheduler for
arbitrary input moves, including duplicates and cycles. Temporary NONE needs
no numeric bound; each SOME is traced back to an actual input operand. -/
theorem parmove_operandBounds (moves : List (Nat × Nat)) (bound : Nat)
    (input : ∀ move ∈ moves, move.1 < bound ∧ move.2 < bound)
    (move : Option Nat × Option Nat)
    (member : move ∈ Compiler.Backend.Parmove.parmove moves) :
    (∀ i, move.1 = some i → i < bound) ∧
    (∀ i, move.2 = some i → i < bound) := by
  constructor
  · intro i equal
    have output : some i ∈ (Compiler.Backend.Parmove.parmove moves).map Prod.fst := by
      exact List.mem_map.mpr ⟨move, member, equal⟩
    have original := Compiler.Backend.Parmove.memMapFstParmove moves i output
    obtain ⟨pair, present, value⟩ := List.mem_map.mp original
    simpa only [value] using (input pair present).1
  · intro i equal
    have output : some i ∈ (Compiler.Backend.Parmove.parmove moves).map Prod.snd := by
      exact List.mem_map.mpr ⟨move, member, equal⟩
    have original := Compiler.Backend.Parmove.memMapSndParmove moves i output
    obtain ⟨pair, present, value⟩ := List.mem_map.mp original
    simpa only [value] using (input pair present).2

/-- Regression evidence for why caller destination conventions must be
retained: arbitrary duplicated destinations can cause the literal scheduler
to emit an identity. This is infrastructure, not a narrowed HOL port. -/
theorem duplicateDestination_identity :
    Compiler.Backend.Parmove.parmove [(1, 2), (1, 1)] =
      [(some 1, some 1), (some 1, some 2)] := by
  simp [Compiler.Backend.Parmove.parmove, Compiler.Backend.Parmove.pmov.eq_def,
    Compiler.Backend.Parmove.fstep, Compiler.Backend.Parmove.splitSource,
    Compiler.Backend.Parmove.frontLast]

/-- Deterministic scheduling preserves nonidentity in active and emitted
moves under the original destination and optional-register invariants. -/
private theorem dstep_nonidentity {α : Type}
    (first second : Compiler.Backend.Parmove.State α)
    (step : Compiler.Backend.Parmove.DStep first second)
    (valid : Compiler.Backend.Parmove.wf first)
    (active : ∀ move ∈ first.2.1, move.1 ≠ move.2)
    (emitted : ∀ move ∈ first.2.2, move.1 ≠ move.2) :
    (∀ move ∈ second.2.1, move.1 ≠ move.2) ∧
    (∀ move ∈ second.2.2, move.1 ≠ move.2) := by
  cases step <;>
    simp_all [Compiler.Backend.Parmove.wf, Compiler.Backend.Parmove.windmill,
      List.map_append, List.nodup_append, List.mem_append, List.mem_cons] <;> grind

/-- Nonidentity is derived from the actual scheduler run and the original
windmill input convention, rather than imposed on its output. -/
theorem parmove_nonidentity {α : Type} [DecidableEq α]
    (moves : List (α × α)) (distinct : Compiler.Backend.Parmove.windmill moves)
    (move : Option α × Option α) (member : move ∈ Compiler.Backend.Parmove.parmove moves) :
    move.1 ≠ move.2 := by
  let initial : Compiler.Backend.Parmove.State α :=
    (moves.map (fun move => (some move.1, some move.2)), [], [])
  have initialValid : Compiler.Backend.Parmove.wf initial := by
    apply Compiler.Backend.Parmove.wf_init
    refine ⟨?_, ?_, ?_⟩
    · simpa [Compiler.Backend.Parmove.windmill, List.map_map, Function.comp_def] using
        (List.Nodup.map (f := some) (by intro a b equal; exact Option.some.inj equal) distinct)
    · intro move member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      rfl
    · intro move member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      rfl
  have run := Compiler.Backend.Parmove.pmovDsteps initial
  have invariant : ∀ last, Compiler.Backend.Parmove.DSteps initial last →
      Compiler.Backend.Parmove.wf last ∧
      (∀ move ∈ last.2.1, move.1 ≠ move.2) ∧
      (∀ move ∈ last.2.2, move.1 ≠ move.2) := by
    intro last steps
    induction steps with
    | refl => exact ⟨initialValid, by simp [initial], by simp [initial]⟩
    | @tail middle last run step ih =>
        have preserved := dstep_nonidentity middle last step ih.1 ih.2.1 ih.2.2
        exact ⟨Compiler.Backend.Parmove.wf_steps middle last
          ⟨ih.1, Compiler.Backend.Parmove.dstep_step middle last step ih.1⟩, preserved⟩
  apply (invariant _ run).2.2 move
  simpa [Compiler.Backend.Parmove.parmove, initial] using member

/-- Whole scheduled-list materialization derives every output-domain and
nonidentity condition from the actual input bounds and original windmill
convention. It assumes neither scheduler output nor target evaluation. -/
theorem scheduledList_sourceNative {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState) (moves : List (Nat × Nat))
    (distinct : Compiler.Backend.Parmove.windmill moves)
    (input : ∀ move ∈ moves,
      move.1 < cakeRiscVRegisterCount + slots ∧ move.2 < cakeRiscVRegisterCount + slots) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    optionMoveList (width := width) (sourceWordStackConfig label allocation slots)
      ((Compiler.Backend.Parmove.parmove moves).map (fun move =>
        (move.1.map (fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i))),
         move.2.map (fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i)))))) =
      some (Compiler.Backend.WordToStack.Native.wMoveAuxNative
        ((Compiler.Backend.Parmove.parmove moves).map (fun move =>
          (formatVar cakeRiscVRegisterCount move.1, formatVar cakeRiscVRegisterCount move.2))) kf) := by
  apply optionMoveList_sourceNative
  intro move member
  have bounds := parmove_operandBounds moves (cakeRiscVRegisterCount + slots) input move member
  exact ⟨bounds.1, bounds.2, parmove_nonidentity moves distinct move member⟩

/-- Actual scalar-to-location scheduling commutes with native parmove.
Injectivity on the input endpoint set is derived from the real frame bounds;
no map-injection hypothesis or scheduled output is assumed. -/
theorem parmove_formattedLocations (slots : Nat) (moves : List (Nat × Nat))
    (distinct : Compiler.Backend.Parmove.windmill moves)
    (input : ∀ move ∈ moves,
      move.1 < cakeRiscVRegisterCount + slots ∧ move.2 < cakeRiscVRegisterCount + slots) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    let location := fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i))
    Compiler.Backend.Parmove.parmove (moves.map (Prod.map location location)) =
      (Compiler.Backend.Parmove.parmove moves).map
        (Prod.map (Option.map location) (Option.map location)) := by
  dsimp only
  apply Compiler.Backend.Parmove.parmove_MAP_INJ
  refine ⟨?_, distinct⟩
  have bound : ∀ i, i ∈ moves.map Prod.fst ++ moves.map Prod.snd →
      i < cakeRiscVRegisterCount + slots := by
    intro i member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨pair, present, equal⟩ := List.mem_map.mp member
      simpa only [equal] using (input pair present).1
    · obtain ⟨pair, present, equal⟩ := List.mem_map.mp member
      simpa only [equal] using (input pair present).2
  dsimp only
  intro x y facts
  exact Option.some.inj (formattedOption_injective cakeRiscVRegisterCount slots
    (some x) (some y)
    (by intro i equal; cases Option.some.inj equal; exact bound x facts.1)
    (by intro i equal; cases Option.some.inj equal; exact bound y facts.2.1)
    facts.2.2)

/-- Actual fuel scheduling and complete optional materialization produce the
literal native scheduled list. Bounds and original destination convention are
input facts; scheduler success and desired code are both conclusions. Initial
production filtering and dispatch remain separate caller obligations. -/
theorem optionOrder_materialize_sourceNative {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState) (moves : List (Nat × Nat))
    (distinct : Compiler.Backend.Parmove.windmill moves)
    (input : ∀ move ∈ moves,
      move.1 < cakeRiscVRegisterCount + slots ∧ move.2 < cakeRiscVRegisterCount + slots) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    let location := fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i))
    (wordStackCakeParallelOptionOrder (moves.map (Prod.map location location))).bind
      (optionMoveList (width := width) (sourceWordStackConfig label allocation slots)) =
      some (Compiler.Backend.WordToStack.Native.wMoveAuxNative
        ((Compiler.Backend.Parmove.parmove moves).map (fun move =>
          (formatVar cakeRiscVRegisterCount move.1, formatVar cakeRiscVRegisterCount move.2))) kf) := by
  dsimp only
  rw [ProductionScheduler.optionOrder_eq_parmove, parmove_formattedLocations slots moves distinct input]
  simp only [Option.bind_some]
  exact scheduledList_sourceNative label slots allocation moves distinct input

/-- The actual retained allocation result discharges scheduled materializer
frame bounds. The remaining windmill guard is the original Move convention;
no caller numeric bounds, successful schedule, or target code are assumed. -/
theorem retainedConsumer_moveMaterialization {width : Nat} [NeZero width]
    (dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source lowered : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output)
    (moves : List (Nat × Nat))
    (occurs : ∀ move ∈ moves, ProductionMoveDomain.CompiledMove move output.colouredProgram)
    (distinct : Compiler.Backend.Parmove.windmill
      (moves.map (fun move => (move.1 / 2, move.2 / 2)))) :
    let slots := cakeWordFrameSlots output.allocation parameters lowered
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    let scalars := moves.map (fun move => (move.1 / 2, move.2 / 2))
    let location := fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i))
    (wordStackCakeParallelOptionOrder (scalars.map (Prod.map location location))).bind
      (optionMoveList (width := width) (sourceWordStackConfig label output.allocation slots)) =
      some (Compiler.Backend.WordToStack.Native.wMoveAuxNative
        ((Compiler.Backend.Parmove.parmove scalars).map (fun move =>
          (formatVar cakeRiscVRegisterCount move.1, formatVar cakeRiscVRegisterCount move.2))) kf) := by
  dsimp only
  rw [ProductionMoveDomain.retainedConsumer_callerFrame
    dead unreach ssa label parameters source lowered output produced]
  apply optionOrder_materialize_sourceNative label output.allocation.nextSpill output.allocation _ distinct
  intro scalar member
  obtain ⟨move, present, equal⟩ := List.mem_map.mp member
  subst scalar
  exact ProductionMoveDomain.retainedConsumer_moveFrame
    dead unreach ssa label parameters source output produced move (occurs move present)

/-- Actual source Move execution discharges the scheduler destination guard.
The only numeric convention retained is HOL's even physical destinations;
source nonerror derives distinctness, rather than assuming scheduler windmill. -/
theorem sourceMove_windmill {width : Nat} [NeZero width] {C F : Type}
    (priority : Nat) (moves : List (Nat × Nat))
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.move priority moves) source = (result, post))
    (notError : result ≠ some .error)
    (even : ∀ n ∈ moves.map Prod.fst, n % 2 = 0) :
    Compiler.Backend.Parmove.windmill (moves.map (fun move => (move.1 / 2, move.2 / 2))) := by
  obtain ⟨_, distinct, _⟩ := WordToStackProofs.CompCorrect.Move.sourceSuccess
    priority moves source post result execution notError
  exact WordToStackProofs.CompCorrect.Move.halvedWindmill moves distinct even

/-- Initial identity filtering of actual formatted locations is precisely
scalar identity filtering on the producer's frame domain. No location-equality
assumption or blanket numeric injection is required. -/
theorem filter_formattedLocations (slots : Nat) (moves : List (Nat × Nat))
    (input : ∀ move ∈ moves,
      move.1 < cakeRiscVRegisterCount + slots ∧ move.2 < cakeRiscVRegisterCount + slots) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    let location := fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i))
    (moves.map (Prod.map location location)).filter (fun move => move.1 != move.2) =
      (moves.filter (fun move => move.1 != move.2)).map (Prod.map location location) := by
  dsimp only
  induction moves with
  | nil => rfl
  | cons move rest ih =>
      have bounds := input move (by simp)
      have tail := ih (fun next member => input next (by simp [member]))
      have inject :
          formattedLocation (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
              (formatVar cakeRiscVRegisterCount (some move.1)) =
          formattedLocation (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
              (formatVar cakeRiscVRegisterCount (some move.2)) ↔ move.1 = move.2 := by
        constructor
        · intro equal
          exact Option.some.inj (formattedOption_injective cakeRiscVRegisterCount slots
            (some move.1) (some move.2)
            (by intro i equal; cases Option.some.inj equal; exact bounds.1)
            (by intro i equal; cases Option.some.inj equal; exact bounds.2) equal)
        · intro equal; rw [equal]
      by_cases equal : move.1 = move.2 <;>
        simp [bne, inject, equal] <;> exact tail

/-- Original destination uniqueness excludes pending identities from every
active destination search. This is the key fact for literal self-removal,
stronger than semantic equivalence of identity assignments. -/
private theorem pendingIdentity_not_activeDestination {α : Type}
    (pending active : List (Compiler.Backend.Parmove.Move α))
    (unique : Compiler.Backend.Parmove.windmill (pending ++ active))
    (move : Compiler.Backend.Parmove.Move α) (member : move ∈ pending)
    (identity : move.1 = move.2) (destination : Option α)
    (activeMember : destination ∈ active.map Prod.fst) : move.2 ≠ destination := by
  have pendingMember : move.1 ∈ pending.map Prod.fst := List.mem_map.mpr ⟨move, member, rfl⟩
  simp only [Compiler.Backend.Parmove.windmill, List.map_append, List.nodup_append] at unique
  grind

/-- Removing identities that cannot match the searched destination preserves
both halves of native first-source splitting, with their original order. -/
private theorem splitSource_filterIdentity {α : Type} [DecidableEq α]
    (destination : Option α) (moves : List (Compiler.Backend.Parmove.Move α))
    (excluded : ∀ move ∈ moves, move.1 = move.2 → move.2 ≠ destination) :
    Compiler.Backend.Parmove.splitSource destination
        (moves.filter (fun move => decide (move.1 ≠ move.2))) =
      ((Compiler.Backend.Parmove.splitSource destination moves).1.filter
          (fun move => decide (move.1 ≠ move.2)),
       (Compiler.Backend.Parmove.splitSource destination moves).2.filter
          (fun move => decide (move.1 ≠ move.2))) := by
  induction moves with
  | nil => rfl
  | cons move rest ih =>
      have tail := ih (fun next member => excluded next (by simp [member]))
      simp only [decide_not] at tail
      by_cases matched : move.2 = destination
      · have different : move.1 ≠ move.2 := by
          intro identity
          exact excluded move (by simp) identity matched
        have notDestination : move.1 ≠ destination := by simpa only [matched] using different
        simp [Compiler.Backend.Parmove.splitSource, matched, notDestination]
      · by_cases identity : move.1 = move.2
        · simp [Compiler.Backend.Parmove.splitSource, matched, identity, tail]
        · simp [Compiler.Backend.Parmove.splitSource, matched, identity, tail]

/-- Remove pending identities only; active and emitted order are untouched. -/
private def erasePendingIdentities {α : Type} [DecidableEq α]
    (state : Compiler.Backend.Parmove.State α) : Compiler.Backend.Parmove.State α :=
  (state.1.filter (fun move => decide (move.1 ≠ move.2)), state.2)

/-- For an active chain, actual deterministic scheduling commutes with
pending-identity removal under the original destination convention. -/
private theorem fstep_erasePending_active {α : Type} [DecidableEq α]
    (pending active emitted : List (Compiler.Backend.Parmove.Move α))
    (destination source : Option α)
    (unique : Compiler.Backend.Parmove.windmill (pending ++ (destination, source) :: active)) :
    Compiler.Backend.Parmove.fstep
      (erasePendingIdentities (pending, (destination, source) :: active, emitted)) =
    erasePendingIdentities (Compiler.Backend.Parmove.fstep
      (pending, (destination, source) :: active, emitted)) := by
  have excluded : ∀ move ∈ pending, move.1 = move.2 → move.2 ≠ destination := by
    intro move member identity
    exact pendingIdentity_not_activeDestination pending ((destination, source) :: active)
      unique move member identity destination (by simp)
  have split := splitSource_filterIdentity destination pending excluded
  cases suffix : (Compiler.Backend.Parmove.splitSource destination pending).2 with
  | nil =>
      simp only [erasePendingIdentities, Compiler.Backend.Parmove.fstep, split, suffix, List.filter_nil]
      cases active with
      | nil => rfl
      | cons head tail =>
          simp only
          split <;> rfl
  | cons next rest =>
      have member : next ∈ pending := by
        rw [← Compiler.Backend.Parmove.splitSource_append destination pending]
        simp [suffix]
      have matched := Compiler.Backend.Parmove.splitSource_suffix_match destination pending next rest suffix
      have different : next.1 ≠ next.2 := by
        intro identity
        exact excluded next member identity matched
      have keep : decide (next.1 ≠ next.2) = true := by simp [different]
      simp only [erasePendingIdentities, Compiler.Backend.Parmove.fstep, split, suffix,
        List.filter_cons, keep, ↓reduceIte, List.filter_append]

/-- Erasure either stutters when native scheduling discards a pending head
identity, or commutes with the actual scheduler step. -/
private theorem fstep_erasePending {α : Type} [DecidableEq α]
    (state : Compiler.Backend.Parmove.State α)
    (unique : Compiler.Backend.Parmove.windmill (state.1 ++ state.2.1)) :
    erasePendingIdentities state = erasePendingIdentities (Compiler.Backend.Parmove.fstep state) ∨
    Compiler.Backend.Parmove.fstep (erasePendingIdentities state) =
      erasePendingIdentities (Compiler.Backend.Parmove.fstep state) := by
  rcases state with ⟨pending, active, emitted⟩
  cases active with
  | cons move active =>
      rcases move with ⟨destination, source⟩
      exact Or.inr (fstep_erasePending_active pending active emitted destination source unique)
  | nil =>
      cases pending with
      | nil => exact Or.inl rfl
      | cons move pending =>
          rcases move with ⟨destination, source⟩
          by_cases identity : destination = source
          · left
            simp [erasePendingIdentities, Compiler.Backend.Parmove.fstep, identity]
          · right
            have reverse : source ≠ destination := Ne.symm identity
            simp [erasePendingIdentities, Compiler.Backend.Parmove.fstep, identity, reverse]

/-- Native scheduling absorbs its actual deterministic step, including the
terminal fixed point. This follows directly from the defining recursion. -/
private theorem pmov_fstep {α : Type} [DecidableEq α]
    (state : Compiler.Backend.Parmove.State α) :
    Compiler.Backend.Parmove.pmov state =
      Compiler.Backend.Parmove.pmov (Compiler.Backend.Parmove.fstep state) := by
  by_cases finished : state.1 = [] ∧ state.2.1 = []
  · rcases state with ⟨pending, active, emitted⟩
    obtain ⟨rfl, rfl⟩ := finished
    rfl
  · rw [Compiler.Backend.Parmove.pmov.eq_def state, dif_neg finished]

/-- Literal emitted scheduler output is invariant under initial pending
identity removal. Original wf guards ensure removed identities cannot be
selected into an active chain; no desired output equality is assumed. -/
private theorem pmov_erasePending {α : Type} [DecidableEq α]
    (state : Compiler.Backend.Parmove.State α)
    (valid : Compiler.Backend.Parmove.wf state) :
    (Compiler.Backend.Parmove.pmov (erasePendingIdentities state)).2.2 =
      (Compiler.Backend.Parmove.pmov state).2.2 := by
  induction state using Compiler.Backend.Parmove.pmov.induct with
  | case1 state finished =>
      rcases state with ⟨pending, active, emitted⟩
      obtain ⟨rfl, rfl⟩ := finished
      rfl
  | case2 state unfinished ih =>
      have step := Compiler.Backend.Parmove.fstepDstep state (by
        intro emitted equal
        exact unfinished (equal ▸ ⟨rfl, rfl⟩))
      have nextValid := Compiler.Backend.Parmove.wf_steps state
        (Compiler.Backend.Parmove.fstep state)
        ⟨valid, Compiler.Backend.Parmove.dstep_step _ _ step valid⟩
      have next := ih nextValid
      have sourceStep := congrArg (fun state => state.2.2) (pmov_fstep state)
      rw [sourceStep]
      rcases fstep_erasePending state valid.1 with stutter | commutes
      · rw [stutter]
        exact next
      · rw [pmov_fstep (erasePendingIdentities state), commutes]
        exact next

/-- Public native scheduling discards initial scalar identities without
changing its literal ordered output under the original windmill convention. -/
theorem parmove_filterIdentity {α : Type} [DecidableEq α]
    (moves : List (α × α)) (distinct : Compiler.Backend.Parmove.windmill moves) :
    Compiler.Backend.Parmove.parmove (moves.filter (fun move => decide (move.1 ≠ move.2))) =
      Compiler.Backend.Parmove.parmove moves := by
  let initial : Compiler.Backend.Parmove.State α :=
    (moves.map (fun move => (some move.1, some move.2)), [], [])
  have valid : Compiler.Backend.Parmove.wf initial := by
    apply Compiler.Backend.Parmove.wf_init
    refine ⟨?_, ?_, ?_⟩
    · simpa [Compiler.Backend.Parmove.windmill, List.map_map, Function.comp_def] using
        (List.Nodup.map (f := some) (by intro a b equal; exact Option.some.inj equal) distinct)
    · intro move member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      rfl
    · intro move member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      rfl
  have lifted :
      (moves.filter (fun move => decide (move.1 ≠ move.2))).map
          (fun move => (some move.1, some move.2)) =
      (moves.map (fun move => (some move.1, some move.2))).filter
          (fun move => decide (move.1 ≠ move.2)) := by
    clear distinct valid initial
    induction moves with
    | nil => rfl
    | cons move rest ih =>
        simp only [decide_not] at ih
        by_cases identity : move.1 = move.2 <;> simp [identity, ih]
  have result := congrArg List.reverse (pmov_erasePending initial valid)
  simpa only [Compiler.Backend.Parmove.parmove, erasePendingIdentities, initial, ← lifted] using result

/-- Initial scalar filtering followed by actual location scheduling and
materialization yields the original unfiltered native scheduled code. -/
theorem filteredOptionOrder_sourceNative {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState) (moves : List (Nat × Nat))
    (distinct : Compiler.Backend.Parmove.windmill moves)
    (input : ∀ move ∈ moves,
      move.1 < cakeRiscVRegisterCount + slots ∧ move.2 < cakeRiscVRegisterCount + slots) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    let location := fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i))
    (wordStackCakeParallelOptionOrder
      ((moves.filter (fun move => decide (move.1 ≠ move.2))).map (Prod.map location location))).bind
      (optionMoveList (width := width) (sourceWordStackConfig label allocation slots)) =
      some (Compiler.Backend.WordToStack.Native.wMoveAuxNative
        ((Compiler.Backend.Parmove.parmove moves).map (fun move =>
          (formatVar cakeRiscVRegisterCount move.1, formatVar cakeRiscVRegisterCount move.2))) kf) := by
  have filteredDistinct : Compiler.Backend.Parmove.windmill
      (moves.filter (fun move => decide (move.1 ≠ move.2))) := by
    exact (List.filter_sublist.map Prod.fst).nodup distinct
  have result := optionOrder_materialize_sourceNative (width := width) label slots allocation
    (moves.filter (fun move => decide (move.1 ≠ move.2))) filteredDistinct
    (fun move member => input move (List.mem_filter.mp member).1)
  simpa only [parmove_filterIdentity moves distinct] using result

/-- Production's concrete Boolean location filter, real fuel scheduler and
optional materializer produce literal native code under original input guards.
The optimized acyclic dispatch branch remains a separate obligation. -/
theorem locationFilteredOptionOrder_sourceNative {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState) (moves : List (Nat × Nat))
    (distinct : Compiler.Backend.Parmove.windmill moves)
    (input : ∀ move ∈ moves,
      move.1 < cakeRiscVRegisterCount + slots ∧ move.2 < cakeRiscVRegisterCount + slots) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    let location := fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i))
    (wordStackCakeParallelOptionOrder
      ((moves.map (Prod.map location location)).filter (fun move => move.1 != move.2))).bind
      (optionMoveList (width := width) (sourceWordStackConfig label allocation slots)) =
      some (Compiler.Backend.WordToStack.Native.wMoveAuxNative
        ((Compiler.Backend.Parmove.parmove moves).map (fun move =>
          (formatVar cakeRiscVRegisterCount move.1, formatVar cakeRiscVRegisterCount move.2))) kf) := by
  dsimp only
  rw [filter_formattedLocations slots moves input]
  have scalarFilter : moves.filter (fun move => move.1 != move.2) =
      moves.filter (fun move => decide (move.1 ≠ move.2)) := by
    apply List.filter_congr
    intro move member
    by_cases equal : move.1 = move.2 <;> simp [bne, equal]
  rw [scalarFilter]
  exact filteredOptionOrder_sourceNative label slots allocation moves distinct input

/-- The actual acyclic dispatch test ensures that every input destination is
absent from all input sources. This derives the fast branch's ready guard. -/
theorem acyclicDispatch_ready {α : Type} [DecidableEq α]
    (moves : List (α × α))
    (independent : moves.any (fun move => decide (move.2 ∈ moves.map Prod.fst)) = false)
    (move : α × α) (member : move ∈ moves) : move.1 ∉ moves.map Prod.snd := by
  simp only [List.any_eq_false, decide_eq_true_eq] at independent
  intro reads
  obtain ⟨other, present, equal⟩ := List.mem_map.mp reads
  exact independent other present (List.mem_map.mpr ⟨move, member, equal.symm⟩)

/-- SOME formatting never occupies either real reserved scratch register,
even for arbitrary spill indices and a zero frame. -/
theorem formattedSome_not_reserved (slots index : Nat) :
    let location := formattedLocation
      (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
      (formatVar cakeRiscVRegisterCount (some index))
    location ≠ WordLocation.register cakeRiscVRegisterCount ∧
      location ≠ WordLocation.register (cakeRiscVRegisterCount + 1) := by
  dsimp only
  by_cases below : index < cakeRiscVRegisterCount
  · simp only [cakeRiscVRegisterCount] at below
    have scratch : index ≠ 22 := by omega
    have temporary : index ≠ 23 := by omega
    simp [formatVar, formattedLocation, cakeRiscVRegisterCount, below, scratch, temporary]
  · simp only [cakeRiscVRegisterCount] at below
    simp [formatVar, formattedLocation, cakeRiscVRegisterCount, below]

/-- Actual remove-destination keeps precisely the tail of a destination-unique
head list. It cannot silently remove another move with the same destination. -/
theorem removeDestination_head (move : WordLocation × WordLocation)
    (rest : List (WordLocation × WordLocation))
    (distinct : ((move :: rest).map Prod.fst).Nodup) :
    wordStackLocationMoveRemoveDestination move.1 (move :: rest) = rest := by
  have absent : move.1 ∉ rest.map Prod.fst := (List.nodup_cons.mp distinct).1
  have keep : ∀ next ∈ rest, (next.1 != move.1) = true := by
    intro next member
    have different : next.1 ≠ move.1 := by
      intro equal
      exact absent (List.mem_map.mpr ⟨next, member, equal⟩)
    simp [bne, different]
  simp only [wordStackLocationMoveRemoveDestination, List.filter_cons, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  exact List.filter_eq_self.mpr keep

/-- Actual acyclic auxiliary lowering follows the input head and exact tail.
This step equation derives all optimized rejection/ready tests from ordinary
operand safety, destination uniqueness and the actual dispatch predicate. -/
theorem acyclicAux_cons {α : Type} (config : WordStackConfig) (fuel : Nat)
    (move : WordLocation × WordLocation) (rest : List (WordLocation × WordLocation))
    (distinct : ((move :: rest).map Prod.fst).Nodup)
    (independent : (move :: rest).any
      (fun next => decide (next.2 ∈ (move :: rest).map Prod.fst)) = false)
    (safe : ∀ next ∈ move :: rest,
      next.1 ≠ .register config.scratch ∧ next.1 ≠ .register config.addressScratch) :
    wordStackParallelLocationMoveAux (α := α) config (fuel + 1) (move :: rest) = (do
      let first ← wordStackLocationMove config move.1 move.2
      let remaining ← wordStackParallelLocationMoveAux config fuel rest
      pure (wordStackJoin first remaining)) := by
  have ready := acyclicDispatch_ready (move :: rest) independent move (by simp)
  have scratch : (move :: rest).any
      (fun next => decide (next.1 = WordLocation.register config.scratch)) = false := by
    simp only [List.any_eq_false, decide_eq_true_eq]
    intro next member
    exact (safe next member).1
  have temporary : (move :: rest).any
      (fun next => decide (next.1 = WordLocation.register config.addressScratch)) = false := by
    simp only [List.any_eq_false, decide_eq_true_eq]
    intro next member
    exact (safe next member).2
  have removal := removeDestination_head move rest distinct
  change ((move :: rest).map (fun next => next.1)).Nodup at distinct
  change move.1 ∉ (move :: rest).map (fun next => next.2) at ready
  rcases move with ⟨destination, source⟩
  have uniqueTest : decide (((destination, source) :: rest).map (fun next => next.1)).Nodup = true := by
    simp only [decide_eq_true_eq]
    exact distinct
  have readyTest : decide (destination ∉ ((destination, source) :: rest).map (fun next => next.2)) = true := by
    simp only [decide_eq_true_eq]
    exact ready
  simp only [wordStackParallelLocationMoveAux, wordStackLocationMoveDestinations,
    scratch, temporary, readyTest, removal]
  simp
  intro impossible
  have contradiction := uniqueTest.symm.trans impossible
  cases contradiction

/-- Projection commutes with the actual optional production join, retaining
all failure cases. This factors the auxiliary recursion's real do-chain. -/
private theorem optionalJoin_project {width : Nat} [NeZero width]
    (first second : Option (StackProg (BitVec width))) :
    (do let first ← first; let second ← second; pure (wordStackJoin first second)).bind project =
    (do let first ← first.bind project; let second ← second.bind project; pure (join first second)) := by
  cases first <;> cases second <;> simp [bind, pure, join_project]

/-- Whole actual acyclic auxiliary output projects to complete ordinary
optional-list materialization. Fuel sufficiency follows the actual list length;
no successful lowering or projected output is a premise. -/
theorem acyclicAux_project {width : Nat} [NeZero width]
    (config : WordStackConfig) (fuel : Nat) (moves : List (WordLocation × WordLocation))
    (bounded : moves.length < fuel)
    (distinct : (moves.map Prod.fst).Nodup)
    (independent : moves.any (fun next => decide (next.2 ∈ moves.map Prod.fst)) = false)
    (safe : ∀ next ∈ moves,
      next.1 ≠ .register config.scratch ∧ next.1 ≠ .register config.addressScratch) :
    (wordStackParallelLocationMoveAux (α := BitVec width) config fuel moves).bind project =
      optionMoveList config (moves.map (fun move => (some move.1, some move.2))) := by
  induction fuel generalizing moves with
  | zero => omega
  | succ fuel ih =>
      cases moves with
      | nil =>
          simp [wordStackParallelLocationMoveAux, wordStackLocationMoveDestinations,
            project, productionToHolProg, progFromProduction, progWToHolProg, Prog.map, optionMoveList]
      | cons move rest =>
          have tailDistinct : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp distinct).2
          have tailIndependent : rest.any (fun next => decide (next.2 ∈ rest.map Prod.fst)) = false := by
            simp only [List.any_eq_false, decide_eq_true_eq] at independent ⊢
            intro next member reads
            exact independent next (by simp [member]) (by simp [reads])
          have tail := ih rest (by simp only [List.length_cons] at bounded; omega)
            tailDistinct tailIndependent (fun next member => safe next (by simp [member]))
          rw [acyclicAux_cons config fuel move rest distinct independent safe, optionalJoin_project,
            locationMove_project, tail]
          simp [optionMoveList, bind, pure]

/-- With no destination read by any pending move, the native scheduler emits
pending moves in their original order. Arbitrary prior emitted moves are retained. -/
private theorem pmov_independent {α : Type} [DecidableEq α]
    (pending emitted : List (Compiler.Backend.Parmove.Move α))
    (ready : ∀ move ∈ pending, move.1 ∉ pending.map Prod.snd) :
    (Compiler.Backend.Parmove.pmov (pending, [], emitted)).2.2 = pending.reverse ++ emitted := by
  induction pending generalizing emitted with
  | nil => rw [Compiler.Backend.Parmove.pmov.eq_def]; simp
  | cons move rest ih =>
      have head := ready move (by simp)
      have different : move.2 ≠ move.1 := by
        intro equal
        exact head (List.mem_map.mpr ⟨move, by simp, equal⟩)
      have tailReady : ∀ next ∈ rest, next.1 ∉ rest.map Prod.snd := by
        intro next member reads
        exact ready next (by simp [member]) (by simp [reads])
      have noRead : move.1 ∉ rest.map Prod.snd := by
        intro reads
        exact head (by simp [reads])
      have split := (Compiler.Backend.Parmove.splitSource_suffix_nil_iff move.1 rest).mpr noRead
      rw [pmov_fstep (move :: rest, [], emitted)]
      simp only [Compiler.Backend.Parmove.fstep, different, ↓reduceIte]
      rw [pmov_fstep (rest, [move], emitted)]
      rcases move with ⟨destination, source⟩
      simp only [Compiler.Backend.Parmove.fstep, split]
      rw [ih _ tailReady]
      simp [List.reverse_cons, List.append_assoc]

/-- The native public scheduler keeps exactly the original lifted list on
the concrete acyclic dispatch branch. No scheduled order is assumed. -/
theorem parmove_independent {α : Type} [DecidableEq α]
    (moves : List (α × α))
    (independent : moves.any (fun move => decide (move.2 ∈ moves.map Prod.fst)) = false) :
    Compiler.Backend.Parmove.parmove moves =
      moves.map (fun move => (some move.1, some move.2)) := by
  let lifted := moves.map (fun move => (some move.1, some move.2))
  have ready : ∀ move ∈ lifted, move.1 ∉ lifted.map Prod.snd := by
    intro move member reads
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨other, otherPresent, equal⟩ := List.mem_map.mp reads
    obtain ⟨source, sourcePresent, rfl⟩ := List.mem_map.mp otherPresent
    have scalarEqual := Option.some.inj equal
    exact acyclicDispatch_ready moves independent original present
      (List.mem_map.mpr ⟨source, sourcePresent, scalarEqual⟩)
  have result := pmov_independent lifted [] ready
  change (Compiler.Backend.Parmove.pmov (lifted, [], [])).2.2.reverse = lifted
  rw [result]
  simp

/-- Both actual production dispatch branches project to the same literal
native optional schedule. Reserved-register safety and uniqueness are input
operand facts, not successful lowering or desired output assumptions. -/
theorem parallelLocationMove_project {width : Nat} [NeZero width]
    (config : WordStackConfig) (moves : List (WordLocation × WordLocation))
    (distinct : (moves.map Prod.fst).Nodup)
    (safe : ∀ next ∈ moves,
      next.1 ≠ .register config.scratch ∧ next.1 ≠ .register config.addressScratch) :
    (wordStackParallelLocationMove (α := BitVec width) config moves).bind project =
      optionMoveList config (Compiler.Backend.Parmove.parmove
        (moves.filter (fun move => move.1 != move.2))) := by
  let filtered := moves.filter (fun move => move.1 != move.2)
  have filteredDistinct : (filtered.map Prod.fst).Nodup :=
    (List.filter_sublist.map Prod.fst).nodup distinct
  have filteredSafe : ∀ next ∈ filtered,
      next.1 ≠ .register config.scratch ∧ next.1 ≠ .register config.addressScratch := by
    intro next member
    exact safe next (List.mem_filter.mp member).1
  unfold wordStackParallelLocationMove
  change ((if filtered.any (fun move => decide (move.2 ∈ filtered.map Prod.fst)) then _ else _) :
    Option (StackProg (BitVec width))).bind project = _
  split
  · rw [ProductionScheduler.optionOrder_eq_parmove]
    simp only
    exact optionMoveList_project config _
  · rename_i absent
    have independent : filtered.any (fun move => decide (move.2 ∈ filtered.map Prod.fst)) = false := by
      cases value : filtered.any (fun move => decide (move.2 ∈ filtered.map Prod.fst)) <;> simp_all
    rw [acyclicAux_project config (filtered.length + 1) filtered (by omega)
      filteredDistinct independent filteredSafe, parmove_independent filtered independent]

/-- Complete actual parallel-location lowering of formatted scalar moves
projects to literal native scheduled code. Both initial filtering and optimized
dispatch are proved; location uniqueness and safety are derived from the real
frame domain and original scalar destination convention. -/
theorem parallelFormattedMove_sourceNative {width : Nat} [NeZero width]
    (label slots : Nat) (allocation : WordSpillState) (moves : List (Nat × Nat))
    (distinct : Compiler.Backend.Parmove.windmill moves)
    (input : ∀ move ∈ moves,
      move.1 < cakeRiscVRegisterCount + slots ∧ move.2 < cakeRiscVRegisterCount + slots) :
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    let location := fun i => formattedLocation kf (formatVar cakeRiscVRegisterCount (some i))
    (wordStackParallelLocationMove (α := BitVec width)
      (sourceWordStackConfig label allocation slots) (moves.map (Prod.map location location))).bind project =
      some (Compiler.Backend.WordToStack.Native.wMoveAuxNative
        ((Parmove.parmove moves).map (fun move =>
          (formatVar cakeRiscVRegisterCount move.1, formatVar cakeRiscVRegisterCount move.2))) kf) := by
  dsimp only
  let location := fun i => formattedLocation
    (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    (formatVar cakeRiscVRegisterCount (some i))
  have unique : ((moves.map (Prod.map location location)).map Prod.fst).Nodup := by
    have original := distinct.map_on (f := location) (by
      intro x memberX y memberY equal
      obtain ⟨left, leftMember, leftEqual⟩ := List.mem_map.mp memberX
      obtain ⟨right, rightMember, rightEqual⟩ := List.mem_map.mp memberY
      have boundsX : x < cakeRiscVRegisterCount + slots := by
        simpa only [leftEqual] using (input left leftMember).1
      have boundsY : y < cakeRiscVRegisterCount + slots := by
        simpa only [rightEqual] using (input right rightMember).1
      exact Option.some.inj (formattedOption_injective cakeRiscVRegisterCount slots (some x) (some y)
        (by intro i equal; cases Option.some.inj equal; exact boundsX)
        (by intro i equal; cases Option.some.inj equal; exact boundsY) equal))
    simpa [List.map_map, Function.comp_def] using original
  have safe : ∀ next ∈ moves.map (Prod.map location location),
      next.1 ≠ WordLocation.register (sourceWordStackConfig label allocation slots).scratch ∧
      next.1 ≠ WordLocation.register (sourceWordStackConfig label allocation slots).addressScratch := by
    intro next member
    obtain ⟨move, _, rfl⟩ := List.mem_map.mp member
    simpa [location, sourceWordStackConfig, cakeRiscVRegisterCount] using formattedSome_not_reserved slots move.1
  rw [parallelLocationMove_project _ _ unique safe]
  have scheduled := locationFilteredOptionOrder_sourceNative (width := width) label slots allocation moves distinct input
  dsimp only at scheduled
  rw [ProductionScheduler.optionOrder_eq_parmove] at scheduled
  simpa only [Option.bind_some] using scheduled

/-- Actual name-list lookup succeeds from the shared allocation producer and
real scheduler operand occurrences. Every returned location is the native
format of its actual total colour; no lookup-success premise is added. -/
theorem retainedConsumer_locationMoves {width : Nat} [NeZero width]
    (dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source lowered : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output)
    (moves : List (Nat × Nat))
    (occurs : ∀ move ∈ moves,
      ProductionMoveDomain.SchedulerOperand move.1 output.program ∧
      ProductionMoveDomain.SchedulerOperand move.2 output.program) :
    let slots := cakeWordFrameSlots output.allocation parameters lowered
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    let location := fun name => formattedLocation kf
      (formatVar cakeRiscVRegisterCount (some (CakeAlloc.totalColour output.colouring name / 2)))
    wordStackLocationMovesFromNames (sourceWordStackConfig label output.allocation slots) moves =
      some (moves.map (Prod.map location location)) := by
  dsimp only
  induction moves with
  | nil => simp [wordStackLocationMovesFromNames]
  | cons move rest ih =>
      have head := occurs move (by simp)
      have destination := (ProductionMoveDomain.retainedConsumer_formatOperand
        dead unreach ssa label parameters source lowered output produced move.1 head.1).1
      have sourceLookup := (ProductionMoveDomain.retainedConsumer_formatOperand
        dead unreach ssa label parameters source lowered output produced move.2 head.2).1
      have tail := ih (fun next member => occurs next (by simp [member]))
      rcases move with ⟨destinationName, sourceName⟩
      simp only [wordStackLocationMovesFromNames, destination, sourceLookup, tail,
        bind, pure, Option.bind_some, List.map_cons]
      rfl

private theorem prodMap_function {α β γ δ : Type} (f : α → γ) (g : β → δ) :
    Prod.map f g = (fun pair => (f pair.1, g pair.2)) := by
  funext pair
  cases pair
  rfl

/-- Full actual retained-allocation move-list correspondence. The real
producer derives name lookup, frame bounds, reserved-register safety and both
lowering branches. Only the original destination convention remains; no target
run, successful move lowering, desired code or arbitrary numeric bound is used. -/
theorem retainedConsumer_moveListNative {width : Nat} [NeZero width]
    (dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source lowered : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa
      dead unreach ssa label parameters source = some output)
    (moves : List (Nat × Nat))
    (occurs : ∀ move ∈ moves,
      ProductionMoveDomain.SchedulerOperand move.1 output.program ∧
      ProductionMoveDomain.SchedulerOperand move.2 output.program)
    (distinct : Parmove.windmill (moves.map (fun move =>
      (CakeAlloc.totalColour output.colouring move.1 / 2,
       CakeAlloc.totalColour output.colouring move.2 / 2)))) :
    let slots := cakeWordFrameSlots output.allocation parameters lowered
    let kf := (cakeRiscVRegisterCount, (if slots = 0 then 0 else slots + 1), slots)
    (wordStackMoveList (α := BitVec width) (sourceWordStackConfig label output.allocation slots) moves).bind project =
      some (WordToStack.Native.wMoveNative
        (moves.map (Prod.map (CakeAlloc.totalColour output.colouring)
          (CakeAlloc.totalColour output.colouring))) kf) := by
  dsimp only
  have lookup := retainedConsumer_locationMoves dead unreach ssa label parameters source lowered output produced moves occurs
  dsimp only at lookup
  simp only [wordStackMoveList, lookup, bind, Option.bind_some]
  have bounds : ∀ move ∈ moves.map (fun move =>
      (CakeAlloc.totalColour output.colouring move.1 / 2,
       CakeAlloc.totalColour output.colouring move.2 / 2)),
      move.1 < cakeRiscVRegisterCount + cakeWordFrameSlots output.allocation parameters lowered ∧
      move.2 < cakeRiscVRegisterCount + cakeWordFrameSlots output.allocation parameters lowered := by
    intro scalar member
    obtain ⟨move, present, equal⟩ := List.mem_map.mp member
    subst scalar
    exact ⟨(ProductionMoveDomain.retainedConsumer_formatOperand
      dead unreach ssa label parameters source lowered output produced move.1 (occurs move present).1).2,
      (ProductionMoveDomain.retainedConsumer_formatOperand
      dead unreach ssa label parameters source lowered output produced move.2 (occurs move present).2).2⟩
  have result := parallelFormattedMove_sourceNative (width := width) label
    (cakeWordFrameSlots output.allocation parameters lowered) output.allocation
    (moves.map (fun move => (CakeAlloc.totalColour output.colouring move.1 / 2,
       CakeAlloc.totalColour output.colouring move.2 / 2))) distinct bounds
  simpa [WordToStack.Native.wMoveNative, List.map_map, Function.comp_def, prodMap_function] using result

end Flapjack.ProductionMoveMaterialization
