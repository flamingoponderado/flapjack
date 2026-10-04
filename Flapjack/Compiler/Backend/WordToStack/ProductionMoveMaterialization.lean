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
full scheduler list and native literal sequencing remain under construction. -/
namespace Flapjack.ProductionMoveMaterialization
open RiscV RiscV.CakeRegAlloc ProductionMoves
open Compiler.Backend.WordToStackRegFormat

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

end Flapjack.ProductionMoveMaterialization
