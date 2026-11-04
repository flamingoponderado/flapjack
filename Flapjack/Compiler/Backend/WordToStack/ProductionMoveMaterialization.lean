import Flapjack.Compiler.Backend.WordToStack.ProductionMoveDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionMoves
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

private theorem prodMap_function {α β γ δ : Type} (f : α → γ) (g : β → δ) :
    Prod.map f g = (fun pair => (f pair.1, g pair.2)) := by
  funext pair
  cases pair
  rfl

end Flapjack.ProductionMoveMaterialization
