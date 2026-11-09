module

public import Flapjack.Compiler.Backend.DataLive
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Misc.SptreeLookup
public import Flapjack.Compiler.Backend.Semantics.DataProps.Variables

@[expose] public section

/-! State relation and local-variable lemmas for data liveness. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem
open Classical

/-- States agree on the fields observed by the liveness proof and on every
live local. This follows the source relation but is untagged until its state
carriers and complete statement have been reviewed against HOL. -/
def stateRel {C F : Type} (source target : State C F) (live : NumSet) : Prop :=
  source.code = target.code ∧ source.clock = target.clock ∧ source.space = target.space ∧
  source.ffi = target.ffi ∧ source.refs = target.refs ∧ source.global = target.global ∧
  source.handler = target.handler ∧ source.stack.length = target.stack.length ∧
  source.compile = target.compile ∧ source.compileOracle = target.compileOracle ∧
  source.tstamps = target.tstamps ∧ source.limits = target.limits ∧
  source.stackFrameSizes = target.stackFrameSizes ∧
  ∀ key, sptMem key live → sptLookup key source.locals = sptLookup key target.locals

/-- A state is related to itself for every live set. -/
theorem stateRel_refl {C F : Type} (state : State C F) (live : NumSet) : stateRel state state live := by
  simp [stateRel]

/-- Restricting a live set preserves the state relation. -/
theorem stateRel_mono {C F : Type} (source target : State C F) (larger smaller : NumSet)
    (related : stateRel source target larger)
    (subset : ∀ key, sptMem key smaller → sptMem key larger) : stateRel source target smaller := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  exact ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames,
    fun key member => locals key (subset key member)⟩

/-- Inserting a list of live names records both the new names and the
previous live set. -/
theorem mem_listInsert (names : List Nat) (live : NumSet) (key : Nat) :
    sptMem key (sptListInsert names live) ↔ key ∈ names ∨ sptMem key live := by
  induction names generalizing live with
  | nil => simp [sptListInsert]
  | cons name names ih =>
    simp only [sptListInsert, ih, sptMem_sptInsert, List.mem_cons]
    simp [or_assoc, or_left_comm, or_comm]

/-- Intersection keeps exactly the keys present in both sparse sets. -/
theorem mem_inter (left right : NumSet) (key : Nat) :
    sptMem key (sptInter left right) ↔ sptMem key left ∧ sptMem key right := by
  exact Iff.of_eq (congrFun (sptDomain_sptInter left right) key)

/-- A successful cut has exactly the requested names and retains their
original values. -/
theorem cutEnv_lookup {α : Type} (names : NumSet) (env cut : Spt α)
    (run : DataSem.cutEnv names env = some cut) (key : Nat) :
    sptLookup key cut = if sptMem key names then sptLookup key env else none := by
  classical
  unfold DataSem.cutEnv at run
  split at run
  · simp only [Option.some.injEq] at run
    subst cut
    rw [sptLookup_mkWf, sptLookup_sptInterCases]
    cases envLookup : sptLookup key env <;> cases namesLookup : sptLookup key names <;>
      simp [sptMem, sptDomain, namesLookup]
  · simp at run

/-- A successful source cut can be mirrored on the intersection of its names
with the live set, and the resulting environments agree on every live key. -/
theorem cutEnv_inter_related {C F : Type} (source target : State C F) (names live : NumSet)
    (related : stateRel source target (sptInter names live)) (sourceCut : Spt Value)
    (run : DataSem.cutEnv names source.locals = some sourceCut) :
    ∃ targetCut, DataSem.cutEnv (sptInter names live) target.locals = some targetCut ∧
      ∀ key, sptMem key live → sptLookup key sourceCut = sptLookup key targetCut := by
  classical
  have sourcePresent : ∀ key, sptMem key names → sptMem key source.locals := by
    unfold DataSem.cutEnv at run
    split at run
    · assumption
    · simp at run
  have targetPresent : ∀ key, sptMem key (sptInter names live) → sptMem key target.locals := by
    intro key member
    have existsSource := sourcePresent key ((mem_inter names live key).1 member).1
    have lookupEq := related.2.2.2.2.2.2.2.2.2.2.2.2.2 key member
    simpa [sptMem, sptDomain, ← lookupEq] using existsSource
  let targetCut := sptMkWf (sptInter target.locals (sptInter names live))
  have targetRun : DataSem.cutEnv (sptInter names live) target.locals = some targetCut := by
    simp only [DataSem.cutEnv, if_pos targetPresent]
    rfl
  refine ⟨targetCut, targetRun, ?_⟩
  intro key member
  rw [cutEnv_lookup names source.locals sourceCut run key,
    cutEnv_lookup (sptInter names live) target.locals targetCut targetRun key]
  by_cases present : sptMem key names
  · have both := (mem_inter names live key).2 ⟨present, member⟩
    simp [present, both, related.2.2.2.2.2.2.2.2.2.2.2.2.2 key both]
  · have absent : ¬sptMem key (sptInter names live) := by simp [mem_inter, present]
    simp [present, absent]

/-- Related states return the same value for each live local. -/
theorem stateRel_getVar {C F : Type} (source target : State C F) (live : NumSet) (key : Nat)
    (related : stateRel source target live) (member : sptMem key live) :
    DataSem.getVar key source.locals = DataSem.getVar key target.locals := by
  exact related.2.2.2.2.2.2.2.2.2.2.2.2.2 key member

/-- If every requested name is live, both states read the same value list,
including the same failure when a name is absent. -/
theorem stateRel_getVars {C F : Type} (source target : State C F) (live : NumSet) (names : List Nat)
    (related : stateRel source target live) (members : ∀ key ∈ names, sptMem key live) :
    DataSem.getVars names source.locals = DataSem.getVars names target.locals := by
  apply DataProps.every_getVars names source.locals target.locals
  intro key member
  exact related.2.2.2.2.2.2.2.2.2.2.2.2.2 key (members key member)

/-- In particular, the liveness set built by `sptListInsert` covers every
argument read by the instruction. -/
theorem stateRel_getVars_listInsert {C F : Type} (source target : State C F) (names : List Nat) (live : NumSet)
    (related : stateRel source target (sptListInsert names live)) :
    DataSem.getVars names source.locals = DataSem.getVars names target.locals := by
  apply stateRel_getVars source target (sptListInsert names live) names related
  intro key member
  exact (mem_listInsert names live key).2 (Or.inl member)

/-- Writing the same value to both states restores agreement on the written
name and retains agreement on the other live names. -/
theorem stateRel_setVar {C F : Type} (source target : State C F) (live : NumSet)
    (dest : Nat) (value : Value) (related : stateRel source target (sptDelete dest live)) :
    stateRel (setVar dest value source) (setVar dest value target) live := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  refine ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, ?_⟩
  intro key member
  by_cases same : key = dest
  · subst key
    simp [setVar, sptLookup_sptInsert_same]
  · have active : sptMem key (sptDelete dest live) := by
      simpa [sptMem, sptDomain, sptLookup_sptDelete, same] using member
    simp [setVar, sptLookup_sptInsert_ne dest key value _ same, locals key active]

/-- The liveness pass preserves skip and its state relation. -/
theorem compile_skip_correct {C F : Type} (source target : State C F) (live : NumSet)
    (related : stateRel source target (compile .skip live).2) :
    DataSem.evaluate (compile .skip live).1 target = (none, target) ∧ stateRel source target live := by
  exact ⟨by simp [compile, DataSem.evaluate], related⟩

/-- A move whose source is live produces related states on the live set
after the instruction, unless the source execution has a type error. -/
theorem evaluate_move_preserves {C F : Type} (source target sourceNext : State C F)
    (live : NumSet) (dest src : Nat) (result : Option (Flapjack.SemanticPrimitivesHOL.Result (List Value) Value))
    (related : stateRel source target (sptInsert src () (sptDelete dest live)))
    (run : DataSem.evaluate (.move dest src) source = (result, sourceNext))
    (notTypeError : result ≠ some (.err (.abort .typeError))) :
    ∃ targetNext, DataSem.evaluate (.move dest src) target = (result, targetNext) ∧
      stateRel sourceNext targetNext live := by
  have srcLive : sptMem src (sptInsert src () (sptDelete dest live)) :=
    (sptMem_sptInsert src src () _).2 (Or.inl rfl)
  have sameRead := stateRel_getVar source target _ src related srcLive
  have deleted : stateRel source target (sptDelete dest live) :=
    stateRel_mono source target _ _ related (fun key member =>
      (sptMem_sptInsert key src () _).2 (Or.inr member))
  cases read : DataSem.getVar src source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notTypeError rfl)
  | some value =>
    have targetRead : DataSem.getVar src target.locals = some value := by rw [← sameRead, read]
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨setVar dest value target, by simp [DataSem.evaluate, targetRead],
      stateRel_setVar source target live dest value deleted⟩

/-- The liveness pass preserves a non-type-error move, relating its output
states at the requested live set. -/
theorem compile_move_correct {C F : Type} (source target sourceNext : State C F)
    (live : NumSet) (dest src : Nat) (result : Option (Flapjack.SemanticPrimitivesHOL.Result (List Value) Value))
    (related : stateRel source target (compile (.move dest src) live).2)
    (run : DataSem.evaluate (.move dest src) source = (result, sourceNext))
    (notTypeError : result ≠ some (.err (.abort .typeError))) :
    ∃ targetNext, DataSem.evaluate (compile (.move dest src) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext live := by
  exact evaluate_move_preserves source target sourceNext live dest src result related run notTypeError

/-- Decrementing both clocks preserves liveness-related states. -/
theorem stateRel_decClock {C F : Type} (source target : State C F) (live : NumSet)
    (related : stateRel source target live) : stateRel (decClock source) (decClock target) live := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  exact ⟨code, by simp [decClock, clock], space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits,
    frames, locals⟩

/-- Flushing both states clears their local environments and stacks, so the
resulting states agree for any requested live set. -/
theorem stateRel_flush_true {C F : Type} (source target : State C F) (inputLive outputLive : NumSet)
    (related : stateRel source target inputLive) : stateRel (flushState true source) (flushState true target) outputLive := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  simp [stateRel, flushState, code, clock, space, ffi, refs, global, handler, compiler, oracle, stamps, limits, frames]

/-- Flushing locals on both states preserves their relation for any output
live set while retaining the related stack lengths. -/
theorem stateRel_flush_false {C F : Type} (source target : State C F) (inputLive outputLive : NumSet)
    (related : stateRel source target inputLive) : stateRel (flushState false source) (flushState false target) outputLive := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  simp [stateRel, flushState, code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames]

/-- The liveness pass preserves tick evaluation, both when it decrements the
clock and when it clears the state after a timeout. -/
theorem compile_tick_correct {C F : Type} (source target : State C F) (live : NumSet)
    (related : stateRel source target (compile .tick live).2) :
    ∃ targetNext, DataSem.evaluate (compile .tick live).1 target =
      ((DataSem.evaluate .tick source).1, targetNext) ∧
      stateRel (DataSem.evaluate .tick source).2 targetNext live := by
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by rw [← related.2.1, zero]
    refine ⟨flushState true target, ?_, ?_⟩
    · simp [compile, DataSem.evaluate, zero, targetZero]
    · simpa [DataSem.evaluate, zero] using stateRel_flush_true source target live live related
  · have targetNonzero : target.clock ≠ 0 := by rw [← related.2.1]; exact zero
    refine ⟨decClock target, ?_, ?_⟩
    · simp [compile, DataSem.evaluate, zero, targetNonzero]
    · simpa [DataSem.evaluate, zero] using stateRel_decClock source target live related

/-- The liveness pass preserves a non-type-error return and its values. -/
theorem compile_return_correct {C F : Type} (source target sourceNext : State C F)
    (live : NumSet) (names : List Nat) (result : Option (Flapjack.SemanticPrimitivesHOL.Result (List Value) Value))
    (related : stateRel source target (compile (.return names) live).2)
    (run : DataSem.evaluate (.return names) source = (result, sourceNext))
    (notTypeError : result ≠ some (.err (.abort .typeError))) :
    ∃ targetNext, DataSem.evaluate (compile (.return names) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext live := by
  have sameRead := stateRel_getVars_listInsert source target names .ln related
  cases read : DataSem.getVars names source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notTypeError rfl)
  | some values =>
    have targetRead : DataSem.getVars names target.locals = some values := by rw [← sameRead, read]
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨flushState false target, by simp [compile, DataSem.evaluate, targetRead],
      stateRel_flush_false source target _ live related⟩

/-- Space reservation remains correct when the liveness pass restricts its
saved names to the intersection with the live set. -/
theorem compile_makeSpace_correct {C F : Type} (source target sourceNext : State C F)
    (live names : NumSet) (amount : Nat)
    (result : Option (Flapjack.SemanticPrimitivesHOL.Result (List Value) Value))
    (related : stateRel source target (compile (.makeSpace amount names) live).2)
    (run : DataSem.evaluate (.makeSpace amount names) source = (result, sourceNext))
    (notTypeError : result ≠ some (.err (.abort .typeError))) :
    ∃ targetNext, DataSem.evaluate (compile (.makeSpace amount names) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext live := by
  cases sourceRun : DataSem.cutEnv names source.locals with
  | none =>
    simp [DataSem.evaluate, sourceRun] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notTypeError rfl)
  | some sourceCut =>
    obtain ⟨targetCut, targetRun, locals⟩ := cutEnv_inter_related source target names live related sourceCut sourceRun
    simp [DataSem.evaluate, sourceRun] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨addSpace { target with locals := targetCut } amount, ?_, ?_⟩
    · simp [compile, DataSem.evaluate, targetRun]
    · rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
      exact ⟨code, clock, rfl, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩

end Flapjack.Compiler.Backend.DataLive
