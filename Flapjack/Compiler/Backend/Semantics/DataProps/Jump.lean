module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! Exception-jump transport for states with the same control stack. -/
namespace Flapjack.Compiler.Backend.DataSem

/-- An exception jump depends on the input stack and handler for its control
fields; all other fields come from the state being jumped. This auxiliary
lemma has no direct HOL counterpart. -/
theorem jumpExc_transport {C F : Type} (source target jumped : State C F)
    (stack : target.stack = source.stack) (handler : target.handler = source.handler)
    (run : jumpExc source = some jumped) :
    jumpExc target = some { target with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize } := by
  unfold jumpExc at run ⊢
  rw [stack, handler]
  split at run <;> simp_all
  split at run <;> simp_all
  subst jumped
  simp


/-- Flapjack infrastructure for the reviewed HOL `rich_list$LASTN` rendering
    `wordSemLastN`: the last `n` elements are the suffix dropped after
    `LENGTH l - n`.  No separate HOL original; HOL states the corresponding
    facts through `LASTN_def` and `REVERSE_TAKE`. -/
theorem wordSemLastN_eq_drop {α : Type} (n : Nat) (l : List α) :
    wordSemLastN n l = l.drop (l.length - n) := by
  unfold wordSemLastN
  rw [List.take_reverse, List.reverse_reverse]

/-- Exact HOL `jump_exc_IMP` (`dataPropsScript.sml:1830`): a successful jump
    finds the exception frame at `LASTN (handler + 1)` and returns the state
    with that frame's handler, locals, stack tail and locals size. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "jump_exc_IMP"]
theorem jumpExcImp {C F : Type} (s t : State C F) (run : jumpExc s = some t) :
    s.handler < s.stack.length ∧
    ∃ (n : Nat) (e : Spt DataSem.Value) (ls : Option Nat) (xs : List Stack),
      wordSemLastN (s.handler + 1) s.stack = .exc ls e n :: xs ∧
      t = { s with handler := n, locals := e, stack := xs, localsSize := ls } := by
  unfold jumpExc at run
  by_cases h : s.handler < s.stack.length
  · simp only [h, if_true] at run
    cases d : s.stack.drop (s.stack.length - (s.handler + 1)) with
    | nil =>
      simp only [d] at run
      cases run
    | cons frame rest =>
      cases frame with
      | env size env =>
        simp only [d] at run
        cases run
      | exc ls e n =>
        simp only [d, Option.some.injEq] at run
        refine ⟨h, n, e, ls, rest, ?_, ?_⟩
        · rw [wordSemLastN_eq_drop, d]
        · rw [run]
  · simp only [h, if_false] at run
    cases run

/-- Exact HOL `jump_exc_NONE` (`dataPropsScript.sml:1819`): the handler search
reads only the handler index and the control stack, so updates to the locals,
clock, stack maximum, locals size and safety flag preserve its outcome. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "jump_exc_NONE"]
theorem jumpExc_none_frame {C F : Type} (state : State C F) (locals : Spt DataSem.Value)
    (clock : Nat) (mx : Option Nat) (localsSize : Option Nat) (safe : Bool) :
    (jumpExc { state with locals := locals } = none ↔ jumpExc state = none) ∧
    (jumpExc { state with clock := clock } = none ↔ jumpExc state = none) ∧
    (jumpExc { state with stackMax := mx } = none ↔ jumpExc state = none) ∧
    (jumpExc { state with localsSize := localsSize } = none ↔ jumpExc state = none) ∧
    (jumpExc { state with safeForSpace := safe } = none ↔ jumpExc state = none) := by
  have frame {a b : State C F} (handler : a.handler = b.handler) (stack : a.stack = b.stack) :
      (jumpExc a = none ↔ jumpExc b = none) := by
    unfold jumpExc
    rw [handler, stack]
    by_cases h : b.handler < b.stack.length
    · simp only [if_pos h]
      split <;> simp
    · simp [h]
  exact ⟨frame rfl rfl, frame rfl rfl, frame rfl rfl, frame rfl rfl, frame rfl rfl⟩

end Flapjack.Compiler.Backend.DataSem
