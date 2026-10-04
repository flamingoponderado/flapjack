import Flapjack.Compiler.Backend.Semantics.StackSem.State

/-! Counterpart of StackSem's code lookup and clock-clamping prerequisites.
The payload of the code tree and the result component of the clock pair retain
HOL's polymorphism. No evaluator or production-path refinement is supplied. -/
namespace Flapjack.StackSemControl

/-- Canonical finite-support state roundtrip re-export; infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Direct code label lookup or indirect lookup through a zero-offset Loc.
    The register-key carrier is arbitrary, independently of the positive
    register-word dimension and code payload. This is the full original
    `num + β` / `β |-> γ word_loc` signature, not a Nat-key specialization.
    The code tree is sptree, not a finite-support fmap translation. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "find_code_def"
  (fmap_as_finite_support_relation := [regs]) (words_as_type_indexed_bitvec)]
def findCode {width : Nat} [NeZero width] {κ : Type} {α : Type}
    (target : Sum Nat κ) (regs : HolFiniteMapExact κ (WordLocW width))
    (code : Spt α) : Option α :=
  match target with
  | .inl label => sptLookup label code
  | .inr reg =>
      match regs.lookup reg with
      | some (.loc label 0) => sptLookup label code
      | _ => none

/-- Clamp only the returned state's clock to the input/returned minimum.
HOL's two states have independent word, code, and FFI carriers: only their
natural-number clocks are related. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def fixClock {width returnedWidth : Nat} [NeZero width] [NeZero returnedWidth]
    {C F ReturnedC ReturnedF R : Type}
    (s : StackSemStateFiniteExact width C F)
    (x : R × StackSemStateFiniteExact returnedWidth ReturnedC ReturnedF) :
    R × StackSemStateFiniteExact returnedWidth ReturnedC ReturnedF :=
  (x.1, { x.2 with clock := min s.clock x.2.clock })

/-- HOL's local clock bound, retaining its sole successful-pair equality premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fixClockImp {width returnedWidth : Nat} [NeZero width] [NeZero returnedWidth]
    {C F ReturnedC ReturnedF R : Type}
    (s : StackSemStateFiniteExact width C F)
    (x : R × StackSemStateFiniteExact returnedWidth ReturnedC ReturnedF) (res : R)
    (s1 : StackSemStateFiniteExact returnedWidth ReturnedC ReturnedF)
    (h : fixClock s x = (res, s1)) : s1.clock ≤ s.clock := by
  have hc := congrArg (fun pair => pair.2.clock) h
  change min s.clock x.2.clock = s1.clock at hc
  rw [← hc]
  exact Nat.min_le_left _ _

/-- HOL loop reentry: normal completion and Continue 0 reenter; every other
control result leaves the current loop. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "cont_loop_def"
  (words_as_type_indexed_bitvec)]
def contLoop {width : Nat} [NeZero width] : Option (StackSemResult width) → Bool
  | none => true
  | some (.continue label) => decide (label = 0)
  | _ => false

/-- HOL loop exit: Break 0 becomes normal completion, positive Break labels
and all Continue labels decrement by natural monus, other results propagate.
In evaluate's Loop clause, Continue 0 takes contLoop's reentry branch first. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "exit_loop_def"
  (words_as_type_indexed_bitvec)]
def exitLoop {width : Nat} [NeZero width] :
    Option (StackSemResult width) → Option (StackSemResult width)
  | some (.break label) => if label = 0 then none else some (.break (label - 1))
  | some (.continue label) => some (.continue (label - 1))
  | result => result

/-- HOL `dest_Seq` (`cakeml/compiler/backend/semantics/stackSemScript.sml`):
    expose a `Seq`'s two immediate sub-programs, otherwise `none`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def destSeq {width : Nat} [NeZero width] :
    Flapjack.Compiler.Backend.StackLang.HolProg width →
      Option (Flapjack.Compiler.Backend.StackLang.HolProg width ×
        Flapjack.Compiler.Backend.StackLang.HolProg width)
  | .seq first second => some (first, second)
  | _ => none

/-- HOL `bad_fun_return_def` (`cakeml/compiler/backend/semantics/stackSemScript.sml:754-758`):
a call/jump sub-evaluation is a bad function return when it produced `NONE` or
a `Break`/`Continue`; every other result propagates. Exact StackSem
`StackSemResult` classifier, distinct from WordSem's same-named definition over
its different result type. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "bad_fun_return_def"
  (words_as_type_indexed_bitvec)]
def badFunReturn {width : Nat} [NeZero width] : Option (StackSemResult width) → Bool
  | none => true
  | some (.break _) => true
  | some (.continue _) => true
  | _ => false

end Flapjack.StackSemControl
