import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackLists
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

/-!
# `evaluate_stack_swap` statement

The per-program conclusion of `wordPropsScript.sml:2316-2363`
`evaluate_stack_swap`, as an untagged definition so that HOL's `evaluate_ind`
cases can be stated as genuine cases of the theorem. Flapjack infrastructure;
the tagged assembly states the HOL theorem itself.
-/

namespace Flapjack

namespace WordSemStackEq

open WordSemStateFiniteExact

/-- HOL `evaluate_stack_swap`'s result-dependent conclusion at `(c, s)`:
`SOME Error` is unconstrained; `FinalFFI`, `TimeOut` and `NotEnoughSpace`
empty the stack and locals and are stack-insensitive; `Exception` lands in the
`LASTN (s.handler + 1)` handler frame and transports to every value-equal
stack with that frame; every other result keeps the stack keys and handler and
transports to every value-equal stack. -/
def stackSwapPost {width : Nat} [NeZero width] {C F : Type}
    (c : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Prop :=
  match evaluate c s with
  | (some .error, _) => True
  | (some (.finalFfi e), s1) =>
      s1.stack = [] ∧ s1.locals = .ln ∧
        ∀ xs, sValEq s.stack xs → evaluate c { s with stack := xs } = (some (.finalFfi e), s1)
  | (some .timeOut, s1) =>
      s1.stack = [] ∧ s1.locals = .ln ∧
        ∀ xs, sValEq s.stack xs → evaluate c { s with stack := xs } = (some .timeOut, s1)
  | (some .notEnoughSpace, s1) =>
      s1.stack = [] ∧ s1.locals = .ln ∧
        ∀ xs, sValEq s.stack xs → evaluate c { s with stack := xs } = (some .notEnoughSpace, s1)
  | (some (.exception x y), s1) =>
      s.handler < s.stack.length ∧
      ∃ e0 e n ls m lss,
        wordSemLastN (s.handler + 1) s.stack = .stackFrame m e0 e (some n) :: ls ∧
        m = s1.localsSize ∧
        (e.map Prod.fst = lss.map Prod.fst ∧
          s1.locals = sptUnion (sptFromAList lss) (sptFromAList e0)) ∧
        sKeyEq s1.stack ls ∧ s1.handler = n.1 ∧
        ∀ xs e0' e' ls',
          wordSemLastN (s.handler + 1) xs = .stackFrame m e0' e' (some n) :: ls' ∧
            sValEq s.stack xs →
          ∃ st locs,
            evaluate c { s with stack := xs } =
              (some (.exception x y), { s1 with stack := st, handler := n.1, locals := locs }) ∧
            (∃ lss', e'.map Prod.fst = lss'.map Prod.fst ∧
              locs = sptUnion (sptFromAList lss') (sptFromAList e0') ∧
              lss.map Prod.snd = lss'.map Prod.snd) ∧
            sValEq s1.stack st ∧ sKeyEq ls' st
  | (res, s1) =>
      sKeyEq s.stack s1.stack ∧ s1.handler = s.handler ∧
        ∀ xs, sValEq s.stack xs →
          ∃ st, evaluate c { s with stack := xs } = (res, { s1 with stack := st }) ∧
            sValEq s1.stack st ∧ sKeyEq xs st

end WordSemStackEq

end Flapjack
