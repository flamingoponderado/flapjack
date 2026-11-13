module

public import Flapjack.Compiler.Backend.RegAlloc.Exceptions
public import Flapjack.Translator.Monadic.MonadBase

@[expose] public section

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal state-exception list filter (`reg_allocScript.sml:170-179`).
Predicates run from head to tail; each successful `true` prepends the element
to the accumulator, so selected elements end up reversed in front of the
initial accumulator, which is returned unchanged on the empty list. The
accepted bind propagates a failure together with its returned state and skips
all later predicates. Value, state and exception carriers are independent, as
in the original type. Production allocator routing remains separate work. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "st_ex_FILTER_def"]
def stExFilter {state value exception : Type}
    (predicate : value → M state Bool exception) :
    List value → List value → M state (List value) exception
  | [], acc => ret acc
  | head :: tail, acc =>
    bind (predicate head) (fun selected =>
      if selected then stExFilter predicate tail (head :: acc)
      else stExFilter predicate tail acc)

/-- A filter whose predicate is pure on the given list returns the reversed
selection together with the unchanged state. Flapjack infrastructure shared by
the production background and initialization proofs; no separate HOL
declaration is claimed. -/
theorem stExFilter_pure {α : Type} (predicate : α → M State Bool StateException)
    (pure : α → Bool) (nodes acc : List α) (state : State)
    (reads : ∀ node ∈ nodes, predicate node state = (.success (pure node), state)) :
    stExFilter predicate nodes acc state =
      (.success ((nodes.filter pure).reverse ++ acc), state) := by
  induction nodes generalizing acc with
  | nil => rfl
  | cons node rest ih =>
    simp only [stExFilter, Translator.Monadic.MonadBase.bind, reads node List.mem_cons_self]
    cases selected : pure node <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, List.filter_cons, selected,
        List.reverse_cons, List.append_assoc, List.singleton_append]
    all_goals exact ih _ (fun next member => reads next (List.mem_cons_of_mem node member))

end Flapjack.RegAlloc
