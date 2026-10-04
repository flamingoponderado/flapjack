import Flapjack.Compiler.Backend.WordDepthProof.Helpers
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.CodeOnlyGrows

/-!
# `max_depth_call_graph_lemma` statement

The per-program conclusion of `word_depthProofScript.sml:147-788`
`max_depth_call_graph_lemma`, as an untagged definition so that HOL's
`evaluate_ind` cases can be stated as genuine cases of the theorem (as for
`evaluate_stack_swap`). Flapjack infrastructure; the tagged assembly states
the HOL theorem itself. HOL `set ns SUBSET domain funs2` is "every element of
`ns` has a successful lookup in `funs2`".
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact

/-- HOL `max_depth_call_graph_lemma`'s conclusion at `(prog, s)`, with the
run's result and final state read from `evaluate prog s`, quantified over
`funs n ns funs2` with the original premises. -/
def depthPost {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ (funs : Spt (Nat × WordLangProgHOL (BitVec width))) (n : Nat) (ns : List Nat)
    (funs2 : Spt (Nat × WordLangProgHOL (BitVec width))),
    sptSubspt funs funs2 ∧ sptSubspt funs2 s.code ∧ s.localsSize = sptLookup n s.stackSize ∧
      (evaluate prog s).1 ≠ some .error ∧ n ∈ ns ∧ ns.Nodup ∧
      (∀ x, x ∈ ns → (sptLookup x funs2).isSome = true) →
    optionLe (evaluate prog s).2.stackMax
        (optionMap₂ max s.stackMax
          (optionMap₂ (· + ·) (wordSemStackSize s.stack)
            (optionMap₂ max (maxDepthGraphs s.stackSize ns ns funs funs2)
              (maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) prog))))) ∧
      (maxDepthGraphs s.stackSize ns ns funs funs2 ≠ none ∧
          maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) prog) ≠ none →
        (evaluate prog s).2.stackSize = s.stackSize ∧
          ((evaluate prog s).1 = none ∨ (∃ k, (evaluate prog s).1 = some (.break k)) ∨
              (∃ k, (evaluate prog s).1 = some (.continue k)) →
            (evaluate prog s).2.localsSize = s.localsSize))

/-- A run that is not `Error` and leaves `stack_max`, `stack_size` and (for a
normal, `Break` or `Continue` result) `locals_size` unchanged satisfies the
conclusion, whatever the call graph (Flapjack infrastructure for the leaf
cases). -/
theorem depthPost_of_const {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (h : (evaluate prog s).1 ≠ some .error →
      (evaluate prog s).2.stackMax = s.stackMax ∧
        (evaluate prog s).2.stackSize = s.stackSize ∧
        ((evaluate prog s).1 = none ∨ (∃ k, (evaluate prog s).1 = some (.break k)) ∨
            (∃ k, (evaluate prog s).1 = some (.continue k)) →
          (evaluate prog s).2.localsSize = s.localsSize)) :
    depthPost prog s := by
  intro funs n ns funs2 hyp
  obtain ⟨hmax, hss, hloc⟩ := h hyp.2.2.2.1
  refine ⟨?_, fun _ => ⟨hss, hloc⟩⟩
  rw [hmax]
  exact (optionLe_X_MAX_X _ _).2

end Flapjack.Compiler.Backend.WordDepthProof
