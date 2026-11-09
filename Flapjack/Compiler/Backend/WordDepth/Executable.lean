module

public import Flapjack.Compiler.Backend.WordDepthProof.Helpers

@[expose] public section

/-! Exact executable fusion of call-graph construction and maximum-depth
evaluation. Original HOL declarations remain unchanged. The composed Option
result retains missing frames, indirect calls, and recursive-call behavior. -/
namespace Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack Flapjack.Compiler.Backend.WordDepth
open Flapjack.Compiler.Backend.WordDepthProof
set_option maxRecDepth 10000
set_option maxHeartbeats 0


private def frame (sizes : Spt Nat) (n : Nat) (depth : Option Nat) : Option Nat :=
  optionMap₂ (· + ·) (sptLookup n sizes) depth

/-- Compute the original call graph's depth directly, without constructing and
comparing intermediate CallTree values. No input validity premise is required. -/
def callGraphDepth {width : Nat} [NeZero width] (sizes : Spt Nat) :
    Spt (Nat × WordLangProgHOL (BitVec width)) → Nat → List Nat → Nat →
      WordLangProgHOL (BitVec width) → Option Nat
  | funs, n, ns, total, .seq p1 p2 =>
      optionMap₂ max (callGraphDepth sizes funs n ns total p1)
        (callGraphDepth sizes funs n ns total p2)
  | funs, n, ns, total, .ite _ _ _ p1 p2 =>
      optionMap₂ max (callGraphDepth sizes funs n ns total p1)
        (callGraphDepth sizes funs n ns total p2)
  | funs, n, ns, total, .call ret dest _args handler =>
      match dest with
      | none => none
      | some d =>
          if d ∈ ns ∧ ret = none then some 0
          else
            match _lookup : sptLookup d funs with
            | none => none
            | some (_, body) =>
                match ret with
                | none =>
                    if ns.length < total then
                      optionMap₂ max (frame sizes d (some 0))
                        (callGraphDepth sizes funs d (d :: ns) total body)
                    else some 0
                | some (_, _, retProg, _, _) =>
                    let newFuns := sptDelete d funs
                    match handler with
                    | none =>
                        optionMap₂ max (frame sizes n (frame sizes d (some 0)))
                          (optionMap₂ max
                            (frame sizes n (callGraphDepth sizes newFuns d [d] total body))
                            (callGraphDepth sizes funs n ns total retProg))
                    | some (_, p, _, _) =>
                        optionMap₂ max
                          (frame sizes n ((frame sizes d (some 0)).map (fun depth => 3 + depth)))
                          (optionMap₂ max
                            (frame sizes n ((callGraphDepth sizes newFuns d [d] total body).map
                              (fun depth => 3 + depth)))
                            (optionMap₂ max (callGraphDepth sizes funs n ns total p)
                              (callGraphDepth sizes funs n ns total retProg)))
  | funs, n, ns, total, .mustTerminate p => callGraphDepth sizes funs n ns total p
  | _, n, _, _, .alloc _ _ => frame sizes n (some 0)
  | _, _, _, _, .install _ _ _ _ _ => none
  | funs, n, ns, total, .loop _ body _ => callGraphDepth sizes funs n ns total body
  | _, _, _, _, _ => some 0
termination_by funs _ ns total p => (sptSize funs, total - ns.length, sizeOf p)
decreasing_by
  all_goals
    first
      | apply Prod.Lex.left
        exact sptSize_sptDelete_lt _ _ _ _lookup
      | apply Prod.Lex.right
        apply Prod.Lex.left
        simp only [List.length_cons]; omega
      | apply Prod.Lex.right
        apply Prod.Lex.right
        decreasing_trivial

theorem callGraphDepth_eq {width : Nat} [NeZero width] (sizes : Spt Nat)
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) (n : Nat)
    (ns : List Nat) (total : Nat) (program : WordLangProgHOL (BitVec width)) :
    maxDepth sizes (callGraph funs n ns total program) =
      callGraphDepth sizes funs n ns total program := by
  fun_induction callGraphDepth sizes funs n ns total program <;>
    simp_all [callGraph, maxDepth_mkBranch, maxDepth, frame]
  all_goals
    split <;> simp_all +zetaDelta [maxDepth_mkBranch, maxDepth]
  all_goals
    split <;> simp_all +zetaDelta [maxDepth_mkBranch, maxDepth] <;> omega

/-- Exact maximum depth of the original full call graph, computed by fusion. -/
def fullCallGraphDepth {width : Nat} [NeZero width] (sizes : Spt Nat) (n : Nat)
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) : Option Nat :=
  match sptLookup n funs with
  | none => none
  | some (_, program) =>
      optionMap₂ max (frame sizes n (some 0))
        (callGraphDepth sizes funs n [n] (sptSize funs) program)

/-- Unconditional whole Option result equality, including malformed maps,
missing frames, indirect calls and original cycle handling. -/
theorem fullCallGraphDepth_eq {width : Nat} [NeZero width] (sizes : Spt Nat) (n : Nat)
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) :
    fullCallGraphDepth sizes n funs = maxDepth sizes (fullCallGraph n funs) := by
  unfold fullCallGraphDepth fullCallGraph
  split <;> simp_all [maxDepth, frame, callGraphDepth_eq]

end Flapjack.Compiler.Backend.WordDepth.Executable
