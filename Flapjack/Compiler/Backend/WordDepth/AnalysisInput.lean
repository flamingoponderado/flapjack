import Flapjack.Compiler.Backend.WordDepth.Executable
import Flapjack.Misc.Sptree.Map

/-! Exact analysis-only input compression. Instructions ignored by callGraph
are discarded from this separate input, while the executed backend retains the
original Word program. No HOL declaration is replaced or independently tagged. -/
namespace Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack Flapjack.Compiler.Backend.WordDepth
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def slimSeq {α : Type} (p q : WordLangProgHOL α) : WordLangProgHOL α :=
  match p, q with
  | .skip, p => p
  | p, .skip => p
  | p, q => .seq p q

/-- Remove only data ignored by callGraph, and collapse its Leaf-valued branches. -/
def slim {α : Type} : WordLangProgHOL α → WordLangProgHOL α
  | .seq p q => slimSeq (slim p) (slim q)
  | .ite _ _ _ p q => slimSeq (slim p) (slim q)
  | .call returns target _arguments handler =>
      .call (match returns with | none => none | some (a,b,p,c,d) => some (a,b,slim p,c,d))
        target [] (match handler with | none => none | some (a,p,b,c) => some (a,slim p,b,c))
  | .mustTerminate p => slim p
  | .loop _ p _ => slim p
  | .alloc a b => .alloc a b
  | .install a b c d e => .install a b c d e
  | _ => .skip
termination_by p => sizeOf p

private theorem slim_call {α : Type}
    (returns : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL α × Nat × Nat))
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL α × Nat × Nat)) :
    slim (.call returns target arguments handler) =
      .call (returns.map fun (a,b,p,c,d) => (a,b,slim p,c,d))
        target [] (handler.map fun (a,p,b,c) => (a,slim p,b,c)) := by
  rw [slim.eq_def]
  cases returns <;> cases handler <;> rfl

private def slimDecl {α : Type} (entry : Nat × WordLangProgHOL α) :=
  (entry.1, slim entry.2)

private theorem map_mkBN {α β : Type} (f : α → β) (l r : Spt α) :
    sptMap f (sptMkBN l r) = sptMkBN (sptMap f l) (sptMap f r) := by
  cases l <;> cases r <;> rfl

private theorem map_mkBS {α β : Type} (f : α → β) (l r : Spt α) (v : α) :
    sptMap f (sptMkBS l v r) = sptMkBS (sptMap f l) (f v) (sptMap f r) := by
  cases l <;> cases r <;> rfl

private theorem delete_map {α β : Type} (f : α → β) (tree : Spt α) (key : Nat) :
    sptDelete key (sptMap f tree) = sptMap f (sptDelete key tree) := by
  induction tree generalizing key with
  | ln => rfl
  | ls value => simp only [sptMap, sptDelete]; split <;> rfl
  | bn l r ihl ihr =>
      simp only [sptMap, sptDelete]
      split
      · rfl
      · split <;> simp only [map_mkBN, ihl, ihr]
  | bs l value r ihl ihr =>
      simp only [sptMap, sptDelete]
      split
      · rfl
      · split <;> simp only [map_mkBS, ihl, ihr]

private theorem size_map {α β : Type} (f : α → β) (tree : Spt α) :
    sptSize (sptMap f tree) = sptSize tree := by
  induction tree <;> simp_all [sptMap, sptSize]

private theorem mkBranch_leaf_left (tree : CallTree) : mkBranch .leaf tree = tree := by
  by_cases same : tree = .leaf <;> simp [mkBranch, same, eq_comm]

private theorem mkBranch_leaf_right (tree : CallTree) : mkBranch tree .leaf = tree := by
  by_cases same : tree = .leaf <;> simp [mkBranch, same]

private theorem graph_slimSeq {width : Nat} [NeZero width]
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) (n : Nat) (ns : List Nat)
    (total : Nat) (p q : WordLangProgHOL (BitVec width)) :
    callGraph funs n ns total (slimSeq p q) =
      mkBranch (callGraph funs n ns total p) (callGraph funs n ns total q) := by
  unfold slimSeq
  split <;> simp [callGraph, mkBranch_leaf_left, mkBranch_leaf_right]

/-- The complete original call tree is preserved, not just a projected bound.
Payload-only Spt mapping preserves raw constructor shape and all deleted keys. -/
theorem callGraph_slim_eq {width : Nat} [NeZero width]
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) (n : Nat) (ns : List Nat)
    (total : Nat) (program : WordLangProgHOL (BitVec width)) :
    callGraph (sptMap slimDecl funs) n ns total (slim program) =
      callGraph funs n ns total program := by
  fun_induction callGraph funs n ns total program <;>
    try simp_all +zetaDelta [slim_call, slim, graph_slimSeq, callGraph, delete_map]
  all_goals
    split <;> simp_all +zetaDelta [sptLookup_sptMap, slimDecl]
  all_goals
    split <;> simp_all +zetaDelta [sptLookup_sptMap]

/-- Payload-only analysis input map, preserving raw tree constructors and keys. -/
def slimCode {width : Nat} (funs : Spt (Nat × WordLangProgHOL (BitVec width))) :=
  sptMap slimDecl funs

theorem fullCallGraph_slim_eq {width : Nat} [NeZero width] (n : Nat)
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) :
    fullCallGraph n (slimCode funs) = fullCallGraph n funs := by
  unfold slimCode fullCallGraph
  rw [sptLookup_sptMap]
  cases lookup : sptLookup n funs with
  | none => rfl
  | some entry =>
      obtain ⟨arity, program⟩ := entry
      simp only [Option.map_some, slimDecl, size_map, callGraph_slim_eq]

/-- Fast exact full-program stack-bound analysis. The compiler backend continues
to consume the original Word program, rather than this separate analysis map. -/
def fullCallGraphDepthExecutable {width : Nat} [NeZero width] (sizes : Spt Nat) (n : Nat)
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) : Option Nat :=
  fullCallGraphDepth sizes n (slimCode funs)

theorem fullCallGraphDepthExecutable_eq {width : Nat} [NeZero width] (sizes : Spt Nat)
    (n : Nat) (funs : Spt (Nat × WordLangProgHOL (BitVec width))) :
    fullCallGraphDepthExecutable sizes n funs = maxDepth sizes (fullCallGraph n funs) := by
  unfold fullCallGraphDepthExecutable
  rw [fullCallGraphDepth_eq, fullCallGraph_slim_eq]

end Flapjack.Compiler.Backend.WordDepth.Executable
