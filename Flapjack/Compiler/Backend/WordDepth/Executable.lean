import Flapjack.Compiler.Backend.WordDepthProof.Helpers

/-! Exact executable fusion of call-graph construction and maximum-depth
evaluation. Original HOL declarations remain unchanged. The composed Option
result retains missing frames, indirect calls, and recursive-call behavior. -/
namespace Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack Flapjack.Compiler.Backend.WordDepth
open Flapjack.Compiler.Backend.WordDepthProof
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem sptSize_sptMkBN_le {α : Type} (a r : Spt α) :
    sptSize (sptMkBN a r) ≤ sptSize a + sptSize r := by
  cases a <;> cases r <;> simp [sptMkBN, sptSize]

/-- `sptSize` of a `mk_BS`-collapsed triple is bounded by the sum of the two
    children sizes plus one.  Untagged Flapjack infrastructure used only for
    the `callGraph` termination measure. -/
private theorem sptSize_sptMkBS_le {α : Type} (a r : Spt α) (v : α) :
    sptSize (sptMkBS a v r) ≤ sptSize a + sptSize r + 1 := by
  cases a <;> cases r <;> simp [sptMkBS, sptSize]

/-- Deleting a present key strictly decreases the spt size.  This untagged
    Flapjack termination lemma proves the strict inequality needed by the
    `callGraph` measure on the local tree implementation; it is not presented
    as a port of a HOL declaration. -/
private theorem sptSize_sptDelete_lt {α : Type} (t : Spt α) (k : Nat) (v : α)
    (h : sptLookup k t = some v) : sptSize (sptDelete k t) < sptSize t := by
  induction t generalizing k v with
  | ln => simp at h
  | ls x =>
      by_cases hk : k = 0
      · subst hk; simp [sptDelete, sptSize]
      · simp [sptLookup, hk] at h
  | bn l r ihl ihr =>
      by_cases hk : k = 0
      · simp [sptLookup, hk] at h
      · simp only [sptLookup, hk, if_false] at h
        by_cases he : k % 2 = 0
        · simp only [he, if_true] at h
          rw [sptDelete]
          simp only [hk, if_false, he, if_true]
          calc
            sptSize (sptMkBN (sptDelete ((k - 1) / 2) l) r)
                ≤ sptSize (sptDelete ((k - 1) / 2) l) + sptSize r :=
                  sptSize_sptMkBN_le _ _
            _ < sptSize l + sptSize r := by
                  have := ihl ((k - 1) / 2) v h; omega
        · simp only [he, if_false] at h
          rw [sptDelete]
          simp only [hk, if_false, he, if_false]
          calc
            sptSize (sptMkBN l (sptDelete ((k - 1) / 2) r))
                ≤ sptSize l + sptSize (sptDelete ((k - 1) / 2) r) :=
                  sptSize_sptMkBN_le _ _
            _ < sptSize l + sptSize r := by
                  have := ihr ((k - 1) / 2) v h; omega
  | bs l x r ihl ihr =>
      by_cases hk : k = 0
      · subst hk
        simp only [sptLookup, if_true] at h
        rw [sptDelete]
        simp only [if_true]
        simp [sptSize]
      · simp only [sptLookup, hk, if_false] at h
        by_cases he : k % 2 = 0
        · simp only [he, if_true] at h
          rw [sptDelete]
          simp only [hk, if_false, he, if_true]
          calc
            sptSize (sptMkBS (sptDelete ((k - 1) / 2) l) x r)
                ≤ sptSize (sptDelete ((k - 1) / 2) l) + sptSize r + 1 :=
                  sptSize_sptMkBS_le _ _ _
            _ < sptSize l + sptSize r + 1 := by
                  have := ihl ((k - 1) / 2) v h; omega
        · simp only [he, if_false] at h
          rw [sptDelete]
          simp only [hk, if_false, he, if_false]
          calc
            sptSize (sptMkBS l x (sptDelete ((k - 1) / 2) r))
                ≤ sptSize l + sptSize (sptDelete ((k - 1) / 2) r) + 1 :=
                  sptSize_sptMkBS_le _ _ _
            _ < sptSize l + sptSize r + 1 := by
                  have := ihr ((k - 1) / 2) v h; omega


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
