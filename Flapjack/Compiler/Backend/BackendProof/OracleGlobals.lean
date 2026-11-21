module

public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
public import Flapjack.Compiler.Backend.BackendProps.Pure
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.CompileSafety
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.CompileGlobals
public import Flapjack.Compiler.Backend.ClosInterp.Proofs.Globals
public import Flapjack.Misc.Bag

@[expose] public section

/-! backendProofScript.sml 714-733: `oracle_monotonic_globals_flat_to_clos`,
transporting oracle monotonicity of the global variables assigned by the
flat-language oracle across the flat-to-closure translation. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Backend.BackendProps

/-- Flapjack helper: a successor of a present flat global is in the image. -/
private theorem succ_mem_image (b : Bag Nat) (k : Nat) (h : 1 ≤ b k) :
    k + 1 ∈ Set.image Nat.succ (setOfBag b) := ⟨k, h, rfl⟩

/-- Exact HOL `oracle_monotonic_globals_flat_to_clos`
(`backendProofScript.sml:714-733`). HOL `no_Mat_decs` is the Bool-valued
reviewed `noMatDecs`, `SET_OF_BAG` is `setOfBag`, `IMAGE SUC` is
`Set.image Nat.succ`, `x INSERT s` is `insert x s` and `$<` is `(· < ·)`. The
oracle configuration type `α` and the closure auxiliary type `β` are
independent, as captured. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "oracle_monotonic_globals_flat_to_clos"]
theorem oracleMonotonic_globals_flatToClos {α β : Type} (p : List FlatLang.Exp)
    (orac : Nat → α × List FlatLang.Exp) :
    FlatProps.noMatDecs p = true ∧ (∀ n, FlatProps.noMatDecs (orac n).2 = true) ∧
      oracleMonotonic (Set.image Nat.succ ∘ setOfBag ∘ FlatProps.elistGlobals ∘ Prod.snd)
        (· < ·) (insert 0 (Set.image Nat.succ (setOfBag (FlatProps.elistGlobals p)))) orac →
      oracleMonotonic (setOfBag ∘ ClosProps.elistGlobals ∘ Prod.fst ∘ Prod.snd) (· < ·)
        (setOfBag (ClosProps.elistGlobals (FlatToClos.compileProg p)))
        (pureCo (FlatToClos.incCompileDecs (α := β)) ∘ orac) := by
  intro ⟨hp, horac, hmono⟩
  refine oracleMonotonic_subset _ _ _ _ _ _ _ ⟨?_, ?_⟩ hmono
  · intro x hx
    change 1 ≤ ClosProps.elistGlobals (FlatToClos.compileProg p) x at hx
    rw [FlatToClos.compileProg_setGlobals p hp] at hx
    simp only [FlatProps.unionGlobalBag, Flapjack.bagUnion, FlatToClos.shiftGlobalBag] at hx
    cases x with
    | zero => exact Set.mem_insert 0 _
    | succ k =>
        apply Set.mem_insert_of_mem
        apply succ_mem_image
        simpa using hx
  · intro n x hx
    change 1 ≤ ClosProps.elistGlobals
      (pureCo (FlatToClos.incCompileDecs (α := β)) (orac n)).2.1 x at hx
    have e : (pureCo (FlatToClos.incCompileDecs (α := β)) (orac n)).2.1 =
        ClosInterp.insertInterp (FlatToClos.compileDecs (orac n).2 ++
          FlatToClos.compileDecs [FlatLang.Exp.con BackendCommon.Tra.none none []]) := rfl
    rw [e, ClosInterp.elistGlobals_insertInterp, ClosProps.elistGlobals_append,
      FlatToClos.compileDecs_setGlobals _ (horac n),
      FlatToClos.compileDecs_setGlobals [FlatLang.Exp.con BackendCommon.Tra.none none []]
        (by simp [FlatProps.noMatDecs, FlatProps.noMat, FlatProps.noMatList])]
      at hx
    simp [FlatProps.unionGlobalBag, Flapjack.bagUnion,
      FlatToClos.shiftGlobalBag, FlatProps.elistGlobals, FlatProps.setGlobals,
      FlatProps.emptyGlobalBag, Flapjack.emptyBag] at hx
    cases x with
    | zero => simp at hx
    | succ k =>
        apply succ_mem_image
        simpa using hx

end Flapjack.Compiler.Backend.BackendProof
