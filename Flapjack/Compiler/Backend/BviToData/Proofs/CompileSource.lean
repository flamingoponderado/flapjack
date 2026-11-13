module

public import Flapjack.Compiler.Backend.BviToData.CompileSourceAgrees
public import Flapjack.Compiler.Backend.BviToData.Proofs.CompileAgreement
public import Mathlib.Tactic

@[expose] public section

/-! Structural properties of the original list-shaped BVI compiler. -/
namespace Flapjack.Compiler.Backend.BviToData
open Classical

/-- Compiling a labeled function preserves its label and arity. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_part_thm"]
theorem compilePart_fn :
    compilePart = (fun (x, y) => (x, (fun (a, b) => (a, compileExp a b)) y)) := by
  funext part
  rcases part with ⟨x, a, b⟩
  rfl

/-- The source compiler assigns one result name per input expression. This
is the equality form used to establish the original `compile_LENGTH` result. -/
theorem compileSource_length (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat) (xs : List Bvi.Exp) :
    (compileSource n env tail live xs).2.1.length = xs.length := by
  fun_induction compileSource n env tail live xs <;> simp_all

/-- A successful source compiler result has exactly one name per expression. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_LENGTH"]
theorem compileSource_LENGTH (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat)
    (xs : List Bvi.Exp) (code : DataLang.Prog) (names : List Nat) (next : Nat)
    (compiled : compileSource n env tail live xs = (code, names, next)) : names.length = xs.length := by
  simpa [compiled] using compileSource_length n env tail live xs

/-- The source compiler never decreases its fresh-name counter. -/
theorem compileSource_counter (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat) (xs : List Bvi.Exp) :
    n ≤ (compileSource n env tail live xs).2.2 := by
  fun_induction compileSource n env tail live xs <;> simp_all <;> omega

/-- The original implication form of fresh-name counter monotonicity. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_LESS_EQ"]
theorem compileSource_LESS_EQ (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat)
    (xs : List Bvi.Exp) (code : DataLang.Prog) (names : List Nat) (next : Nat)
    (compiled : compileSource n env tail live xs = (code, names, next)) : n ≤ next := by
  simpa [compiled] using compileSource_counter n env tail live xs

/-- Every result name produced by the source compiler is below its returned
fresh-name counter. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_RANGE_lemma"]
theorem compileSource_range (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat) (xs : List Bvi.Exp) :
    ∀ v ∈ (compileSource n env tail live xs).2.1, v < (compileSource n env tail live xs).2.2 := by
  fun_induction compileSource n env tail live xs <;> (simp_all [Flapjack.holHd]; try omega)
  case case2 n env tail live x y xs c1 vs1 n1 h1 c2 vs2 n2 h2 ih1 ih2 =>
    have len := compileSource_length n env false live [x]
    rw [h1] at len
    have counter := compileSource_counter n1 env false (Flapjack.holHd vs1 :: live) (y :: xs)
    simp only [Flapjack.holHd] at counter
    rw [h2] at counter
    cases vs1 with
    | nil => simp at len
    | cons v rest =>
      simp at counter ⊢
      have bound := ih1 v (by simp)
      omega

/-- Result names of a compilation are below its returned fresh counter. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_RANGE"]
theorem compileSource_RANGE (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat)
    (xs : List Bvi.Exp) (code : DataLang.Prog) (names : List Nat) (next : Nat)
    (compiled : compileSource n env tail live xs = (code, names, next)) :
    ∀ v ∈ names, v < next := by
  simpa [compiled] using compileSource_range n env tail live xs

/-- The original source theorem relating singleton compilation and the
non-tail list rewrite. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_sing_eq"]
theorem compileSing_source_eq :
    (∀ n env tail live x code name next,
      compileSing n env tail live x = (code, name, next) →
      compileSource n env tail live [x] = (code, [name], next)) ∧
    (∀ n env live xs, compileList n env live xs = compileSource n env false live xs) := by
  constructor
  · intro n env tail live x code name next compiled
    simpa [compiled] using compileSource_agrees n env tail live [x]
  · intro n env live xs
    have agrees := (compileSource_agrees n env false live xs).symm
    cases xs with
    | nil => simpa [compileList] using agrees
    | cons x rest =>
      cases rest with
      | nil => simpa [compileList] using agrees
      | cons y ys => simpa using agrees

end Flapjack.Compiler.Backend.BviToData
