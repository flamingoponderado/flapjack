module

public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Compiler.Backend.ClosNumber
public import Flapjack.Compiler.Backend.ClosKnown.Total
public import Flapjack.Compiler.Backend.ClosTicks.Source
public import Flapjack.Compiler.Backend.ClosLetop.Source
public import Flapjack.Compiler.Backend.ClosAnnotate.Original
public import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants

@[expose] public section

/-! Source preprocessing list and state properties. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Direct-call conversion preserves the number of input expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "LENGTH_FST_calls"]
theorem length_fst_calls (xs : List ClosLang.Exp) (g0 : ClosCall.State) :
    (ClosCall.calls xs g0).1.length = xs.length := by
  exact ClosCall.callsSingList_length xs g0

/-- Ignoring the table preserves it while threading the state and code. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ignore_table_uncurry"]
theorem ignoreTable_uncurry {δ ε α β γ : Type} (f : δ → ε → α × β)
    (st : δ) (p : ε × γ) :
    ClosNumber.ignoreTable f st p = ((f st p.1).1, (f st p.1).2, p.2) := by
  cases p with
  | mk x y =>
    cases h : f st x
    simp [ClosNumber.ignoreTable, h]

private theorem empty_of_length {α β : Type} (xs : List α) (ys : List β)
    (h : ys.length = xs.length) :
    (xs = [] → ys = []) ∧ (xs ≠ [] → ys ≠ []) := by
  cases xs <;> cases ys <;> simp_all

/-- Known-function optimization preserves emptiness of its expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "known_nil"]
theorem known_nil (b : List ClosLang.Exp) (a : ClosKnown.Config)
    (c : List ClosKnown.ValApprox) (d : Spt ClosKnown.ValApprox) :
    (b = [] → (ClosKnown.knownListTotal a b c d).1 = []) ∧
    (b ≠ [] → (ClosKnown.knownListTotal a b c d).1 ≠ []) := by
  exact empty_of_length b _ (ClosKnown.knownListTotal_length a b c d)

/-- Tick removal preserves emptiness of its expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "remove_ticks_nil"]
theorem removeTicks_nil (xs : List ClosLang.Exp) :
    (xs = [] → ClosTicks.removeList xs = []) ∧
    (xs ≠ [] → ClosTicks.removeList xs ≠ []) := by
  exact empty_of_length xs _ (ClosTicks.removeList_length xs)

/-- Let-operation cleanup preserves emptiness of its expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "let_op_nil"]
theorem letOp_nil (xs : List ClosLang.Exp) :
    (xs = [] → ClosLetop.compileList xs = []) ∧
    (xs ≠ [] → ClosLetop.compileList xs ≠ []) := by
  exact empty_of_length xs _ (ClosLetop.compileList_length xs)

/-- Annotation preserves emptiness of its expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "annotate_nil"]
theorem annotate_nil (xs : List ClosLang.Exp) (n : Nat) :
    (xs = [] → ClosAnnotate.annotateSource n xs = []) ∧
    (xs ≠ [] → ClosAnnotate.annotateSource n xs ≠ []) := by
  have length : (ClosAnnotate.annotateSource n xs).length = xs.length := by
    rw [(ClosAnnotate.annotateSource_sing_eq n (.var .none 0) xs).2]
    exact ClosAnnotate.annotateList_length n xs
  exact empty_of_length xs _ length

/-- Call conversion preserves the empty list and its state, and nonemptiness. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "calls_nil"]
theorem calls_nil (xs : List ClosLang.Exp) (p : ClosCall.State) :
    (xs = [] → ClosCall.calls xs p = ([], p)) ∧
    (xs ≠ [] → (ClosCall.calls xs p).1 ≠ []) := by
  constructor
  · intro h
    subst xs
    simp [ClosCall.calls, ClosCall.callsSingList]
  · exact (empty_of_length xs _ (ClosCall.callsSingList_length xs p)).2

/-- Numbering preserves emptiness of its expression list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "renumber_code_locs_list_nil"]
theorem renumberList_nil (xs : List ClosLang.Exp) (n : Nat) :
    (xs = [] → (ClosNumber.renumberList n xs).2 = []) ∧
    (xs ≠ [] → (ClosNumber.renumberList n xs).2 ≠ []) := by
  exact empty_of_length xs _ (ClosNumber.renumberList_length xs n)

/-- Incremental multi-argument introduction preserves empty and nonempty inputs. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "mcompile_inc_nil"]
theorem mcompileInc_nil {α β γ : Type} (p : List ClosLang.Exp × α) (maxApp : Nat) :
    (p.1 = [] → ClosMti.compileInc (Output := β) maxApp p = ([], [])) ∧
    (p.1 ≠ [] → (ClosMti.compileInc (Output := γ) maxApp p).1 ≠ []) := by
  have length := ClosMti.introList_length maxApp p.1
  constructor
  · intro empty
    have h := (empty_of_length p.1 _ length).1 empty
    simp [ClosMti.compileInc, h]
  · exact (empty_of_length p.1 _ length).2

end Flapjack.Compiler.Backend.ClosToBvl
