import Flapjack.Compiler.Backend.WordAlloc.ClashTreeProg
import Flapjack.Compiler.Backend.WordAlloc.ProgramWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ColouringOk
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CheckPartialCol
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CheckCol
import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSetDeletion
import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Pancake.WordConvs.WfCutsets

/-!
# `clash_tree_colouring_ok` statement

The statement of `word_allocProofScript.sml:2813-2826` `clash_tree_colouring_ok`
split into its per-program goal, so that the HOL `get_clash_tree_ind` cases can
be stated as genuine cases of the same theorem, and the common `Delta` step of
the statement cases. These are Flapjack infrastructure for the case split; the
tagged assembly states the HOL theorem itself. HOL sets are predicates:
`IMAGE f (domain t)` is `fun y => ∃ x, sptDomain t x ∧ f x = y` and
`INJ f (domain t) UNIV` is injectivity on `sptDomain t`.
-/

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc

/-- HOL `clash_tree_colouring_ok`'s five conclusions (`hide`'d in HOL). -/
def clashTreeConcl {width : Nat} [NeZero width] (f : Nat → Nat)
    (prog : WordLangProgHOL (BitVec width)) (live : NumSet) (lt : List (NumSet × NumSet))
    (livein flivein : NumSet) : Prop :=
  sptWf livein = true ∧
    (∀ a b, sptDomain livein a → sptDomain livein b → f a = f b → a = b) ∧
    colouringOk f prog live lt ∧
    livein = getLive prog live lt ∧
    sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ f x = y)

/-- HOL `clash_tree_colouring_ok` at one program, universally over the remaining
HOL binders `lt f live flive livein flivein` with the six HOL premises. -/
def clashTreeGoal {width : Nat} [NeZero width] (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (lt : List (NumSet × NumSet)) (f : Nat → Nat) (live flive livein flivein : NumSet),
    wfCutsets prog ∧ sptWf live = true ∧
      (∀ p, p ∈ lt → sptWf p.1 = true ∧ sptWf p.2 = true) ∧
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) ∧
      (∀ a b, sptDomain live a → sptDomain live b → f a = f b → a = b) ∧
      checkClashTree f (getClashTree prog lt) live flive = some (livein, flivein) →
    clashTreeConcl f prog live lt livein flivein

/-- The `Delta` step of `check_clash_tree`: the writes are checked against the
incoming live set, then the reads against the live set minus the writes
(HOL `start_tac` with `check_partial_col_INJ`, `domain_numset_list_delete` and
`INJ_IMP_IMAGE_DIFF`). -/
theorem checkDelta (f : Nat → Nat) (w r : List Nat) (live flive livein flivein : NumSet)
    (hw : sptWf live = true)
    (hd : sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y))
    (hi : ∀ a b, sptDomain live a → sptDomain live b → f a = f b → a = b)
    (hc : checkClashTree f (.delta w r) live flive = some (livein, flivein)) :
    (∀ a b, (sptDomain live a ∨ a ∈ w) → (sptDomain live b ∨ b ∈ w) → f a = f b → a = b) ∧
      sptWf livein = true ∧ livein = numsetListInsert r (numsetListDelete w live) ∧
      (∀ a b, sptDomain livein a → sptDomain livein b → f a = f b → a = b) ∧
      sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ f x = y) := by
  unfold checkClashTree at hc
  cases h1 : checkPartialCol f w live flive with
  | none => rw [h1] at hc; cases hc
  | some p1 =>
  obtain ⟨l1, f1⟩ := p1
  rw [h1] at hc
  obtain ⟨-, hl1, hinj1, -⟩ := checkPartialColInj w f live flive l1 f1 hw hd hi h1
  have hinjW : ∀ a b, (sptDomain live a ∨ a ∈ w) → (sptDomain live b ∨ b ∈ w) →
      f a = f b → a = b := by
    intro a b ha hb hab
    refine hinj1 a b ?_ ?_ hab <;> rw [hl1, domainNumsetListInsert]
    · exact ha
    · exact hb
  have hwD : sptWf (numsetListDelete w live) = true := (numsetListDeleteSwap w 0 live hw).1
  have hdD : sptDomain (numsetListDelete (w.map f) flive) =
      (fun y => ∃ x, sptDomain (numsetListDelete w live) x ∧ f x = y) := by
    rw [domainNumsetListDelete, domainNumsetListDelete, hd]
    have himg := injImageDiff f (sptDomain live) (fun k => k ∈ w)
      (fun x y hx hy hxy => hinjW x y hx hy hxy)
    funext y
    apply propext
    show ((∃ x, sptDomain live x ∧ f x = y) ∧ y ∉ w.map f) ↔
      ∃ x, (sptDomain live x ∧ x ∉ w) ∧ f x = y
    have h2 : (∃ x, (sptDomain live x ∧ x ∉ w) ∧ f x = y) ↔
        ((∃ x, sptDomain live x ∧ f x = y) ∧ ¬ ∃ x, x ∈ w ∧ f x = y) := by
      rw [congrFun himg y]
    rw [h2, List.mem_map]
  have hiD : ∀ a b, sptDomain (numsetListDelete w live) a →
      sptDomain (numsetListDelete w live) b → f a = f b → a = b := by
    intro a b ha hb hab
    rw [domainNumsetListDelete] at ha hb
    exact hi a b ha.1 hb.1 hab
  obtain ⟨hw2, hl2, hinj2, hd2⟩ := checkPartialColInj r f (numsetListDelete w live)
    (numsetListDelete (w.map f) flive) livein flivein hwD hdD hiD hc
  exact ⟨hinjW, hw2, hl2, hinj2, hd2⟩

/-- A statement whose clash tree is a single `Delta w r` satisfies the
conclusions once its writes are `w` and its `get_live` is the `Delta` result
(Flapjack infrastructure for the statement cases). -/
theorem deltaConcl {width : Nat} [NeZero width] (prog : WordLangProgHOL (BitVec width))
    (f : Nat → Nat) (w r : List Nat) (live flive livein flivein : NumSet)
    (lt : List (NumSet × NumSet))
    (hw : sptWf live = true)
    (hd : sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y))
    (hi : ∀ a b, sptDomain live a → sptDomain live b → f a = f b → a = b)
    (hc : checkClashTree f (.delta w r) live flive = some (livein, flivein))
    (hW : ∀ k, sptDomain (getWrites prog) k ↔ k ∈ w)
    (hL : sptWf live = true → numsetListInsert r (numsetListDelete w live) = getLive prog live lt)
    (hCO : colouringOk f prog live lt ↔
      ((∀ a b, sptDomain (getLive prog live lt) a → sptDomain (getLive prog live lt) b →
          f a = f b → a = b) ∧
        (∀ a b, sptDomain (sptUnion (getWrites prog) live) a →
          sptDomain (sptUnion (getWrites prog) live) b → f a = f b → a = b))) :
    clashTreeConcl f prog live lt livein flivein := by
  obtain ⟨hinjW, hw2, hl2, hinj2, hd2⟩ := checkDelta f w r live flive livein flivein hw hd hi hc
  have hEq : livein = getLive prog live lt := hl2.trans (hL hw)
  refine ⟨hw2, hinj2, hCO.mpr ⟨?_, ?_⟩, hEq, hd2⟩
  · rw [← hEq]; exact hinj2
  · intro a b ha hb hab
    rw [sptDomain_sptUnion] at ha hb
    refine hinjW a b ?_ ?_ hab
    · rcases ha with ha | ha
      · exact Or.inr ((hW a).mp ha)
      · exact Or.inl ha
    · rcases hb with hb | hb
      · exact Or.inr ((hW b).mp hb)
      · exact Or.inl hb

end Flapjack.WordAlloc
