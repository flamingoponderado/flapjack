module

public import Flapjack.Compiler.Backend.ClosToBvl.Constants
public import Flapjack.Compiler.Backend.ClosLang.CodeLabels
public import Flapjack.Misc.Option
public import Flapjack.Compiler.Backend.ClosToBvl.Layout
public import Flapjack.Compiler.Backend.Semantics.BvlProps.CodeLabels
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Code-label properties of closure-to-BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang

/-- Compiling a primitive operator preserves exactly its label, when present. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "assign_get_code_label_compile_op"]
theorem assignGetCodeLabel_compileOp (op : Op) :
    assignGetCodeLabel (compileOp op) =
      match Flapjack.holOptionSome (fun n : Nat => op = .label n) with
      | some n => {n}
      | none => ∅ := by
  classical
  by_cases h : ∃ n : Nat, op = .label n
  · obtain ⟨n, rfl⟩ := h
    have selected : Flapjack.holOptionSome (fun k : Nat => Op.label n = .label k) = some n := by
      apply (Flapjack.holOptionSome_eq_some_iff _ ?_ _).2
      · rfl
      · intro a b ha hb
        simpa using ha.symm.trans hb
    rw [selected]
    rfl
  · have absent : Flapjack.holOptionSome (fun n : Nat => op = .label n) = none := by
      simp [Flapjack.holOptionSome, h]
    rw [absent]
    cases op <;> try rfl
    case label n => exact (h ⟨n, rfl⟩).elim
    case blockOp b =>
      cases b <;> try rfl
      case constant c =>
        cases c <;> try rfl
        case constCons t cs =>
          simp only [compileOp, compileConst]
          split <;> rfl
    case globOp g => cases g <;> rfl
    case memOp m => cases m <;> rfl

/-- Recursive closure setup references its generated labels and the labels
already present in the continuation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "recc_Lets_code_labels"]
theorem reccLets_codeLabels (n : Nat) (nargs : List Nat) (k : Nat) (rest : Bvl.Exp) :
    BvlProps.getCodeLabels (reccLetsHOL n nargs k rest) =
      (fun j => n + 2 * j) '' Set.Iio k ∪ BvlProps.getCodeLabels rest := by
  have reccLabel (loc arity index : Nat) :
      BvlProps.getCodeLabels (reccLet loc arity index) = {loc} := by
    change BvlProps.getCodeLabels
      (.let [.op (.blockOp (.elemAt 2)) [.var 0]]
        (.let [.op (.blockOp (.cons 30)) [.var 0, mkConst (arity - 1), mkLabel loc]]
          (.let [.op (.memOp .update) [.var 0, mkConst index, .var 1]] (.var 1)))) = {loc}
    simp [BvlProps.getCodeLabels, BvlProps.getCodeLabelsList, mkConst, mkLabel, assignGetCodeLabel]
  induction k generalizing nargs rest with
  | zero =>
    ext x
    simp [reccLetsHOL]
  | succ k ih =>
    rw [reccLetsHOL, BvlProps.getCodeLabels, BvlProps.getCodeLabelsList, ih]
    simp only [reccLabel, BvlProps.getCodeLabelsList, Set.union_empty]
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩ | h)
      · exact Or.inl ⟨k, by omega, rfl⟩
      · exact Or.inl ⟨j, by omega, rfl⟩
      · exact Or.inr h
    · rintro (⟨j, hj, rfl⟩ | h)
      · by_cases eq : j = k
        · subst j; exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨j, by omega, rfl⟩)
      · exact Or.inr (Or.inr h)

/-- Each generated auxiliary entry comes from the input list or the original
accumulator. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "MEM_build_aux_imp_SND_MEM"]
theorem mem_buildAux_imp_snd_mem (n : Nat) (ls : List (Nat × Bvl.Exp))
    (acc : List (Nat × Nat × Bvl.Exp)) (m : Nat) (aux : List (Nat × Nat × Bvl.Exp))
    (x : Nat × Nat × Bvl.Exp) (h : buildAux n ls acc = (m, aux) ∧ x ∈ aux) :
    x.2 ∈ ls ∨ x ∈ acc := by
  induction ls generalizing n acc with
  | nil =>
    simp only [buildAux, Prod.mk.injEq] at h
    rcases h with ⟨⟨_, rfl⟩, member⟩
    exact Or.inr member
  | cons entry rest ih =>
    obtain ⟨arity, body⟩ := entry
    simp only [buildAux] at h
    rcases ih (n + 2) ((n, arity, body) :: acc) h with member | member
    · exact Or.inl (List.mem_cons_of_mem _ member)
    · simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Or.inl (by simp)
      · exact Or.inr member

end Flapjack.Compiler.Backend.ClosToBvl
