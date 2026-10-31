import Flapjack.Compiler.Backend.ClosConstant.Proofs.Hash

/-! Correspondence of recursive constant flattening implementations. -/
namespace Flapjack.Compiler.Backend.ClosConstant.Proofs
open Flapjack.Compiler.Backend.ClosLang Flapjack.Compiler.Backend.ClosToBvl

mutual
/-- Hash-consed flattening of a constant agrees with the association-list model. -/
theorem addParts_related (constant : Const) (index : Nat) (tree : Spt (List (ConstPart × Nat)))
    (aux : List (ConstPart × Nat)) (good : goodHashTable tree aux) :
    let (n1, r1, tree1, acc1) := addParts constant index tree (aux.map (updateTag ∘ Prod.fst))
    let (n2, r2, aux2) := parts constant index aux
    n1 = n2 ∧ r1 = r2 ∧ aux2.map (updateTag ∘ Prod.fst) = acc1 ∧ goodHashTable tree1 aux2 := by
  cases constant with
  | constInt n => exact addPart_related index (.int n) tree aux good
  | constStr text => exact addPart_related index (.str text) tree aux good
  | constWord64 word => exact addPart_related index (.w64 word) tree aux good
  | constCons tag constants =>
    cases targetRun : addPartsList constants index tree (aux.map (updateTag ∘ Prod.fst)) with
    | mk targetIndex targetTail =>
      cases targetTail with
      | mk targetIndices targetTail =>
        cases targetTail with
        | mk targetTree targetAcc =>
          cases sourceRun : partsList constants index aux with
          | mk sourceIndex sourceTail =>
            cases sourceTail with
            | mk sourceIndices sourceAux =>
              have relation := addPartsList_related constants index tree aux good
              rw [targetRun, sourceRun] at relation
              obtain ⟨indexEq, indicesEq, accEq, nextGood⟩ := relation
              subst targetIndex
              subst targetIndices
              have final := addPart_related sourceIndex (.con tag sourceIndices) targetTree sourceAux nextGood
              simp only [addParts, parts, targetRun, sourceRun]
              rw [← accEq]
              exact final

/-- Hash-consed flattening of a constant list agrees with the source model. -/
theorem addPartsList_related (constants : List Const) (index : Nat) (tree : Spt (List (ConstPart × Nat)))
    (aux : List (ConstPart × Nat)) (good : goodHashTable tree aux) :
    let (n1, rs1, tree1, acc1) := addPartsList constants index tree (aux.map (updateTag ∘ Prod.fst))
    let (n2, rs2, aux2) := partsList constants index aux
    n1 = n2 ∧ rs1 = rs2 ∧ aux2.map (updateTag ∘ Prod.fst) = acc1 ∧ goodHashTable tree1 aux2 := by
  cases constants with
  | nil => exact ⟨rfl, rfl, rfl, good⟩
  | cons constant rest =>
    cases targetFirst : addParts constant index tree (aux.map (updateTag ∘ Prod.fst)) with
    | mk targetIndex targetTail =>
      cases targetTail with
      | mk targetFound targetTail =>
        cases targetTail with
        | mk targetTree targetAcc =>
          cases sourceFirst : parts constant index aux with
          | mk sourceIndex sourceTail =>
            cases sourceTail with
            | mk sourceFound sourceAux =>
              have firstRel := addParts_related constant index tree aux good
              rw [targetFirst, sourceFirst] at firstRel
              obtain ⟨indexEq, foundEq, accEq, nextGood⟩ := firstRel
              subst targetIndex
              subst targetFound
              have restRel := addPartsList_related rest sourceIndex targetTree sourceAux nextGood
              simp only [addPartsList, partsList, targetFirst, sourceFirst]
              rw [← accEq]
              cases targetRest : addPartsList rest sourceIndex targetTree (sourceAux.map (updateTag ∘ Prod.fst)) with
              | mk targetLast targetRestTail =>
                cases targetRestTail with
                | mk targetIndices targetRestTail =>
                  cases targetRestTail with
                  | mk finalTree finalAcc =>
                    cases sourceRest : partsList rest sourceIndex sourceAux with
                    | mk sourceLast sourceRestTail =>
                      cases sourceRestTail with
                      | mk sourceIndices finalAux =>
                        rw [targetRest, sourceRest] at restRel
                        obtain ⟨lastEq, indicesEq, finalAccEq, finalGood⟩ := restRel
                        exact ⟨lastEq, by simp [indicesEq], finalAccEq, finalGood⟩
end

/-- Recursive hash-consing agrees with the association-list flattening model
for both constants and constant lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "add_parts_thm"]
theorem addParts_thm :
    (∀ constant index tree acc n1 r1 tree1 acc1 aux n2 r2 aux1,
      addParts constant index tree acc = (n1, r1, tree1, acc1) ∧
      parts constant index aux = (n2, r2, aux1) ∧
      aux.map (updateTag ∘ Prod.fst) = acc ∧ goodHashTable tree aux →
      n1 = n2 ∧ r1 = r2 ∧ aux1.map (updateTag ∘ Prod.fst) = acc1 ∧ goodHashTable tree1 aux1) ∧
    (∀ constants index tree acc n1 rs1 tree1 acc1 aux n2 rs2 aux1,
      addPartsList constants index tree acc = (n1, rs1, tree1, acc1) ∧
      partsList constants index aux = (n2, rs2, aux1) ∧
      aux.map (updateTag ∘ Prod.fst) = acc ∧ goodHashTable tree aux →
      n1 = n2 ∧ rs1 = rs2 ∧ aux1.map (updateTag ∘ Prod.fst) = acc1 ∧ goodHashTable tree1 aux1) := by
  constructor
  · intro constant index tree acc n1 r1 tree1 acc1 aux n2 r2 aux1 ⟨targetRun, sourceRun, accEq, good⟩
    subst acc
    have result := addParts_related constant index tree aux good
    rw [targetRun, sourceRun] at result
    exact result
  · intro constants index tree acc n1 rs1 tree1 acc1 aux n2 rs2 aux1 ⟨targetRun, sourceRun, accEq, good⟩
    subst acc
    have result := addPartsList_related constants index tree aux good
    rw [targetRun, sourceRun] at result
    exact result

/-- Except for the two special direct-code cases, constant compilation builds
the tag-shifted parts produced by the source model. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "compile_const_thm"]
theorem compileConst_thm (constant : Const)
    (prereqs : (∀ n, constant ≠ .constInt n) ∧ (∀ tag, constant ≠ .constCons tag [])) :
    compileConst constant = .blockOp (.build ((toParts constant).map updateTag)) := by
  obtain ⟨notInt, notEmpty⟩ := prereqs
  cases constant with
  | constInt n => exact False.elim (notInt n rfl)
  | constStr text => rfl
  | constWord64 word => rfl
  | constCons tag constants =>
    cases constants with
    | nil => exact False.elim (notEmpty tag rfl)
    | cons first rest =>
      have good : goodHashTable .ln [] := by
        intro key value
        simp [lookupPart, sptLookup]
      cases targetRun : addPartsList (first :: rest) 0 .ln [] with
      | mk targetIndex targetTail =>
        cases targetTail with
        | mk targetIndices targetTail =>
          cases targetTail with
          | mk targetTree targetAcc =>
            cases sourceRun : partsList (first :: rest) 0 [] with
            | mk sourceIndex sourceTail =>
              cases sourceTail with
              | mk sourceIndices sourceAux =>
                have relation := addPartsList_related (first :: rest) 0 .ln [] good
                simp only [List.map_nil] at relation
                rw [targetRun, sourceRun] at relation
                simp only at relation
                obtain ⟨_, indicesEq, accEq, _⟩ := relation
                simp only [compileConst, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, targetRun,
                  toParts, sourceRun, List.map_reverse, List.map_cons, updateTag, List.map_map]
                simp [← accEq, indicesEq, Function.comp_def]

end Flapjack.Compiler.Backend.ClosConstant.Proofs
