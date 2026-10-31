import Flapjack.Compiler.Backend.ClosConstant.Proofs.Build
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic

/-! Naive constant flattening and reconstruction from the HOL proof. -/
namespace Flapjack.Compiler.Backend.ClosConstant.Proofs
open Flapjack.Compiler.Backend.ClosLang Flapjack.Compiler.Backend.ClosSem
open Flapjack.Compiler.Backend.BackendCommon

private def lookupPart (part : ConstPart) : List (ConstPart × Nat) → Option Nat
  | [] => none
  | (other, index) :: rest => if part = other then some index else lookupPart part rest

/-- Assign an index to a part, reusing its previous index when present. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "make_part_def"]
def makePart (index : Nat) (part : ConstPart) (aux : List (ConstPart × Nat)) :
    Nat × Nat × List (ConstPart × Nat) :=
  match lookupPart part aux with
  | some old => (index, old, aux)
  | none => (index + 1, index, (part, index) :: aux)

mutual
/-- Flatten a constant using a part association list. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "parts_def"]
def parts (constant : Const) (index : Nat) (aux : List (ConstPart × Nat)) :
    Nat × Nat × List (ConstPart × Nat) :=
  match constant with
  | .constInt n => makePart index (.int n) aux
  | .constWord64 w => makePart index (.w64 w) aux
  | .constStr text => makePart index (.str text) aux
  | .constCons tag cs =>
    let (next, indices, aux) := partsList cs index aux
    makePart next (.con tag indices) aux

/-- Flatten a list of constants in source order. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "parts_def"]
def partsList (constants : List Const) (index : Nat) (aux : List (ConstPart × Nat)) :
    Nat × List Nat × List (ConstPart × Nat) :=
  match constants with
  | [] => (index, [], aux)
  | constant :: rest =>
    let (next, found, aux) := parts constant index aux
    let (last, foundRest, aux) := partsList rest next aux
    (last, found :: foundRest, aux)
end

/-- Flatten a constant to a dependency-ordered part sequence. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "to_parts_def"]
def toParts : Const → List ConstPart
  | .constInt n => [.int n]
  | .constStr text => [.str text]
  | .constWord64 w => [.w64 w]
  | .constCons tag cs =>
    let (_, indices, aux) := partsList cs 0 []
    (.con tag indices :: aux.map Prod.fst).reverse

private theorem makePart_suffix (index : Nat) (part : ConstPart) (aux : List (ConstPart × Nat)) :
    ∃ added, (makePart index part aux).2.2 = added ++ aux := by
  unfold makePart
  split
  · exact ⟨[], rfl⟩
  · exact ⟨[(part, index)], rfl⟩

mutual
/-- Flattening one constant only prepends to the existing part accumulator. -/
theorem parts_suffix (constant : Const) (index : Nat) (aux : List (ConstPart × Nat)) :
    ∃ added, (parts constant index aux).2.2 = added ++ aux := by
  cases constant with
  | constInt n => exact makePart_suffix index (.int n) aux
  | constStr text => exact makePart_suffix index (.str text) aux
  | constWord64 w => exact makePart_suffix index (.w64 w) aux
  | constCons tag constants =>
    cases result : partsList constants index aux with
    | mk next pair =>
      cases pair with
      | mk indices nextAux =>
        obtain ⟨firstPrefix, firstEq⟩ := partsList_suffix constants index aux
        rw [result] at firstEq
        simp only at firstEq
        obtain ⟨secondPrefix, secondEq⟩ := makePart_suffix next (.con tag indices) nextAux
        refine ⟨secondPrefix ++ firstPrefix, ?_⟩
        simp only [parts, result]
        rw [secondEq, firstEq, List.append_assoc]

/-- Flattening a list of constants only prepends to the accumulator. -/
theorem partsList_suffix (constants : List Const) (index : Nat) (aux : List (ConstPart × Nat)) :
    ∃ added, (partsList constants index aux).2.2 = added ++ aux := by
  cases constants with
  | nil => exact ⟨[], rfl⟩
  | cons constant rest =>
    cases first : parts constant index aux with
    | mk next pair =>
      cases pair with
      | mk found nextAux =>
        cases second : partsList rest next nextAux with
        | mk last pair =>
          cases pair with
          | mk indices lastAux =>
            obtain ⟨firstPrefix, firstEq⟩ := parts_suffix constant index aux
            rw [first] at firstEq
            simp only at firstEq
            obtain ⟨secondPrefix, secondEq⟩ := partsList_suffix rest next nextAux
            rw [second] at secondEq
            simp only at secondEq
            refine ⟨secondPrefix ++ firstPrefix, ?_⟩
            simp only [partsList, first, second]
            rw [secondEq, firstEq, List.append_assoc]
end

/-- Both flattening functions preserve the suffix of their input accumulator. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "parts_acc"]
theorem parts_acc :
    (∀ c n aux m r res, parts c n aux = (m, r, res) → ∃ added, res = added ++ aux) ∧
    (∀ cs n aux m rs res, partsList cs n aux = (m, rs, res) → ∃ added, res = added ++ aux) := by
  constructor
  · intro c n aux m r res run
    obtain ⟨added, eq⟩ := parts_suffix c n aux
    rw [run] at eq
    exact ⟨added, eq⟩
  · intro cs n aux m rs res run
    obtain ⟨added, eq⟩ := partsList_suffix cs n aux
    rw [run] at eq
    exact ⟨added, eq⟩

/-- Interpret a constant part as a constant tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_part_def"]
def buildPartSyntax (memory : Nat → Const) : ConstPart → Const
  | .int n => .constInt n
  | .str text => .constStr text
  | .w64 w => .constWord64 w
  | .con tag indices => .constCons tag (indices.map memory)

/-- Build a constant tree from a sequence of parts. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_def"]
def buildSyntax (memory : Nat → Const) (index : Nat) : List ConstPart → Const
  | [] => memory (index - 1)
  | part :: rest =>
    buildSyntax (fun key => if key = index then buildPartSyntax memory part else memory key) (index + 1) rest

/-- Build from parts with the initial zero-constant memory. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_const_def"]
def buildConstSyntax (parts : List ConstPart) : Const :=
  buildSyntax (fun _ => .constInt 0) 0 parts

/-- Evaluating the syntax-level builder commutes with evaluating each stored
constant. This generalizes the final reconstruction step in the HOL proof. -/
theorem makeConst_buildSyntax (parts : List ConstPart) (memory : Nat → Const) (index : Nat) :
    makeConst (buildSyntax memory index parts) = build (fun key => makeConst (memory key)) index parts := by
  induction parts generalizing memory index with
  | nil => rfl
  | cons part rest ih =>
    simp only [buildSyntax, build]
    rw [ih]
    congr 1
    funext key
    split
    · cases part <;> simp [buildPartSyntax, buildPart, makeConst, List.map_map]
    · rfl

/-- Building and evaluating a syntax constant agrees with building values
directly, for every part sequence. -/
theorem makeConst_buildConstSyntax (parts : List ConstPart) :
    makeConst (buildConstSyntax parts) = buildConst parts := by
  simpa [buildConstSyntax, buildConst, makeConst] using
    makeConst_buildSyntax parts (fun _ => .constInt 0) 0

/-- Shifting constructor tags does not merge distinct parts. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "update_tag_11"]
theorem updateTag_eq_iff (x y : ConstPart) : updateTag x = updateTag y ↔ x = y := by
  have shiftInjective : Function.Injective closTagShift := by
    intro a b equal
    simp only [closTagShift] at equal
    split at equal <;> split at equal <;> omega
  cases x <;> cases y <;> simp [updateTag, shiftInjective.eq_iff]

/-- Memory produced after building a sequence of syntax parts. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_map_def"]
def buildMap (memory : Nat → Const) (index : Nat) : List ConstPart → Nat → Const
  | [] => memory
  | part :: rest =>
    buildMap (fun key => if key = index then buildPartSyntax memory part else memory key) (index + 1) rest

/-- Building two sequences is equivalent to building the first and then the second. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_map_APPEND"]
theorem buildMap_append (xs ys : List ConstPart) (memory : Nat → Const) (index : Nat) :
    buildMap memory index (xs ++ ys) = buildMap (buildMap memory index xs) (index + xs.length) ys := by
  induction xs generalizing memory index with
  | nil => simp [buildMap]
  | cons part rest ih => simp [buildMap, ih, Nat.add_comm, Nat.add_left_comm]

/-- Building parts leaves all earlier indices untouched. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_map_ignore"]
theorem buildMap_ignore (xs : List ConstPart) (memory : Nat → Const) (index key : Nat)
    (earlier : key < index) : buildMap memory index xs key = memory key := by
  induction xs generalizing memory index with
  | nil => rfl
  | cons part rest ih =>
    simp only [buildMap]
    rw [ih _ (index + 1) (by omega)]
    simp [show key ≠ index by omega]

/-- Split a final part from the earlier memory-building sequence. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_mem_thm"]
theorem buildSyntax_append_one (memory : Nat → Const) (index : Nat) (xs : List ConstPart) (last : ConstPart) :
    buildSyntax memory index (xs ++ [last]) =
      buildSyntax (buildMap memory index xs) (index + xs.length) [last] := by
  induction xs generalizing memory index with
  | nil => simp [buildMap]
  | cons part rest ih => simp [buildSyntax, buildMap, ih, Nat.add_comm, Nat.add_left_comm]

end Flapjack.Compiler.Backend.ClosConstant.Proofs
