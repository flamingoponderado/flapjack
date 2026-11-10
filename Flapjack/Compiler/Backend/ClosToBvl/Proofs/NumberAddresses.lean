module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationDistinct
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationParity
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IncrementalAddresses
import Mathlib.Data.List.Nodup

@[expose] public section

/-! Required addresses after closure-location numbering. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

private theorem extracted_marker (n : Nat) (ys : List ClosLang.Exp) :
    extractedAddrs (.op .none (.intOp (.const (Int.ofNat n))) [] :: ys) =
      (List.range (max 1 ys.length)).map (n + ·) := by
  cases ys with
  | nil => simp [extractedAddrs, extractNameSource_eq_extractName, extractName]
  | cons a as => simp [extractedAddrs, extractNameSource_eq_extractName, extractName]

private theorem numbered_req {α : Type} (n : Nat) (es : List ClosLang.Exp) :
    (reqCompileIncAddrs [Nat.succ]
      ((ClosNumber.compileInc n es).2, ([] : List (Nat × α × ClosLang.Exp)))).Nodup := by
  let reserve := max 1 es.length
  let aligned := makeEven (n + reserve)
  cases hr : ClosNumber.renumberList aligned es with
  | mk finish ys =>
    have len := ClosNumber.renumberList_imp_length aligned es finish ys hr
    have locs := ClosNumber.renumberList_codeLocations_distinct aligned es
    simp only [hr] at locs
    have even := ClosNumber.renumberCodeLocs_even.1 aligned es (even_makeEven (n + reserve))
    simp only [hr] at even
    have alignBound : n + reserve ≤ aligned := by
      simp only [aligned, makeEven]
      split <;> omega
    let first := (List.range reserve).map (n + ·)
    let rest := codeLocations ys
    have firstNodup : first.Nodup := by
      apply (List.nodup_map_iff (fun _ _ h => Nat.add_left_cancel h)).mpr
      exact List.nodup_range
    have nextNodup : (rest.map Nat.succ).Nodup :=
      (List.nodup_map_iff (fun _ _ h => Nat.succ.inj h)).mpr locs.1
    have firstBound : ∀ x ∈ first, x < aligned := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hi := List.mem_range.mp hi
      omega
    have noFirstRest : first.Disjoint rest := by
      apply List.disjoint_left.mpr
      intro x hx hy
      have a := firstBound x hx
      have b := locs.2.1 x hy
      omega
    have noFirstNext : first.Disjoint (rest.map Nat.succ) := by
      apply List.disjoint_left.mpr
      intro x hx hmap
      obtain ⟨y, ymem, rfl⟩ := List.mem_map.mp hmap
      have a := firstBound y.succ hx
      have b := locs.2.1 y ymem
      omega
    have noRestNext : rest.Disjoint (rest.map Nat.succ) := by
      apply List.disjoint_left.mpr
      intro x hx hmap
      obtain ⟨y, ymem, rfl⟩ := List.mem_map.mp hmap
      have ex := even.2 y.succ hx
      have ey := even.2 y ymem
      omega
    have all := (firstNodup.append locs.1 noFirstRest).append nextNodup
      (List.disjoint_append_left.mpr ⟨noFirstNext, noRestNext⟩)
    have hr' : ClosNumber.renumberList (makeEven (n + max es.length 1)) es = (finish, ys) := by
      simpa [aligned, reserve, Nat.max_comm] using hr
    simp only [ClosNumber.compileInc, hr', reqCompileIncAddrs,
      List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons,
      List.append_nil, codeLocations, codeLocationsExp]
    rw [extracted_marker]
    simpa [len, reserve, first, rest, List.append_assoc] using all

/-- Numbering an incremental program with empty auxiliary code yields distinct
required addresses, empty auxiliary code and an extractable entry marker. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "number_compile_inc_req"]
theorem numberCompileInc_req {α : Type} (n : Nat)
    (prog : List ClosLang.Exp × List (Nat × α × ClosLang.Exp)) :
    let nprog := (ClosNumber.ignoreTable ClosNumber.compileInc n prog).2
    prog.2 = [] →
      (reqCompileIncAddrs [Nat.succ] nprog).Nodup ∧
      nprog.2 = [] ∧ canExtract nprog.1 := by
  obtain ⟨es, code⟩ := prog
  dsimp only
  intro empty
  subst code
  simp only [ClosNumber.ignoreTable]
  constructor
  · exact numbered_req n es
  · constructor
    · trivial
    · simp only [ClosNumber.compileInc]
      exact ⟨.none, n, (ClosNumber.renumberList
        (makeEven (n + max es.length 1)) es).2, rfl⟩
/-- Every required numbered address lies between the input and output counters. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "MEM_number_req"]
theorem mem_number_req {α : Type} (x n : Nat)
    (prog : List ClosLang.Exp × List (Nat × α × ClosLang.Exp))
    (h : x ∈ reqCompileIncAddrs [Nat.succ]
      (ClosNumber.ignoreTable ClosNumber.compileInc n prog).2 ∧ prog.2 = []) :
    n ≤ x ∧ x < (ClosNumber.compileInc n prog.1).1 := by
  obtain ⟨es, code⟩ := prog
  obtain ⟨member, empty⟩ := h
  simp only at empty
  subst code
  let reserve := max 1 es.length
  let aligned := makeEven (n + reserve)
  cases hr : ClosNumber.renumberList aligned es with
  | mk finish ys =>
    have hr' : ClosNumber.renumberList (makeEven (n + max es.length 1)) es = (finish, ys) := by
      simpa [aligned, reserve, Nat.max_comm] using hr
    have len := ClosNumber.renumberList_imp_length aligned es finish ys hr
    have locs := ClosNumber.renumberList_codeLocations_distinct aligned es
    simp only [hr] at locs
    have even := ClosNumber.renumberCodeLocs_even.1 aligned es (even_makeEven (n + reserve))
    simp only [hr] at even
    have alignBound : n + reserve ≤ aligned := by
      simp only [aligned, makeEven]
      split <;> omega
    have nextBound := ClosNumber.renumberList_start_le es aligned
    simp only [hr] at nextBound
    simp only [ClosNumber.ignoreTable, ClosNumber.compileInc, hr', reqCompileIncAddrs,
      List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons, List.append_nil,
      codeLocations, codeLocationsExp, List.mem_append] at member ⊢
    rw [extracted_marker] at member
    simp only [len, List.mem_map, List.mem_range, List.not_mem_nil, false_or,
      List.nil_append] at member
    rcases member with (⟨i, hi, rfl⟩ | hx) | ⟨i, hi, rfl⟩
    · change i < reserve at hi
      omega
    · have low := locs.2.1 x hx
      have high := locs.2.2 x hx
      omega
    · have low := locs.2.1 i hi
      have high := locs.2.2 i hi
      have ei := even.2 i hi
      have ef := even.1
      omega
end Flapjack.Compiler.Backend.ClosToBvl
