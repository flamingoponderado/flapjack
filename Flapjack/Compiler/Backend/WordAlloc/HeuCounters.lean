import Flapjack.Misc.Sptree

namespace Flapjack.WordAlloc

/-- Literal five natural counter product, in original source order. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "heu_data"]
abbrev HeuData := Nat × Nat × Nat × Nat × Nat

@[hol "cakeml/compiler/backend/word_allocScript.sml" "add1_lhs_const_def"]
def add1LhsConst (x : Nat) (t : Spt HeuData) : Spt HeuData :=
  match sptLookup x t with
  | none => sptInsert x (1, 0, 0, 0, 0) t
  | some (const, reg, mem, rreg, rmem) =>
      sptInsert x (const + 1, reg, mem, rreg, rmem) t

@[hol "cakeml/compiler/backend/word_allocScript.sml" "add1_lhs_reg_def"]
def add1LhsReg (x : Nat) (t : Spt HeuData) : Spt HeuData :=
  match sptLookup x t with
  | none => sptInsert x (0, 1, 0, 0, 0) t
  | some (const, reg, mem, rreg, rmem) =>
      sptInsert x (const, reg + 1, mem, rreg, rmem) t

@[hol "cakeml/compiler/backend/word_allocScript.sml" "add1_lhs_mem_def"]
def add1LhsMem (x : Nat) (t : Spt HeuData) : Spt HeuData :=
  match sptLookup x t with
  | none => sptInsert x (0, 0, 1, 0, 0) t
  | some (const, reg, mem, rreg, rmem) =>
      sptInsert x (const, reg, mem + 1, rreg, rmem) t

@[hol "cakeml/compiler/backend/word_allocScript.sml" "add1_rhs_reg_def"]
def add1RhsReg (x : Nat) (t : Spt HeuData) : Spt HeuData :=
  match sptLookup x t with
  | none => sptInsert x (0, 0, 0, 1, 0) t
  | some (const, reg, mem, rreg, rmem) =>
      sptInsert x (const, reg, mem, rreg + 1, rmem) t

@[hol "cakeml/compiler/backend/word_allocScript.sml" "add1_rhs_mem_def"]
def add1RhsMem (x : Nat) (t : Spt HeuData) : Spt HeuData :=
  match sptLookup x t with
  | none => sptInsert x (0, 0, 0, 0, 1) t
  | some (const, reg, mem, rreg, rmem) =>
      sptInsert x (const, reg, mem, rreg, rmem + 1) t

end Flapjack.WordAlloc
