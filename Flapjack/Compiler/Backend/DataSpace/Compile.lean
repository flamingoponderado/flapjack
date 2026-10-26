import Flapjack.Compiler.Backend.DataSpace.Requirements

/-! Move and combine allocation-space reservations. -/
namespace Flapjack.Compiler.Backend.DataSpace
open DataLang

/-- Reinsert a deferred allocation-space reservation. -/
@[hol "cakeml/compiler/backend/data_spaceScript.sml" "pMakeSpace_def"]
def pMakeSpace : Sum Prog (Nat × NumSet × Prog) → Prog
  | .inl c => c
  | .inr (k, names, c) => .seq (.makeSpace k names) c

/-- Hoist allocation-space reservations while updating their live-name sets. -/
@[hol "cakeml/compiler/backend/data_spaceScript.sml" "space_def"]
def space : Prog → Sum Prog (Nat × NumSet × Prog)
  | .makeSpace k names => .inr (k, names, .skip)
  | .seq c1 c2 =>
      let d1 := pMakeSpace (space c1)
      let x2 := space c2
      match x2 with
      | .inl c4 =>
          match c1 with
          | .makeSpace k names => .inr (k, names, c4)
          | .skip => .inl c4
          | _ => .inl (.seq d1 c4)
      | .inr (k, names, c4) =>
          match c1 with
          | .skip => .inr (k, names, c4)
          | .makeSpace _ names1 => .inr (k, sptInter names1 names, c4)
          | .move dst src =>
              .inr (k, sptInsert src () (sptDelete dst names), .seq (.move dst src) c4)
          | .assign dst op args none =>
              .inr (opSpaceReq op args.length + k, sptListInsert args (sptDelete dst names),
                .seq (.assign dst op args none) c4)
          | _ => .inl (.seq d1 (pMakeSpace x2))
  | .ifThenElse n x y => .inl (.ifThenElse n (pMakeSpace (space x)) (pMakeSpace (space y)))
  | c => .inl c

/-- Apply the reservation pass and restore any leading deferred reservation. -/
@[hol "cakeml/compiler/backend/data_spaceScript.sml" "compile_def"]
def compile (c : Prog) : Prog := pMakeSpace (space c)

end Flapjack.Compiler.Backend.DataSpace
