import Flapjack.Compiler.Backend.PresLang.Clos
import Flapjack.Compiler.Backend.DataLang.Syntax

/-! Data-language explorer display corresponding to `data_seqs_def`,
`data_prog_to_display_def`, `data_fun_to_display_def` and `data_to_strs_def`
in `cakeml/compiler/backend/presLangScript.sml`. This is untagged because
the shared display tree uses Lean strings rather than HOL `mlstring`; byte
encoding correspondence and explorer wiring remain open. -/
namespace Flapjack.Compiler.Backend.PresLang.Data
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def item (name : String) (xs : List DisplayExpr) : DisplayExpr := .item none name xs
private def number (n : Nat) : DisplayExpr := .string (toString n)
private def nums (ns : List Nat) : DisplayExpr := .tuple (ns.map number)
private def optional (f : α → DisplayExpr) : Option α → DisplayExpr
  | none => .string "none"
  | some x => item "some" [f x]

/-- Print the keys of a sparse live set in ascending numeric order. -/
def liveSet (s : NumSet) : DisplayExpr :=
  let keys := ((sptToAList s).map Prod.fst).mergeSort (· ≤ ·)
  .string ("{" ++ String.intercalate "," (keys.map toString) ++ "}")

/-- Flatten nested sequences in source order, using an accumulator so that
deeply nested programs do not require repeated list concatenation. -/
def seqs (p : DataLang.Prog) (tail : List DataLang.Prog) : List DataLang.Prog :=
  match p with
  | .seq a b => seqs a (seqs b tail)
  | _ => p :: tail

private def returns (r : List Nat × NumSet) : DisplayExpr := .tuple [nums r.1, liveSet r.2]
private def forceReturn (r : Nat × NumSet) : DisplayExpr := .tuple [number r.1, liveSet r.2]

mutual
/-- Render a DataLang program with the original depth/list fuel behavior. -/
def program : Nat → Spt MlString → DataLang.Prog → DisplayExpr
  | 0, _, _ => .string "..."
  | fuel + 1, names, p => match p with
    | .skip => .string "skip"
    | .move x y => .tuple [number x, .string ":=", number y]
    | .call r dest args handler => item "call" [optional returns r,
        .string (Clos.attachName names dest), nums args,
        match handler with
        | none => .string "none"
        | some (v, body) => item "some" [.tuple [number v, program fuel names body]]]
    | .force ret loc src => item "force" [optional forceReturn ret, number loc, number src]
    | .assign n op args live => .tuple [number n, .string ":=", Clos.op names op, nums args, optional liveSet live]
    | .seq a b => .list (.string "seq" :: programs fuel names (seqs a (seqs b [])))
    | .ifThenElse n a b => item "if" [number n, program fuel names a, program fuel names b]
    | .makeSpace n live => item "make_space" [number n, liveSet live]
    | .raise n => item "raise" [number n]
    | .return ns => item "return" [nums ns]
    | .tick => .string "tick"

private def programs : Nat → Spt MlString → List DataLang.Prog → List DisplayExpr
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, names, p :: ps => program fuel names p :: programs fuel names ps
end

/-- Render DataLang functions using the original one-billion-step display fuel. -/
def functions (names : Spt MlString) (fs : List (Nat × Nat × DataLang.Prog)) : List String :=
  mapAppendDisplayStrings (fun (n, arity, body) =>
    displayStrTreeToStrings "\n\n" (displayToStrTree (.tuple [
      .string "func", .string (Clos.attachName names (some n)),
      nums (List.range arity), program 1000000000 names body]))) fs

/-- Encode byte-valued display text without UTF-8 expansion. -/
def functionBytes (names : Spt MlString) (fs : List (Nat × Nat × DataLang.Prog)) : List HolChar :=
  (functions names fs).flatMap fun fragment => fragment.toList.map (fun c => BitVec.ofNat 8 c.toNat)

end Flapjack.Compiler.Backend.PresLang.Data
