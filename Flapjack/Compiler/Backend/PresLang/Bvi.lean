import Flapjack.Compiler.Backend.PresLang.Bvl
import Flapjack.Compiler.Backend.Bvi.Syntax

/-! BVI explorer display following `bvi_to_display_def`,
`bvi_fun_to_display_def`, and `bvi_to_strs_def` in `presLangScript.sml`.
It remains untagged because the display tree uses Lean strings in place of
HOL `mlstring`; byte encoding correspondence and explorer wiring remain open. -/
namespace Flapjack.Compiler.Backend.PresLang.Bvi
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def item (name : String) (xs : List DisplayExpr) : DisplayExpr := .item none name xs
private def varDisplay (n : Nat) : DisplayExpr := .string (Clos.varName n)

mutual
/-- Render BVI expressions, including handlers and multi-result calls. -/
def expression (names : Spt MlString) (height : Nat) : Bvi.Exp → DisplayExpr
  | .var n => item "var" [varDisplay (height - n - 1)]
  | .ifThenElse a b c => item "if" [expression names height a, expression names height b, expression names height c]
  | .let es e => .list (.string "let" :: (bindings names height (es.length - 1) es ++ [expression names (height + es.length) e]))
  | .raise e => item "raise" [expression names height e]
  | .tick e => item "tick" [expression names height e]
  | .call _ dest es handler => item "call" (.string (Clos.attachName names dest) ::
      (es.map (expression names height) ++ match handler with
       | none => []
       | some e => [item "handler" [varDisplay height, .string "->", expression names (height + 1) e]]))
  | .force loc n => item "force" [varDisplay (height - n - 1), .string (Clos.attachName names (some loc))]
  | .op o es => item "op" (Clos.op names o :: es.map (expression names height))
  | .return es => item "return" (es.map (expression names height))
  | .letCall rets _ dest es body => .list [.string "letcall",
      item "call" (.string (Clos.attachName names (some dest)) :: es.map (expression names height)),
      .tuple ((List.range rets).reverse.map (fun i => varDisplay (height + i))),
      expression names (height + rets) body]
termination_by e => sizeOf e

private def bindings (names : Spt MlString) (height index : Nat) : List Bvi.Exp → List DisplayExpr
  | [] => []
  | e :: es => .tuple [varDisplay (height + index), .string "<-", expression names height e] ::
      bindings names height (index - 1) es
termination_by es => sizeOf es
end

/-- Render BVI functions in input order using the original label table. -/
def programs (names : Spt MlString) (functions : List (Nat × Nat × Bvi.Exp)) : List String :=
  mapAppendDisplayStrings (fun (n, arity, body) =>
    displayStrTreeToStrings "\n\n" (displayToStrTree (.tuple [
      .string "func", .string (Clos.attachName names (some n)),
      .tuple ((List.range arity).reverse.map varDisplay), expression names arity body]))) functions

/-- Encode the byte-valued display text without UTF-8 expansion. -/
def programBytes (names : Spt MlString) (functions : List (Nat × Nat × Bvi.Exp)) : List HolChar :=
  (programs names functions).flatMap fun fragment => fragment.toList.map (fun c => BitVec.ofNat 8 c.toNat)

end Flapjack.Compiler.Backend.PresLang.Bvi
