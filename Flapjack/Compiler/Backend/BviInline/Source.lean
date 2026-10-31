import Flapjack.Compiler.Backend.BviInline

/-! Total source-shaped BVI inline pass traversals. -/
namespace Flapjack.Compiler.Backend.BviInline
open Bvi

mutual
/-- Flapjack infrastructure: total tick removal following the source
constructor clauses. This remains untagged until the HOL carriers and the
executed traversal have been reviewed against this definition. -/
def removeTicksSource : Exp → Exp
  | .var n => .var n
  | .ifThenElse x y z => .ifThenElse (removeTicksSource x) (removeTicksSource y) (removeTicksSource z)
  | .let xs body => .let (removeTicksListSource xs) (removeTicksSource body)
  | .raise body => .raise (removeTicksSource body)
  | .tick body => removeTicksSource body
  | .call _ target args handler =>
      .call 0 target (removeTicksListSource args)
        (match handler with | none => none | some body => some (removeTicksSource body))
  | .force location index => .force location index
  | .op op args => .op op (removeTicksListSource args)
  | .letCall rets _ target args body => .letCall rets 0 target (removeTicksListSource args) (removeTicksSource body)
  | .return args => .return (removeTicksListSource args)
termination_by e => sizeOf e

/-- Flapjack infrastructure: source-shaped list traversal for tick removal. -/
def removeTicksListSource : List Exp → List Exp
  | [] => []
  | e :: rest => removeTicksSource e :: removeTicksListSource rest
termination_by es => sizeOf es
end

end Flapjack.Compiler.Backend.BviInline
