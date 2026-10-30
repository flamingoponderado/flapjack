import Flapjack.Compiler.Backend.Semantics.BvlSem.State
import Flapjack.Misc.ListEl

/-! BVL code lookup for direct and indirect calls. -/
namespace Flapjack.Compiler.Backend.BvlSem

private instance : Nonempty Value := ⟨.number 0⟩

/-- Resolve a direct label or the code pointer at the end of an indirect
call's argument list, checking the original arity convention. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "find_code_def"]
noncomputable def findCode {α : Type} (dest : Option Nat) (args : List Value) (code : Spt (Nat × α)) :
    Option (List Value × α) :=
  match dest with
  | some loc =>
    match sptLookup loc code with
    | none => none
    | some (arity, exp) => if args.length = arity then some (args, exp) else none
  | none =>
    if args.isEmpty then none else
      match Flapjack.holLast args with
      | .codePtr loc =>
        match sptLookup loc code with
        | none => none
        | some (arity, exp) => if args.length = arity + 1 then some (args.dropLast, exp) else none
      | _ => none

end Flapjack.Compiler.Backend.BvlSem
