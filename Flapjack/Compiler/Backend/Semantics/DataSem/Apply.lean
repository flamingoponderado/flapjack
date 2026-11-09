module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Conversions
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
public import Flapjack.Compiler.Backend.Semantics.DataSem.Stack
public import Flapjack.Misc.Sptree.FromList

@[expose] public section

/-! Data-language installation and the full primitive entry point. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical

/-- Install the next oracle program only when both decoded buffers, their
explicit lengths, and the compiler's next configuration agree. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_install_def"]
noncomputable def doInstall {C F R : Type} (args : List Value) (s : State C F) :
    Result (Value × State C F) R :=
  let fail : Result (Value × State C F) R := .err (.abort .typeError)
  match args with
  | [v1, v2, len1, len2] =>
    match valueToBytes v1, valueToWords v2 with
    | some bytes, some data =>
      if len1 ≠ .number (Int.ofNat bytes.length) ∨ len2 ≠ .number (Int.ofNat data.length) then fail else
        let (config, programs) := s.compileOracle 0
        let nextOracle := fun n => s.compileOracle (n + 1)
        match s.compile config programs, programs with
        | some (bytes', data', config'), (label, _) :: _ =>
          if bytes = bytes' ∧ data = data' ∧ (nextOracle 0).1 = config' then
            let newCode := sptUnion s.code (sptFromAList programs)
            .val (.codePtr label, { s with safeForSpace := false, code := newCode, compileOracle := nextOracle })
          else fail
        | _, _ => fail
    | _, _ => fail
  | _ => fail

/-- Apply the installation, heap-space, stack-space, and representation
checks in their original order. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_app_def"]
noncomputable def doApp {C F : Type} (op : ClosLang.Op) (values : List Value) (s : State C F) :
    Result (Value × State C F) Value :=
  let fail : Result (Value × State C F) Value := .err (.abort .typeError)
  match op with
  | .install => doInstall values { s with stackMax := none, stackFrameSizes := .ln }
  | .intOp .greater | .intOp .greaterEq => fail
  | _ => match doSpace op values s with
    | none => fail
    | some next => doAppAux op values (doStack op values (doLimSafe next op values))

end Flapjack.Compiler.Backend.DataSem
