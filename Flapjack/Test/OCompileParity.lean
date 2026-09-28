import Flapjack.Pancake.CrepToLoop.Optimise

/-! Direct parity for `crep_to_loop$ocompile` (`crep_to_loopScript.sml:216`).
The expected shapes are copied from `scripts/hol-probes/ocompile_probe.out`;
the return case intentionally checks the right-associated `nested_seq` shape,
including the trailing `Skip` retained by CakeML's optimizer. -/

namespace Flapjack.Test.OCompileParity

def sourceContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

def ffiSourceContext : LoopContext Nat :=
  { vars := [(1, 5), (2, 6), (3, 7), (4, 8)], functions := [], maxVar := 4,
    target := .rv64i }

def parityGuard : Bool :=
  (match oCompile sourceContext [] (.skip : CrepProg Nat) with
  | .mark .skip => true
  | _ => false) &&
  (match oCompile sourceContext []
      (.assign 1 (.const 17) : CrepProg Nat) with
  | .mark (.seq (.mark .skip) (.mark .skip)) => true
  | _ => false) &&
  (match oCompile sourceContext []
      (.return [.const 17] : CrepProg Nat) with
  | .mark
      (.seq (.mark (.assign 1 (.const 17)))
        (.mark (.seq (.mark (.return [1])) (.mark .skip)))) => true
  | _ => false) &&
  (match oCompile ffiSourceContext []
      (.extCall "f" 1 2 3 4 : CrepProg Nat) with
  | .mark (.ffi "f" 5 6 7 8 []) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.OCompileParity
