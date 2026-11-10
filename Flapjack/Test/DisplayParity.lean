module

public import Flapjack.Display

-- Checks below run compiled code from these modules.
public meta import Flapjack.Display
@[expose] public section

namespace Flapjack.Test.DisplayParity

open Flapjack

/-! Direct oracle guards for `pan_passesScript.sml:112-181`:
`opsize_to_display_def`, `insert_es_def`, `varkind_to_str_def`,
`primop_to_display_def`, and `dest_annot_def`. -/

def varKindOracle : Bool :=
  varKindToDisplayString .global == "global" &&
    varKindToDisplayString .local == "local"

def destAnnotOracle : Bool :=
  destAnnot (.annot "tag" "text" : Prog Nat) == some ("tag", "text") &&
    destAnnot (.skip : Prog Nat) == none

/-! Direct oracle guards for `loop_prog_to_display_def` and its handler
    equation in `pan_passesScript.sml:549-631`. -/

#guard varKindOracle
#guard destAnnotOracle
end Flapjack.Test.DisplayParity
