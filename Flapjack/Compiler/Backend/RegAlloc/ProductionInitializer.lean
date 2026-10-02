import Flapjack.Compiler.Backend.RegAlloc.ProductionInitDomain
import Flapjack.Compiler.Backend.RegAlloc.ProductionInitialSeed

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- The literal input seed supplied by original reg_alloc_aux to run_ira_state:
present Atemp tag slots, empty adjacency rows, zero degree/parent slots and
false move slots. Untagged specialization of the already ported native runner;
this is not a complete port of reg_alloc_aux. -/
def initializerIraSeed (dimension : Nat) : IraState :=
  { adj_ls := (dimension, []), node_tag := (dimension, .Atemp)
    degrees := (dimension, 0), dim := dimension, simp_wl := [], spill_wl := []
    freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := []
    coalesced := (dimension, 0), move_related := (dimension, false), stack := [] }

/-- Complete native state obtained by expanding the actual original runner
seed. Every field is retained, including the original Atemp tag value.
Untagged runner specialization for the executed initializer correspondence. -/
def initializerNativeSeed (dimension : Nat) : State :=
  { adj_ls := List.replicate dimension [], node_tag := List.replicate dimension .Atemp
    degrees := List.replicate dimension 0, dim := dimension
    simp_wl := [], spill_wl := [], freeze_wl := []
    avail_moves_wl := [], unavail_moves_wl := []
    coalesced := List.replicate dimension 0, move_related := List.replicate dimension false
    stack := [] }

/-- Original runner expansion, with no invariant or successful computation
assumption. Untagged concrete input specialization; arbitrary exceptions and
zero dimension are preserved. -/
theorem runInitializerSeed_eq {value exception : Type}
    (computation : Translator.Monadic.MonadBase.M State value exception) (dimension : Nat) :
    runIraState computation (initializerIraSeed dimension) =
      Translator.Monadic.MonadBase.run computation (initializerNativeSeed dimension) := rfl

end Flapjack.RegAlloc
