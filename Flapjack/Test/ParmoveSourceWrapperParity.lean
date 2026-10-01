import Flapjack.Compiler.Backend.Parmove.SourceMembershipWrapper
import Flapjack.Test.ParmoveFstepParity

namespace Flapjack.Test.ParmoveSourceWrapperParity
open Flapjack.Compiler.Backend.Parmove

/-! The actual scheduler fixtures in parmove_scheduler_probe.out are replayed
by ParmoveFstepParity; these kernel applications check source membership
for arbitrary observed registers in each original parmove input. -/

example (x : Nat) : some x ∈ (parmove ([] : List (Nat × Nat))).map Prod.snd →
    x ∈ ([] : List (Nat × Nat)).map Prod.snd :=
  memMapSndParmove _ x

example (x : Nat) : some x ∈ (parmove ([(1,1)] : List (Nat × Nat))).map Prod.snd →
    x ∈ ([(1,1)] : List (Nat × Nat)).map Prod.snd :=
  memMapSndParmove _ x

example (x : Nat) : some x ∈ (parmove ([(1,2)] : List (Nat × Nat))).map Prod.snd →
    x ∈ ([(1,2)] : List (Nat × Nat)).map Prod.snd :=
  memMapSndParmove _ x

example (x : Nat) : some x ∈ (parmove ([(1,2),(2,3),(3,4)] : List (Nat × Nat))).map Prod.snd →
    x ∈ ([(1,2),(2,3),(3,4)] : List (Nat × Nat)).map Prod.snd :=
  memMapSndParmove _ x

example (x : Nat) : some x ∈ (parmove ([(1,2),(2,1)] : List (Nat × Nat))).map Prod.snd →
    x ∈ ([(1,2),(2,1)] : List (Nat × Nat)).map Prod.snd :=
  memMapSndParmove _ x

example (x : Nat) : some x ∈ (parmove ([(1,2),(2,3),(3,1)] : List (Nat × Nat))).map Prod.snd →
    x ∈ ([(1,2),(2,3),(3,1)] : List (Nat × Nat)).map Prod.snd :=
  memMapSndParmove _ x

example (x : Nat) : some x ∈ (parmove ([(1,2),(1,3)] : List (Nat × Nat))).map Prod.snd →
    x ∈ ([(1,2),(1,3)] : List (Nat × Nat)).map Prod.snd :=
  memMapSndParmove _ x

end Flapjack.Test.ParmoveSourceWrapperParity
