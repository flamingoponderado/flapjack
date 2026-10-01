import Flapjack.Compiler.Backend.Parmove.DestinationWrapper

namespace Flapjack.Test.ParmoveDestinationWrapperParity
open Flapjack.Compiler.Backend.Parmove

example : (parmove ([] : List (Nat × Nat))).map Prod.fst = [] := by cbv
example : (parmove [((1 : Nat),1)]).map Prod.fst = [] := by cbv
example : (parmove [((1 : Nat),2),(2,3)]).map Prod.fst = [some 1,some 2] := by cbv
example : (parmove [((1 : Nat),2),(2,1)]).map Prod.fst = [none,some 2,some 1] := by cbv
example : (parmove [((1 : Nat),2),(1,3)]).map Prod.fst = [some 1,some 1] := by cbv
example : (parmove [((9 : Nat),7),(2,3),(8,6)]).map Prod.fst = [some 9,some 2,some 8] := by cbv
example : (parmove [((none : Option Nat),some 2),(some 1,none)]).map Prod.fst =
    [some (some 1),some none] := by cbv

-- Apply the source's one-way statement to every same-input observation.
example (x : Nat) : some x ∈ (parmove ([] : List (Nat × Nat))).map Prod.fst →
    x ∈ ([] : List (Nat × Nat)).map Prod.fst := memMapFstParmove [] x
example (x : Nat) : some x ∈ (parmove [((1 : Nat),1)]).map Prod.fst →
    x ∈ [((1 : Nat),1)].map Prod.fst := memMapFstParmove _ x
example (x : Nat) : some x ∈ (parmove [((1 : Nat),2),(2,3)]).map Prod.fst →
    x ∈ [((1 : Nat),2),(2,3)].map Prod.fst := memMapFstParmove _ x
example (x : Nat) : some x ∈ (parmove [((1 : Nat),2),(2,1)]).map Prod.fst →
    x ∈ [((1 : Nat),2),(2,1)].map Prod.fst := memMapFstParmove _ x
example (x : Nat) : some x ∈ (parmove [((1 : Nat),2),(1,3)]).map Prod.fst →
    x ∈ [((1 : Nat),2),(1,3)].map Prod.fst := memMapFstParmove _ x
example (x : Nat) : some x ∈ (parmove [((9 : Nat),7),(2,3),(8,6)]).map Prod.fst →
    x ∈ [((9 : Nat),7),(2,3),(8,6)].map Prod.fst := memMapFstParmove _ x
example (x : Option Nat) : some x ∈
    (parmove [((none : Option Nat),some 2),(some 1,none)]).map Prod.fst →
    x ∈ [((none : Option Nat),some 2),(some 1,none)].map Prod.fst := memMapFstParmove _ x

end Flapjack.Test.ParmoveDestinationWrapperParity
