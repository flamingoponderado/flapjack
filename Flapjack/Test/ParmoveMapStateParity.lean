import Flapjack.Compiler.Backend.Parmove.MapState
namespace Flapjack.Test.ParmoveMapStateParity
open Flapjack.Compiler.Backend.Parmove
example : mapState (fun x => x + 1 : Nat → Nat) ([],[],[]) = ([],[],[]) := by decide
example : mapState (fun x => x + 1 : Nat → Nat) ([(1,2)],[],[]) = ([(2,3)],[],[]) := by decide
example : mapState (fun x => x + 1 : Nat → Nat) ([],[(3,4)],[]) = ([],[(4,5)],[]) := by decide
example : mapState (fun x => x + 1 : Nat → Nat) ([],[],[(5,6)]) = ([],[],[(6,7)]) := by decide
example : mapState (fun x => x + 1 : Nat → Nat) ([(1,2),(3,4)],[(5,6)],[(7,8),(9,10)]) = ([(2,3),(4,5)],[(6,7)],[(8,9),(10,11)]) := by decide
example : mapState (fun _ => 0 : Nat → Nat) ([(1,2)],[(3,4)],[(5,6)]) = ([(0,0)],[(0,0)],[(0,0)]) := by decide
example : mapState (fun x => x + 1 : Nat → Nat) ([(18446744073709551616,18446744073709551617)],[],[]) = ([(18446744073709551617,18446744073709551618)],[],[]) := by decide
example : mapState (fun x => !x : Bool → Bool) ([(true,false)],[(false,false)],[(true,true)]) = ([(false,true)],[(true,true)],[(false,false)]) := by decide
example : mapState (fun x => x == 0 : Nat → Bool) ([(0,1)],[(2,0)],[(0,0)]) = ([(true,false)],[(false,true)],[(true,true)]) := by decide
example : mapState (fun _ => some 7 : Option Nat → Option Nat) ([(none,some 1)],[],[(some 2,none)]) = ([(some 7,some 7)],[],[(some 7,some 7)]) := by decide
end Flapjack.Test.ParmoveMapStateParity
