import Flapjack.Compiler.Backend.LabToTarget.NopInsertEncoding
namespace Flapjack.Test.LabToTargetNopInsertEncodingParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def enc : HolAsm 8 → List (BitVec 8)
  | .jump w => [w]
  | .jumpCmp _ _ _ w => [w]
  | .loc _ w => [w]
  | _ => [0]
private def mixed : List (LabLineHOL 8) := [.label 1 2 0,.asm (.asmi (.inst .skip)) [0] 1,.labAsm (.jump (.lab 1 2)) 77 [251] 1]
private def labfirst : List (LabLineHOL 8) := [.label 1 2 0,.labAsm (.jump (.lab 1 2)) 77 [250] 1,.asm (.asmi (.inst .skip)) [0] 1]
example : linesEncWithNop enc .ln [] 5 mixed.reverse ∧ linesEncWithNop enc .ln [] 5 (addNop (enc (.inst .skip)) mixed).reverse := by
  have h : linesEncWithNop enc .ln [] 5 mixed.reverse := by
    change linesEncWithNop enc .ln [] 5 [.labAsm (.jump (.lab 1 2)) 77 [251] 1,.asm (.asmi (.inst .skip)) [0] 1,.label 1 2 0]
    simp only [linesEncWithNop,lineEncWithNop,encWithNop]
    decide +kernel
  exact ⟨h,linesEncWithNop_addNop enc .ln [] 5 mixed ⟨rfl,h⟩⟩
example : addNop (enc (.inst .skip)) mixed = [.label 1 2 0,.asm (.asmi (.inst .skip)) [0,0] 2,.labAsm (.jump (.lab 1 2)) 77 [251] 1] := rfl
example : linesEncWithNop enc .ln [] 5 labfirst.reverse ∧ linesEncWithNop enc .ln [] 5 (addNop (enc (.inst .skip)) labfirst).reverse := by
  have h : linesEncWithNop enc .ln [] 5 labfirst.reverse := by
    change linesEncWithNop enc .ln [] 5 [.asm (.asmi (.inst .skip)) [0] 1,.labAsm (.jump (.lab 1 2)) 77 [250] 1,.label 1 2 0]
    simp only [linesEncWithNop,lineEncWithNop,encWithNop]
    decide +kernel
  exact ⟨h,linesEncWithNop_addNop enc .ln [] 5 labfirst ⟨rfl,h⟩⟩
example : addNop (enc (.inst .skip)) labfirst = [.label 1 2 0,.labAsm (.jump (.lab 1 2)) 77 [250,0] 2,.asm (.asmi (.inst .skip)) [0] 1] := rfl
example : addNop (width := 8) (enc (.inst .skip)) [.label 1 2 0,.label 1 3 0] = [.label 1 2 0,.label 1 3 0] := rfl
example : linesEncWithNop enc .ln [] 5 (addNop (enc (.inst .skip)) []).reverse := by simp [addNop,linesEncWithNop]
example : linesEncWithNop enc .ln [] 5 [.labAsm .halt 77 [235] 1] ∧ linesEncWithNop enc .ln [] 5 (addNop (enc (.inst .skip)) [.labAsm .halt 77 [235] 1]).reverse := by
  have h : linesEncWithNop enc .ln [] 5 [.labAsm .halt 77 [235] 1] := by
    simp only [linesEncWithNop,lineEncWithNop,encWithNop]
    decide +kernel
  exact ⟨h,linesEncWithNop_addNop enc .ln [] 5 _ ⟨rfl,by simpa using h⟩⟩
example : linesEncWithNop enc .ln [] 5 [.labAsm (.call (.lab 1 2)) 77 [99] 1] ∧ linesEncWithNop enc .ln [] 5 (addNop (enc (.inst .skip)) [.labAsm (.call (.lab 1 2)) 77 [99] 1]).reverse := by
  have h : linesEncWithNop enc .ln [] 5 [.labAsm (.call (.lab 1 2)) 77 [99] 1] := by
    simp only [linesEncWithNop,lineEncWithNop]
    decide +kernel
  exact ⟨h,linesEncWithNop_addNop enc .ln [] 5 _ ⟨rfl,by simpa using h⟩⟩
example : ¬linesEncWithNop (width := 8) (fun _ => [0,0]) .ln [] 5 (addNop [0,0] [.asm (.asmi (.inst .skip)) [0,0] 2]).reverse := by
  simp [addNop,linesEncWithNop,lineEncWithNop,encWithNop]
example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (enc (.inst .skip)).length = 1 ∧ linesEncWithNop enc labs ffis pos ls.reverse →
    linesEncWithNop enc labs ffis pos (addNop (enc (.inst .skip)) ls).reverse := linesEncWithNop_addNop enc labs ffis pos ls

def runChecks : IO Bool := do
  IO.println "PASS full reverse-accumulator NOP encoding preservation (9 original observations, 4 actual premise instances, full arbitrary-width consumer)"
  pure true
end Flapjack.Test.LabToTargetNopInsertEncodingParity
