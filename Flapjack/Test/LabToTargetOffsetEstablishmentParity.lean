import Flapjack.Compiler.Backend.LabToTarget.OffsetEstablishment
namespace Flapjack.Test.LabToTargetOffsetEstablishmentParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 10 .ln) .ln
private def enc : HolAsm 8 → List (BitVec 8) := fun _ => [7,8]
private def lines : List (LabLineHOL 8) := [.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3,
  .labAsm (.jump (.lab 3 4)) 99 [] 1,.labAsm .halt 99 [] 1]
private def result : List (LabLineHOL 8) := [.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3,
  .labAsm (.jump (.lab 3 4)) 6 [7,8] 2,.labAsm .halt 234 [7,8] 2]
private def code : List (Section (LabLineHOL 8)) := [⟨7,lines⟩,⟨8,[.labAsm (.call (.lab 3 4)) 99 [] 1]⟩,⟨9,[]⟩]
private def codeResult : List (Section (LabLineHOL 8)) := [⟨7,result⟩,⟨8,[.labAsm (.call (.lab 3 4)) 2 [7,8] 2]⟩,⟨9,[]⟩]
private theorem growthFull : encLinesAgainSimp labs [] 0 enc lines = (result,false) := by
  simp [encLinesAgainSimp,labs,lines,result,enc,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,ffiOffset]
private theorem sectionsFull : encSecsAgain 0 labs [] enc code = (codeResult,false) := by
  simp [encSecsAgain,encLinesAgain,code,codeResult,lines,result,labs,enc,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,ffiOffset]
example : encLinesAgainSimp labs [] 0 enc lines = (result,false) := growthFull
example : linesOffsetOk labs [] 0 result := encLinesAgainSimp_offsetOk labs [] 0 enc lines result false growthFull
example : ¬linesOffsetOk labs [] 0 lines ∧ linesOffsetOk labs [] 0 (encLinesAgainSimp labs [] 0 enc lines).1 := by
  refine ⟨?_,encLinesAgainSimp_offsetOk labs [] 0 enc lines _ _ rfl⟩
  simp only [lines,linesOffsetOk,lineOffsetOk,lineLen]
  decide +kernel
example : encLinesAgainSimp labs [] 4 enc [.labAsm (.jump (.lab 3 4)) 99 [] 3] =
    ([.labAsm (.jump (.lab 3 4)) 6 [7,8] 3],true) ∧
    linesOffsetOk labs [] 4 (encLinesAgainSimp labs [] 4 enc [.labAsm (.jump (.lab 3 4)) 99 [] 3]).1 :=
  by
  refine ⟨?_,encLinesAgainSimp_offsetOk _ _ _ _ _ _ _ rfl⟩
  simp [encLinesAgainSimp,labs,enc,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert]
example : encLinesAgainSimp labs [] 4 enc [.labAsm (.jump (.lab 3 4)) 6 [] 0] =
    ([.labAsm (.jump (.lab 3 4)) 6 [] 0],true) ∧
    linesOffsetOk (width := 8) labs [] 4 [.labAsm (.jump (.lab 3 4)) 6 [] 0] :=
  by
  have he : encLinesAgainSimp labs [] 4 enc [.labAsm (.jump (.lab 3 4)) 6 [] 0] =
      ([.labAsm (.jump (.lab 3 4)) 6 [] 0],true) := by
    simp [encLinesAgainSimp,labs,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert]
  exact ⟨he,encLinesAgainSimp_offsetOk labs [] 4 enc [.labAsm (.jump (.lab 3 4)) 6 [] 0] _ true he⟩
example : encSecsAgain 0 labs [] enc code = (codeResult,false) := sectionsFull
example : offsetOk labs [] 0 codeResult := encSecsAgain_offsetOk 0 labs [] enc code codeResult false sectionsFull
example : ¬offsetOk labs [] 0 [⟨7,result⟩,⟨8,[.labAsm (.call (.lab 3 4)) 4 [7,8] 2]⟩] := by
  simp only [offsetOk,linesOffsetOk,lineOffsetOk,result]
  decide +kernel
example : encLinesAgainSimp (width := 1) .ln [] 17 (fun _ => []) [] = ([],true) ∧
    linesOffsetOk (width := 1) .ln [] 17 [] := ⟨rfl,True.intro⟩
example : encSecsAgain 17 labs [] enc [⟨7,[]⟩,⟨8,[]⟩] = ([⟨7,[]⟩,⟨8,[]⟩],true) ∧
    offsetOk (width := 8) labs [] 17 [⟨7,[]⟩,⟨8,[]⟩] :=
  ⟨rfl,encSecsAgain_offsetOk 17 labs [] enc [⟨7,[]⟩,⟨8,[]⟩] _ true rfl⟩
private def allOpcodes : List (LabLineHOL 8) := [.labAsm (.jump (.lab 3 4)) 99 [] 1,
  .labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 3 4)) 99 [] 1,
  .labAsm (.locValue 2 (.lab 3 4)) 99 [] 1,.labAsm (.call (.lab 3 4)) 99 [] 1,
  .labAsm (.callFFI (.implode [])) 99 [] 1,.labAsm .install 99 [] 1,.labAsm .halt 99 [] 1]
private def ffis : List HolFfiName := [.extCall (.implode [97]),.extCall (.implode []),.extCall (.implode [])]
example : (encLinesAgainSimp labs ffis 0 enc allOpcodes).2 = false ∧
    linesOffsetOk labs ffis 0 (encLinesAgainSimp labs ffis 0 enc allOpcodes).1 := by
  refine ⟨?_,encLinesAgainSimp_offsetOk _ _ _ _ _ _ _ rfl⟩
  decide +kernel
example : encLinesAgainSimp (width := 80) .ln [] (2^80+1) (fun _ => [7,8])
    [.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 1] =
    ([.labAsm .halt (BitVec.ofNat 80 (2^80-17)) [7,8] 2],false) ∧
    linesOffsetOk (width := 80) .ln [] (2^80+1) [.labAsm .halt (BitVec.ofNat 80 (2^80-17)) [7,8] 2] :=
  ⟨rfl,encLinesAgainSimp_offsetOk .ln [] (2^80+1) (fun _ => [7,8])
    [.labAsm .halt (BitVec.ofNat 80 (2^70+3)) [] 1] _ false rfl⟩
example {width : Nat} [NeZero width] (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (enc : HolAsm width → List (BitVec 8)) (lines res : List (LabLineHOL width)) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc lines = (res,ok) → linesOffsetOk labs ffis pos res :=
  encLinesAgainSimp_offsetOk labs ffis pos enc lines res ok
example {width : Nat} [NeZero width] (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (code res : List (Section (LabLineHOL width))) (ok : Bool) :
    encSecsAgain pos labs ffis enc code = (res,ok) → offsetOk labs ffis pos res :=
  encSecsAgain_offsetOk pos labs ffis enc code res ok

def runChecks : IO Bool := do
  IO.println "PASS full unconditional encoder offset establishment (12 original observations, both flags, actual grown section positions/full tuples, all7 opcodes and widths1/8/80)"
  pure true
end Flapjack.Test.LabToTargetOffsetEstablishmentParity
