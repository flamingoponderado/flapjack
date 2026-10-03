import Flapjack.Compiler.Backend.LabToTarget.LineInfo
namespace Flapjack.Test.LabToTargetLineInfoParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {firstCode : Nat} {firstFetched : Nat} {secondCode : Nat} {secondFetched : Nat}
    [NeZero firstCode] [NeZero firstFetched] [NeZero secondCode] [NeZero secondFetched]
    (k1 : Nat) (a : AsmWithLab HolCmp (HolRegImm firstCode) MlString)
    (b : BitVec firstCode) (bytes1 : List (BitVec 8)) (len1 : Nat)
    (xs1 : List (Line (AsmOrCbw (HolAsm firstCode) HolMemop (HolAddr firstCode)) (AsmWithLab HolCmp (HolRegImm firstCode) MlString) (BitVec firstCode))) (rest1 : List (Section (Line (AsmOrCbw (HolAsm firstCode) HolMemop (HolAddr firstCode)) (AsmWithLab HolCmp (HolRegImm firstCode) MlString) (BitVec firstCode)))) (p1 i1 : Nat) (l1 : Option (Line (AsmOrCbw (HolAsm firstFetched) HolMemop (HolAddr firstFetched)) (AsmWithLab HolCmp (HolRegImm firstFetched) MlString) (BitVec firstFetched)))
    (k2 : Nat) (c2 : AsmOrCbw (HolAsm secondCode) HolMemop (HolAddr secondCode))
    (bytes2 : List (BitVec 8)) (len2 : Nat) (xs2 : List (Line (AsmOrCbw (HolAsm secondCode) HolMemop (HolAddr secondCode)) (AsmWithLab HolCmp (HolRegImm secondCode) MlString) (BitVec secondCode)))
    (rest2 : List (Section (Line (AsmOrCbw (HolAsm secondCode) HolMemop (HolAddr secondCode)) (AsmWithLab HolCmp (HolRegImm secondCode) MlString) (BitVec secondCode)))) (p2 i2 : Nat) (l2 : Option (Line (AsmOrCbw (HolAsm secondFetched) HolMemop (HolAddr secondFetched)) (AsmWithLab HolCmp (HolRegImm secondFetched) MlString) (BitVec secondFetched))) :
    lineToInfo (⟨k1,.labAsm a b bytes1 len1::xs1⟩::rest1) p1 (i1+1,l1) =
      lineToInfo (⟨k1,xs1⟩::rest1) (p1+bytes1.length) (i1,l1) ∧
    lineToInfo (⟨k2,.asm c2 bytes2 len2::xs2⟩::rest2) p2 (i2+1,l2) =
      lineToInfo (⟨k2,xs2⟩::rest2) (p2+bytes2.length) (i2,l2) :=
  lineToInfo_next k1 a b bytes1 len1 xs1 rest1 p1 i1 l1 k2 c2 bytes2 len2 xs2 rest2 p2 i2 l2
example {codeWidth : Nat} {fetchedWidth : Nat}
    [NeZero codeWidth] [NeZero fetchedWidth] (k : Nat) (rest : List (Section (Line (AsmOrCbw (HolAsm codeWidth) HolMemop (HolAddr codeWidth)) (AsmWithLab HolCmp (HolRegImm codeWidth) MlString) (BitVec codeWidth))))
    (p : Nat) (t : Nat × Option (Line (AsmOrCbw (HolAsm fetchedWidth) HolMemop (HolAddr fetchedWidth)) (AsmWithLab HolCmp (HolRegImm fetchedWidth) MlString) (BitVec fetchedWidth))) :
    lineToInfo (⟨k,[]⟩::rest) p t = lineToInfo rest p t :=
  lineToInfo_hdEmpty k rest p t
example {codeWidth : Nat} {fetchedWidth : Nat}
    [NeZero codeWidth] [NeZero fetchedWidth] (k a b : Nat)
    (xs : List (LabLineHOL codeWidth)) (rest : List (Section (Line (AsmOrCbw (HolAsm codeWidth) HolMemop (HolAddr codeWidth)) (AsmWithLab HolCmp (HolRegImm codeWidth) MlString) (BitVec codeWidth)))) (p : Nat)
    (t : Nat × Option (Line (AsmOrCbw (HolAsm fetchedWidth) HolMemop (HolAddr fetchedWidth)) (AsmWithLab HolCmp (HolRegImm fetchedWidth) MlString) (BitVec fetchedWidth))) :
    lineToInfo (⟨k,.label a b 0::xs⟩::rest) p t =
      lineToInfo (⟨k,xs⟩::rest) p t :=
  lineToInfo_hdLabel k a b xs rest p t
example {width : Nat} [NeZero width]
    (x : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (k : Nat) (xs : List (LabLineHOL width)) (rest : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (n : Nat) :
    isLabelHOL x = false →
    (List.range (n+1)).map (fun i => (i,asmFetchAux i (⟨k,x::xs⟩::rest))) =
      (0,some x)::(List.range n).map
        (fun i => (i+1,asmFetchAux i (⟨k,xs⟩::rest))) :=
  genlist_asmFetchAux_next x k xs rest n
private def code1 : LabProgHOL 1 :=
  [⟨10,[.label 10 1 99,.asm (.asmi (.inst .skip)) [7,8,9] 999]⟩]
private def fetched80 : LabLineHOL 80 :=
  .asm (.shareMem .load32 7 (.addr 2 (-1))) [11,22] 999
example : lineToInfo code1 13 (0,some fetched80) =
    [(.sharedMem .mappedRead,{entryPc:=14,nbytes:=4,addrReg:=2,addrOff:=1208925819614629174706175,reg:=7,exitPc:=16})] := by cbv
example : lineToInfo code1 13 (1,some fetched80) =
    [(.sharedMem .mappedRead,{entryPc:=17,nbytes:=4,addrReg:=2,addrOff:=1208925819614629174706175,reg:=7,exitPc:=19})] := by cbv
example : lineToInfo ([] : LabProgHOL 1) 7 (99,some (.asm (.shareMem .load 3 (.addr 2 (255 : BitVec 8))) [11,22,33] 999)) =
    [(.sharedMem .mappedRead,{entryPc:=7,nbytes:=0,addrReg:=2,addrOff:=255,reg:=3,exitPc:=10})] := by cbv
example : lineToInfo ([] : LabProgHOL 1) 7 (99,some (.asm (.shareMem .load32 3 (.addr 2 (255 : BitVec 8))) [11,22,33] 999)) =
    [(.sharedMem .mappedRead,{entryPc:=7,nbytes:=4,addrReg:=2,addrOff:=255,reg:=3,exitPc:=10})] := by cbv
example : lineToInfo ([] : LabProgHOL 1) 7 (99,some (.asm (.shareMem .load16 3 (.addr 2 (255 : BitVec 8))) [11,22,33] 999)) =
    [(.sharedMem .mappedRead,{entryPc:=7,nbytes:=2,addrReg:=2,addrOff:=255,reg:=3,exitPc:=10})] := by cbv
example : lineToInfo ([] : LabProgHOL 1) 7 (99,some (.asm (.shareMem .load8 3 (.addr 2 (255 : BitVec 8))) [11,22,33] 999)) =
    [(.sharedMem .mappedRead,{entryPc:=7,nbytes:=1,addrReg:=2,addrOff:=255,reg:=3,exitPc:=10})] := by cbv
example : lineToInfo ([] : LabProgHOL 1) 7 (99,some (.asm (.shareMem .store 3 (.addr 2 (255 : BitVec 8))) [11,22,33] 999)) =
    [(.sharedMem .mappedWrite,{entryPc:=7,nbytes:=0,addrReg:=2,addrOff:=255,reg:=3,exitPc:=10})] := by cbv
example : lineToInfo ([] : LabProgHOL 1) 7 (99,some (.asm (.shareMem .store32 3 (.addr 2 (255 : BitVec 8))) [11,22,33] 999)) =
    [(.sharedMem .mappedWrite,{entryPc:=7,nbytes:=4,addrReg:=2,addrOff:=255,reg:=3,exitPc:=10})] := by cbv
example : lineToInfo ([] : LabProgHOL 1) 7 (99,some (.asm (.shareMem .store16 3 (.addr 2 (255 : BitVec 8))) [11,22,33] 999)) =
    [(.sharedMem .mappedWrite,{entryPc:=7,nbytes:=2,addrReg:=2,addrOff:=255,reg:=3,exitPc:=10})] := by cbv
example : lineToInfo ([] : LabProgHOL 1) 7 (99,some (.asm (.shareMem .store8 3 (.addr 2 (255 : BitVec 8))) [11,22,33] 999)) =
    [(.sharedMem .mappedWrite,{entryPc:=7,nbytes:=1,addrReg:=2,addrOff:=255,reg:=3,exitPc:=10})] := by cbv
example : lineToInfo code1 13 (0,(none : Option (LabLineHOL 80))) = [] := by cbv
example : lineToInfo code1 13 (0,some (.label 1 2 99 : LabLineHOL 80)) = [] := by cbv
example : lineToInfo code1 13 (0,some (.asm (.asmi (.inst .skip)) [0,0] 2 : LabLineHOL 80)) = [] := by cbv
example : lineToInfo code1 13 (0,some (.asm (.cbw 1 2) [0,0] 2 : LabLineHOL 80)) = [] := by cbv
example : lineToInfo code1 13 (0,some (.labAsm .halt 0 [0,0] 2 : LabLineHOL 80)) = [] := by cbv
example : lineToInfo (⟨0,[]⟩::code1) 13 (0,some fetched80) = lineToInfo code1 13 (0,some fetched80) := by cbv
example : lineToInfo (⟨0,[.label 1 2 0]⟩::code1) 13 (0,some fetched80) = lineToInfo code1 13 (0,some fetched80) := by cbv
/-- A real application uses four different source dimensions simultaneously. -/
example :
    lineToInfo (⟨1,[.labAsm .halt (0 : BitVec 1) [0,0,0] 999]⟩::code1) 13 (1,some fetched80) =
      lineToInfo (⟨1,[]⟩::code1) 16 (0,some fetched80) ∧
    lineToInfo ([⟨2,[.asm (.asmi (.inst .skip)) [0] 999]⟩] : LabProgHOL 64) 100
      (1,some (.asm (.shareMem .store8 3 (.addr 2 255)) [11,22] 99 : LabLineHOL 8)) =
      lineToInfo ([⟨2,[]⟩] : LabProgHOL 64) 101
      (0,some (.asm (.shareMem .store8 3 (.addr 2 255)) [11,22] 99 : LabLineHOL 8)) :=
  lineToInfo_next 1 .halt 0 [0,0,0] 999 [] code1 13 0 (some fetched80)
    2 (.asmi (.inst .skip)) [0] 999 [] [] 100 0
    (some (.asm (.shareMem .store8 3 (.addr 2 255)) [11,22] 99))
example : (List.range 4).map (fun i=> (i,asmFetchAux i ([⟨1,[.asm (.asmi (.inst .skip)) [0] 999]⟩] : LabProgHOL 8))) =
    [(0,some (.asm (.asmi (.inst .skip)) [0] 999)),(1,none),(2,none),(3,none)] := by cbv
end Flapjack.Test.LabToTargetLineInfoParity
