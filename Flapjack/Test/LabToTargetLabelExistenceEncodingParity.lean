import Flapjack.Compiler.Backend.LabToTarget.LabelExistenceEncoding
import Mathlib.Data.Set.Insert
namespace Flapjack.Test.LabToTargetLabelExistenceEncodingParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps.LabelSets
private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 10 .ln) .ln
private def existLabs : Spt (Spt Bool) := sptInsert 3 (sptInsert 4 false .ln) .ln
private def enc (_ : HolAsm 8) : List (BitVec 8) := [7,8]
private def acc : List (LabLineHOL 8) := [.labAsm (.locValue 2 (.lab 3 4)) 77 [9] 2,.label 7 8 4]
private def lines : List (LabLineHOL 8) := [.labAsm (.jump (.lab 3 4)) 99 [] 1,.labAsm .halt 99 [] 1]
private def result : List (LabLineHOL 8) := [.label 7 8 4,.labAsm (.locValue 2 (.lab 3 4)) 77 [9] 2,
  .labAsm (.jump (.lab 3 4)) 4 [7,8] 2,.labAsm .halt 232 [7,8] 2]
private theorem guards : (∀ l ∈ acc,lineLabsExist existLabs l) ∧ (∀ l ∈ lines,lineLabsExist existLabs l) := by
  simp [acc,lines,lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,existLabs,sptLookup,sptInsert]
private theorem growth (flag : Bool) : encLinesAgain labs [] 6 enc lines acc flag = (result,10,false) := by
  simp [encLinesAgain,labs,lines,acc,result,enc,getJumpOffset,findPos,getLabel,lookupAny,sptLookup,sptInsert,ffiOffset]
example := guards
example : encLinesAgain labs [] 6 enc lines acc true = (result,10,false) := growth true
example : encLinesAgain labs [] 6 enc lines acc false = (result,10,false) := growth false
example : ∀ l ∈ (encLinesAgain labs [] 6 enc lines acc true).1,lineLabsExist existLabs l := by
  rw [growth true]
  exact encLinesAgain_lineLabsExist labs [] 6 enc lines acc true result (10,false) existLabs
    ⟨growth true,guards⟩
example : encLinesAgain labs [] 6 enc [.labAsm (.jump (.lab 3 4)) 99 [] 3] acc true =
    ([.label 7 8 4,.labAsm (.locValue 2 (.lab 3 4)) 77 [9] 2,.labAsm (.jump (.lab 3 4)) 4 [7,8] 3],9,true) := by
  simp [encLinesAgain,labs,acc,enc,getJumpOffset,findPos,getLabel,lookupAny,sptLookup,sptInsert]
example : encLinesAgain labs [] 34 enc [] acc false = (acc.reverse,34,false) ∧
    (∀ l ∈ acc.reverse,lineLabsExist existLabs l) :=
  ⟨rfl,fun l hm => guards.1 l (List.mem_reverse.mp hm)⟩
private def code : List (Section (LabLineHOL 8)) :=
  [⟨7,[.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3,.labAsm (.jump (.lab 3 4)) 99 [] 1,.labAsm .halt 99 [] 1]⟩,
   ⟨8,[.labAsm (.call (.lab 3 4)) 99 [] 1]⟩,⟨9,[]⟩]
private def codeResult : List (Section (LabLineHOL 8)) :=
  [⟨7,[.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3,.labAsm (.jump (.lab 3 4)) 6 [7,8] 2,.labAsm .halt 234 [7,8] 2]⟩,
   ⟨8,[.labAsm (.call (.lab 3 4)) 2 [7,8] 2]⟩,⟨9,[]⟩]
private theorem sectionResult : encSecsAgain 0 labs [] enc code = (codeResult,false) := by
  simp [encSecsAgain,encLinesAgain,code,codeResult,labs,enc,getJumpOffset,findPos,getLabel,lookupAny,sptLookup,sptInsert,ffiOffset]
private theorem sectionGuard : allLabsExist existLabs code := by
  simp [allLabsExist,secLabsExist,lineLabsExist,code,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,existLabs,sptLookup,sptInsert]
example : encSecsAgain 0 labs [] enc code = (codeResult,false) ∧
    allLabsExist existLabs code ∧ allLabsExist existLabs codeResult :=
  ⟨sectionResult,sectionGuard,encSecsAgain_allLabsExist 0 labs [] enc code codeResult false existLabs ⟨sectionResult,sectionGuard⟩⟩
example : ¬allLabsExist (.ln : Spt (Spt Bool)) code ∧ ¬allLabsExist (.ln : Spt (Spt Bool)) codeResult := by
  simp [allLabsExist,secLabsExist,lineLabsExist,code,codeResult,labsOf,Set.mem_singleton_iff,labLookup,sptLookup]
private theorem allConstructor (a : AsmWithLab HolCmp (HolRegImm 8) MlString)
    (h : lineLabsExist existLabs (.labAsm a (99 : BitVec 8) [] 1)) :
    ∀ l ∈ (encLinesAgain labs [] 0 enc [.labAsm a 99 [] 1] [] true).1,lineLabsExist existLabs l :=
  encLinesAgain_lineLabsExist labs [] 0 enc [.labAsm a 99 [] 1] [] true
    (encLinesAgain labs [] 0 enc [.labAsm a 99 [] 1] [] true).1
    (encLinesAgain labs [] 0 enc [.labAsm a 99 [] 1] [] true).2 existLabs ⟨rfl,by simp,by simpa using h⟩
example := allConstructor (.jump (.lab 3 4)) (by simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,existLabs,sptLookup,sptInsert])
example := allConstructor (.jumpCmp .equal 2 (.imm 1) (.lab 3 4)) (by simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,existLabs,sptLookup,sptInsert])
example := allConstructor (.locValue 2 (.lab 3 4)) (by simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,existLabs,sptLookup,sptInsert])
example := allConstructor (.call (.lab 99 88)) (by simp [lineLabsExist,labsOf])
example := allConstructor (.callFFI (.implode [])) (by simp [lineLabsExist,labsOf])
example := allConstructor .install (by simp [lineLabsExist,labsOf])
example := allConstructor .halt (by simp [lineLabsExist,labsOf])
example : encLinesAgain (width := 1) .ln [] 17 (fun _ => []) [] [] false = ([],17,false) ∧
    allLabsExist (width := 1) (.ln : Spt (Spt Bool)) [] := ⟨rfl,by simp [allLabsExist]⟩
example {α : Type} {width : Nat} [NeZero width] (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (lines acc res : List (LabLineHOL width))
    (ok : Bool) (ok' : Nat × Bool) (labs' : Spt (Spt α)) :
    encLinesAgain labs ffis pos enc lines acc ok = (res,ok') ∧
    (∀ l ∈ acc,lineLabsExist labs' l) ∧ (∀ l ∈ lines,lineLabsExist labs' l) →
    ∀ l ∈ res,lineLabsExist labs' l := encLinesAgain_lineLabsExist labs ffis pos enc lines acc ok res ok' labs'
example {α : Type} {width : Nat} [NeZero width] (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (code res : List (Section (LabLineHOL width))) (ok : Bool)
    (labs' : Spt (Spt α)) : encSecsAgain pos labs ffis enc code = (res,ok) ∧ allLabsExist labs' code →
    allLabsExist labs' res := encSecsAgain_allLabsExist pos labs ffis enc code res ok labs'
def runChecks : IO Bool := do
  IO.println "PASS full encoder label-existence preservation: ten original observations, false/true flags, reverse accumulator, actual multi-section tuples and arbitrary map/width consumers"
  pure true
end Flapjack.Test.LabToTargetLabelExistenceEncodingParity
