import Flapjack.Compiler.Backend.LabToTarget.LineInfo
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack syntax factoring of the literal HOL GENLIST/MAP/FLAT expression;
there is no independently named HOL declaration for this abbreviation. -/
private def rawShmemEntries {width : Nat} [NeZero width] (secs : LabProgHOL width) (p : Nat) :
    List (HolFfiName × ShmemInfoNum) :=
  (((List.range (numPcs secs)).map (fun i => (i,asmFetchAux i secs))).map
    (lineToInfo secs p)).flatten

/-- Flapjack map congruence over the reviewed original empty-section law. -/
private theorem rawShmemEntries_empty {width : Nat} [NeZero width]
    (k p : Nat) (rest : LabProgHOL width) :
    rawShmemEntries (⟨k,[]⟩::rest) p = rawShmemEntries rest p := by
  simp only [rawShmemEntries,numPcs,asmFetchAux,List.map_map,Function.comp_def,
    lineToInfo_hdEmpty]

/-- Flapjack map congruence over the original literal zero-label law. -/
private theorem rawShmemEntries_label {width : Nat} [NeZero width]
    (k a b p : Nat) (xs : List (LabLineHOL width)) (rest : LabProgHOL width) :
    rawShmemEntries (⟨k,.label a b 0::xs⟩::rest) p =
      rawShmemEntries (⟨k,xs⟩::rest) p := by
  simp only [rawShmemEntries,numPcs,asmFetchAux,isLabelHOL,↓reduceIte,
    List.map_map,Function.comp_def,lineToInfo_hdLabel]

/-- Flapjack structural infrastructure projects the full original fetch and
line-extraction successors, keeping every tail entry in order. -/
private theorem rawShmemEntries_asm {width : Nat} [NeZero width]
    (k : Nat) (a : AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (bytes : List (BitVec 8)) (len p : Nat) (xs : List (LabLineHOL width))
    (rest : LabProgHOL width) :
    rawShmemEntries (⟨k,.asm a bytes len::xs⟩::rest) p =
      lineToInfo (⟨k,.asm a bytes len::xs⟩::rest) p (0,some (.asm a bytes len)) ++
        rawShmemEntries (⟨k,xs⟩::rest) (p+bytes.length) := by
  have hcount : numPcs (⟨k,.asm a bytes len::xs⟩::rest) = numPcs (⟨k,xs⟩::rest)+1 := by
    simp [numPcs,isLabelHOL,Nat.add_comm]
  unfold rawShmemEntries
  rw [hcount,genlist_asmFetchAux_next (.asm a bytes len) k xs rest _ (by rfl),
    List.map_cons,List.flatten_cons]
  congr 1
  apply congrArg List.flatten
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i _
  exact (lineToInfo_next (firstCode := 1) (firstFetched := 1)
    (secondCode := width) (secondFetched := width)
    0 .halt 0 [] 0 [] [] 0 0 none
    k a bytes len xs rest p i (asmFetchAux i (⟨k,xs⟩::rest))).2

/-- Flapjack structural infrastructure for the LabAsm half of the same full
original conjunction; no separate HOL fragment is tagged. -/
private theorem rawShmemEntries_lab {width : Nat} [NeZero width]
    (k : Nat) (a : AsmWithLab HolCmp (HolRegImm width) MlString) (w : BitVec width)
    (bytes : List (BitVec 8)) (len p : Nat) (xs : List (LabLineHOL width))
    (rest : LabProgHOL width) :
    rawShmemEntries (⟨k,.labAsm a w bytes len::xs⟩::rest) p =
      lineToInfo (⟨k,.labAsm a w bytes len::xs⟩::rest) p (0,some (.labAsm a w bytes len)) ++
        rawShmemEntries (⟨k,xs⟩::rest) (p+bytes.length) := by
  have hcount : numPcs (⟨k,.labAsm a w bytes len::xs⟩::rest) = numPcs (⟨k,xs⟩::rest)+1 := by
    simp [numPcs,isLabelHOL,Nat.add_comm]
  unfold rawShmemEntries
  rw [hcount,genlist_asmFetchAux_next (.labAsm a w bytes len) k xs rest _ (by rfl),
    List.map_cons,List.flatten_cons]
  congr 1
  apply congrArg List.flatten
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i _
  exact (lineToInfo_next (firstCode := width) (firstFetched := width)
    (secondCode := 1) (secondFetched := 1)
    k a w bytes len xs rest p i (asmFetchAux i (⟨k,xs⟩::rest))
    0 (.asmi (.inst .skip)) [] 0 [] [] 0 0 none).1

/-- Full original extraction characterization. Existing names and info records
are arbitrary prefixes; queried and encoding-validity starts remain independent.
The sole original all_enc_ok guard is retained, and no target execution or
assumed extraction result is supplied. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "get_shmem_info_thm" (words_as_type_indexed_bitvec)]
theorem getShmemInfo_characterization {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (p : Nat) (ffiNames : List HolFfiName)
    (shmemInfo : List ShmemInfoNum) (validPos : Nat) (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) :
    allEncOk c labs ffis validPos secs →
    getShmemInfo secs p ffiNames shmemInfo =
      let (newFfis,newInfo) :=
        (((List.range (numPcs secs)).map (fun i => (i,asmFetchAux i secs))).map
          (lineToInfo secs p)).flatten.unzip
      (ffiNames ++ newFfis,shmemInfo ++ newInfo) := by
  simp only [List.unzip_eq_map]
  change allEncOk c labs ffis validPos secs →
    getShmemInfo secs p ffiNames shmemInfo =
      (ffiNames ++ (rawShmemEntries secs p).map Prod.fst,
       shmemInfo ++ (rawShmemEntries secs p).map Prod.snd)
  induction secs generalizing p ffiNames shmemInfo validPos with
  | nil => simp [getShmemInfo,rawShmemEntries,numPcs]
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    induction lines generalizing p ffiNames shmemInfo validPos with
    | nil =>
      intro he
      rw [allEncOk] at he
      rw [getShmemInfo,rawShmemEntries_empty]
      exact ih p ffiNames shmemInfo validPos he.2
    | cons head lines ihLines =>
      intro he
      have hparts : lineOk c labs ffis validPos head ∧
          allEncOk c labs ffis (validPos+lineLength head) (⟨k,lines⟩::rest) := by
        rw [allEncOk] at he
        exact he
      cases head with
      | label a b len =>
        have hz : validPos%2=0 ∧ len=0 := by simpa only [lineOk] using hparts.1
        have hlen := hz.2
        subst len
        have ht : allEncOk c labs ffis validPos (⟨k,lines⟩::rest) := by
          simpa only [lineLength,↓reduceIte,Nat.add_zero] using hparts.2
        rw [getShmemInfo,rawShmemEntries_label]
        exact ihLines p ffiNames shmemInfo validPos ht
      | asm a bytes len =>
        have ht : allEncOk c labs ffis (validPos+bytes.length) (⟨k,lines⟩::rest) :=
          hparts.2
        cases a with
        | asmi inst =>
          simpa only [getShmemInfo,rawShmemEntries_asm,lineToInfo,List.nil_append] using
            ihLines (p+bytes.length) ffiNames shmemInfo (validPos+bytes.length) ht
        | cbw r1 r2 =>
          simpa only [getShmemInfo,rawShmemEntries_asm,lineToInfo,List.nil_append] using
            ihLines (p+bytes.length) ffiNames shmemInfo (validPos+bytes.length) ht
        | shareMem op reg addr =>
          cases addr with
          | addr base offset =>
            rcases hmem : getMemopInfo op with ⟨name,nb⟩
            let entry : ShmemInfoNum :=
              {entryPc:=p,nbytes:=nb,addrReg:=base,addrOff:=offset.toNat,reg:=reg,exitPc:=p+bytes.length}
            have h := ihLines (p+bytes.length) (ffiNames++[.sharedMem name])
              (shmemInfo++[entry]) (validPos+bytes.length) ht
            simpa only [getShmemInfo,rawShmemEntries_asm,lineToInfo,hmem,posVal,isLabelHOL,
              Bool.false_eq_true,↓reduceIte,List.map_append,List.map_cons,List.map_nil,
              List.append_assoc,List.singleton_append,entry] using h
      | labAsm a w bytes len =>
        have ht : allEncOk c labs ffis (validPos+bytes.length) (⟨k,lines⟩::rest) :=
          hparts.2
        simpa only [getShmemInfo,rawShmemEntries_lab,lineToInfo,List.nil_append] using
          ihLines (p+bytes.length) ffiNames shmemInfo (validPos+bytes.length) ht
end Flapjack.Compiler.Backend.LabToTarget
