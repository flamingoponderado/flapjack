module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FfiSource
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MemoryRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArrayImp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.ReadBytearray
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GetVars

@[expose] public section

/-! Relating the source FFI arguments to the target's memory roots. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
  Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Decode the byte-array length from the header using the arithmetic in the
HOL FFI assignment proof. -/
private theorem ffi_header_length {width : Nat} [NeZero width]
    (conf : Config) (header : BitVec width) (length : Nat)
    (good : goodDimindex width)
    (bounds : if width = 32 then
        length + 4 < 2 ^ (width - 3) ∧
        header >>> (width - conf.lenSize - 2) = BitVec.ofNat width (length + 4)
      else
        length + 8 < 2 ^ (width - 3) ∧
        header >>> (width - conf.lenSize - 3) = BitVec.ofNat width (length + 8)) :
    let decoded := (header >>> (width - wordShiftAmount width - conf.lenSize)) - wordSemBytesInWord
    decoded = BitVec.ofNat width length ∧ decoded.toNat = length := by
  rcases good with hw | hw <;> subst width
  · simp only [↓reduceIte] at bounds
    have shiftEq : 32 - wordShiftAmount 32 - conf.lenSize = 32 - conf.lenSize - 2 := by
      simp [wordShiftAmount]
      omega
    have lengthBound : length < 2 ^ 32 := by
      have h := bounds.1
      norm_num at h ⊢
      omega
    simp only [shiftEq, bounds.2, wordSemBytesInWord]
    constructor
    · simp [BitVec.ofNat_add]
    · simp [BitVec.ofNat_add, BitVec.toNat_ofNat]
      norm_num at lengthBound
      exact lengthBound
  · simp only [show 64 ≠ 32 by decide, if_false] at bounds
    have shiftEq : 64 - wordShiftAmount 64 - conf.lenSize = 64 - conf.lenSize - 3 := by
      simp [wordShiftAmount]
      omega
    have lengthBound : length < 2 ^ 64 := by omega
    simp only [shiftEq, bounds.2, wordSemBytesInWord]
    constructor
    · simp [BitVec.ofNat_add]
    · simp [BitVec.ofNat_add, BitVec.toNat_ofNat]
      norm_num at lengthBound
      exact lengthBound

/-- The emitted length expression loads and decodes a related byte-array
header. Its premises are established from the source state relation below. -/
private theorem ffi_length_expression {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (target : WordSemStateFiniteExact width C F) (reg : Nat)
    (address header : BitVec width) (length : Nat)
    (good : goodDimindex width)
    (addressEval : WordSemStateFiniteExact.wordExp target (realAddr conf reg) = some (.word address))
    (present : target.mdomain address = true) (memory : target.memory address = .word header)
    (decoded : (header >>> (width - wordShiftAmount width - conf.lenSize)) - wordSemBytesInWord =
      BitVec.ofNat width length) :
    WordSemStateFiniteExact.wordExp target
      (.op .sub [shiftN .lsr (.load (realAddr conf reg)) (width - wordShiftAmount width - conf.lenSize),
        .const wordSemBytesInWord]) = some (.word (BitVec.ofNat width length)) := by
  have offsetBound : width - wordShiftAmount width - conf.lenSize < width := by
    rcases good with h | h <;> subst width <;> simp [wordShiftAmount] <;> omega
  have widthBound : width < 2 ^ width := by
    rcases good with h | h <;> subst width <;> decide
  have offsetWord : (BitVec.ofNat width (width - wordShiftAmount width - conf.lenSize)).toNat =
      width - wordShiftAmount width - conf.lenSize := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans offsetBound widthBound)]
  simp [WordSemStateFiniteExact.wordExp, shiftN, addressEval, WordSemStateFiniteExact.memLoad,
    present, memory, wordShiftHOL, offsetWord, Nat.not_le_of_gt offsetBound,
    theWords, wordOpHOL, wordOp, decoded]

/-- The root and byte-read preparation carried out in the HOL `assign_FFI`
proof. This factors its successful source evaluation and local-variable reads;
it is not a separate HOL theorem. -/
theorem ffi_success_inputs {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source cut resultState : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (args : List Nat) (values : List DataSem.Value)
    (name : Basis.Pure.MlString.MlString) (result : DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (cutRun : DataSem.cutStateOpt (some names) source = some cut)
    (read : DataSem.getVars args source.locals = some values)
    (run : DataSem.doApp (.ffi name) values cut = .val (result, resultState)) :
    ∃ (firstVar secondVar : Nat) (firstFlag secondFlag : Bool) (first second : Nat)
      (config bytes updated : List (BitVec 8)) (ffi : HolFfiState F)
      (firstWord secondWord : WordLocW width),
      args = [firstVar, secondVar] ∧
      values = [.refPtr firstFlag first, .refPtr secondFlag second] ∧
      WordSemStateFiniteExact.getVars [adjustVar firstVar, adjustVar secondVar] target =
        some [firstWord, secondWord] ∧
      sptLookup first source.refs = some (.byteArray true config) ∧
      sptLookup second source.refs = some (.byteArray false bytes) ∧
      callFFIHOL source.ffi (.extCall name) config bytes = .ret ffi updated ∧
      updated.length = bytes.length ∧
      Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain
        ((.refPtr firstFlag first, firstWord) :: (.refPtr secondFlag second, secondWord) ::
          (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
           [(theGlobal source.global, holFapply target.store .globals)] ++
           flatStack source.stack target.stack)) ∧
      ∃ (w1 w2 address1 address2 header1 header2 : BitVec width),
        firstWord = .word w1 ∧ secondWord = .word w2 ∧
        getRealAddr conf target.store w1 = some address1 ∧
        getRealAddr conf target.store w2 = some address2 ∧
        target.memory address1 = .word header1 ∧ target.memory address2 = .word header2 ∧
        readBytearrayGenericHOL (address1 + StackRemove.bytesInWord width) config.length
          (memLoadByteAuxExact target.memory target.mdomain target.be) = some config ∧
        readBytearrayGenericHOL (address2 + StackRemove.bytesInWord width) bytes.length
          (memLoadByteAuxExact target.memory target.mdomain target.be) = some bytes ∧
        (if width = 32 then
          config.length + 4 < 2 ^ (width - 3) ∧
          header1 >>> (width - conf.lenSize - 2) = BitVec.ofNat width (config.length + 4)
        else
          config.length + 8 < 2 ^ (width - 3) ∧
          header1 >>> (width - conf.lenSize - 3) = BitVec.ofNat width (config.length + 8)) ∧
        (if width = 32 then
          bytes.length + 4 < 2 ^ (width - 3) ∧
          header2 >>> (width - conf.lenSize - 2) = BitVec.ofNat width (bytes.length + 4)
        else
          bytes.length + 8 < 2 ^ (width - 3) ∧
          header2 >>> (width - conf.lenSize - 3) = BitVec.ofNat width (bytes.length + 8)) ∧
        (let decoded := (header1 >>> (width - wordShiftAmount width - conf.lenSize)) - wordSemBytesInWord
         decoded = BitVec.ofNat width config.length ∧ decoded.toNat = config.length) ∧
        (let decoded := (header2 >>> (width - wordShiftAmount width - conf.lenSize)) - wordSemBytesInWord
         decoded = BitVec.ofNat width bytes.length ∧ decoded.toNat = bytes.length) ∧
        WordSemStateFiniteExact.wordExp target (realAddr conf (adjustVar firstVar)) = some (.word address1) ∧
        WordSemStateFiniteExact.wordExp target (realAddr conf (adjustVar secondVar)) = some (.word address2) ∧
        WordSemStateFiniteExact.wordExp target
          (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar firstVar)))
            (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord]) =
              some (.word (BitVec.ofNat width config.length)) ∧
        WordSemStateFiniteExact.wordExp target
          (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar secondVar)))
            (width - wordShiftAmount width - conf.lenSize), .const wordSemBytesInWord]) =
              some (.word (BitVec.ofNat width bytes.length)) := by
  obtain ⟨base, flag1, flag2, first, second, config, bytes, updated, ffi,
    baseRun, valuesEq, firstRead, secondRead, call, lengthEq, resultEq, resultStateEq⟩ :=
    doApp_ffi_success name values cut resultState result run
  have cutEq := cutStateOpt_some_eq names source cut cutRun
  subst cut
  have argsLength : args.length = 2 := by
    have h := DataSpace.getVars_length args source.locals values read
    simpa [valuesEq] using h.symm
  cases args with
  | nil => simp at argsLength
  | cons firstVar rest =>
    cases rest with
    | nil => simp at argsLength
    | cons secondVar rest =>
      cases rest with
      | cons thirdVar rest => simp at argsLength
      | nil =>
        obtain ⟨words, wordRead, wordLength⟩ :=
          stateRel_getVars conf l1 l2 source target locs [firstVar, secondVar] values related read
        have wordsLength : words.length = 2 := by simpa [valuesEq] using wordLength.symm
        cases words with
        | nil => simp at wordsLength
        | cons firstWord rest =>
          cases rest with
          | nil => simp at wordsLength
          | cons secondWord rest =>
            cases rest with
            | cons thirdWord rest => simp at wordsLength
            | nil =>
              have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
              have rooted := memoryRel_getVars conf target.be (holThe source.tstamps) source
                source.space target.store target.memory target.mdomain target
                ([(theGlobal source.global, holFapply target.store .globals)] ++
                  flatStack source.stack target.stack)
                [firstVar, secondVar] values [firstWord, secondWord]
                ⟨by simpa using memory, read, by simpa using wordRead⟩
              have roots : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                  target.store target.memory target.mdomain
                  ((.refPtr flag1 first, firstWord) :: (.refPtr flag2 second, secondWord) ::
                    (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
                      [(theGlobal source.global, holFapply target.store .globals)] ++
                      flatStack source.stack target.stack)) := by
                simpa [valuesEq] using rooted
              have good := related.2.2.2.2.2.2.1
              have firstLookup : sptLookup first source.refs = some (.byteArray true config) := by simpa using firstRead
              have secondLookup : sptLookup second source.refs = some (.byteArray false bytes) := by simpa using secondRead
              obtain ⟨w1, address1, header1, _, loc1, _, _, _, _, _, _, real1, mem1, dom1, reads1, _, bound1⟩ :=
                Memory.memoryRel_byteArrayImp (β := Unit) conf target.be (holThe source.tstamps)
                  source.refs source.space target.store target.memory target.mdomain flag1 true first config
                  firstWord _ ⟨roots, firstLookup, good⟩
              have tailRoots := Memory.memoryRel_tl conf target.be (holThe source.tstamps)
                source.refs source.space target.store target.memory target.mdomain _ _ roots
              obtain ⟨w2, address2, header2, _, loc2, _, _, _, _, _, _, real2, mem2, dom2, reads2, _, bound2⟩ :=
                Memory.memoryRel_byteArrayImp (β := Unit) conf target.be (holThe source.tstamps)
                  source.refs source.space target.store target.memory target.mdomain flag2 false second bytes
                  secondWord _ ⟨tailRoots, secondLookup, good⟩
              have configRead := imp_readBytearray_genList config config.length
                (address1 + StackRemove.bytesInWord width) (memLoadByteAuxExact target.memory target.mdomain target.be)
                ⟨rfl, fun i hi => ⟨hi, reads1 i hi⟩⟩
              have bytesRead := imp_readBytearray_genList bytes bytes.length
                (address2 + StackRemove.bytesInWord width) (memLoadByteAuxExact target.memory target.mdomain target.be)
                ⟨rfl, fun i hi => ⟨hi, reads2 i hi⟩⟩
              have ⟨firstVarRead, secondVarRead⟩ := getVars_two_imp target
                (adjustVar firstVar) (adjustVar secondVar) firstWord secondWord (by simpa using wordRead)
              rw [loc1] at firstVarRead
              rw [loc2] at secondVarRead
              have shiftBound := related.2.2.2.2.2.2.2.1
              have addrEval1 := Bignum.getRealAddr_lemma conf (adjustVar firstVar) target w1 address1
                ⟨shiftBound, good, firstVarRead, real1⟩
              have addrEval2 := Bignum.getRealAddr_lemma conf (adjustVar secondVar) target w2 address2
                ⟨shiftBound, good, secondVarRead, real2⟩
              have decoded1 := ffi_header_length conf header1 config.length good bound1
              have decoded2 := ffi_header_length conf header2 bytes.length good bound2
              have lengthEval1 := ffi_length_expression conf target (adjustVar firstVar) address1 header1
                config.length good addrEval1 dom1 mem1 decoded1.1
              have lengthEval2 := ffi_length_expression conf target (adjustVar secondVar) address2 header2
                bytes.length good addrEval2 dom2 mem2 decoded2.1
              refine ⟨firstVar, secondVar, flag1, flag2, first, second, config, bytes,
                updated, ffi, firstWord, secondWord, rfl, valuesEq, ?_, ?_, ?_, ?_, lengthEq, ?_⟩
              · simpa using wordRead
              · simpa using firstRead
              · simpa using secondRead
              · simpa using call
              · exact ⟨roots, w1, w2, address1, address2, header1, header2,
                  loc1, loc2, real1, real2, mem1, mem2, configRead, bytesRead, bound1, bound2,
                  decoded1, decoded2, addrEval1, addrEval2, lengthEval1, lengthEval2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
