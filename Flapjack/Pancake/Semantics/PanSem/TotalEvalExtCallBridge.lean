import Flapjack.Pancake.Semantics.PanSem.TotalEvalRanged
import Flapjack.Pancake.Semantics.PanSem.ExtCallExact

/-!
# Production/exact byte-array correspondence for the total panSem `ExtCall`

The production total evaluator reads and writes `ExtCall` byte arrays through
`panSemTotalMachineReadBytes`/`panSemTotalMachineWriteBytes` (`TotalSteps.lean`)
over the word view `panValueWordHOL` of the production memory and the domain
`memaddrs && defined`, while the exact `evaluateHOLFiniteState_extCall_source`
uses `readBytearrayWordHOL`/`panWriteBytearrayWord8HOL` over the exact memory and
`memaddrs` (HOL `read_bytearray`/`write_bytearray`).  Under `PanSemStateRelExec`
the two views and domains agree on every in-domain address, so

* the reads are equal up to the `UInt8`/`word8` projection
  (`panSemTotalMachineReadBytes_eq`), and
* the writes stay `PanSemStateRelExec`-related (`PanSemStateRelExec.machineWriteBytes`),

and with the FFI result bridge `callFfi_extCall_bridge` this gives the `ExtCall`
constructor agreement `panSemTotalEvaluate_extCall_agree`.

Untagged Flapjack-specific bridge infrastructure
(`flapjack-pxn.18.4.3.77.2.14.15`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

variable {σ : Type}

/-- The production memory word view agrees with the exact memory on the
    production domain. -/
theorem panValueWordHOL_eq_of_memoryRel
    {memaddrs : RiscV.Word 64 → Bool}
    {memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64))}
    {exactMemory : RiscV.Word 64 → HolWordLab 64}
    (hm : PanSemMemoryRel memaddrs memory exactMemory) (address : RiscV.Word 64)
    (hd : memaddrs address = true) :
    panValueWordHOL memory address = exactMemory address := by
  simp only [panValueWordHOL, hm address hd]
  cases exactMemory address
  rfl

/-- The production byte-array domain (`memaddrs && defined`) is the exact
    `memaddrs` under `PanSemStateRelExec`. -/
theorem machineDomain_iff {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ} (h : PanSemStateRelExec production exact)
    (address : RiscV.Word 64) :
    (production.memaddrs address && panValueWordDefined production.memory address) = true ↔
      exact.memaddrs address := by
  obtain ⟨_, _, _, _, _, hm, hmd, _⟩ := h
  constructor
  · intro hb
    exact (hmd address).mp (Bool.and_eq_true_iff.mp hb).1
  · intro he
    have hd := (hmd address).mpr he
    simp only [Bool.and_eq_true_iff, hd, true_and]
    simp only [panValueWordDefined, hm address hd]

/-- Byte loads agree: the production loader over the word view and machine
    domain is the exact `word8` loader. -/
theorem panMemLoadByteWord8HOL_machine_eq
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ} (h : PanSemStateRelExec production exact)
    [DecidablePred exact.memaddrs] :
    panMemLoadByteWord8HOL (panValueWordHOL production.memory)
        (fun candidate =>
          production.memaddrs candidate && panValueWordDefined production.memory candidate = true)
        production.be =
      panMemLoadByteWord8HOL exact.memory exact.memaddrs exact.be := by
  funext address
  have hbe : exact.be = production.be := h.2.2.2.2.2.2.2.2.2.1
  simp only [panMemLoadByteWord8HOL, hbe]
  by_cases hd : exact.memaddrs (panByteAlignHOL address)
  · have hdp := (machineDomain_iff h (panByteAlignHOL address)).mpr hd
    have hdb : production.memaddrs (panByteAlignHOL address) = true :=
      (Bool.and_eq_true_iff.mp hdp).1
    rw [panValueWordHOL_eq_of_memoryRel h.2.2.2.2.2.1 _ hdb]
    rcases hx : exact.memory (panByteAlignHOL address) with ⟨v⟩
    simp [hd, hdp, hx]
  · have hdp : ¬ (production.memaddrs (panByteAlignHOL address) &&
        panValueWordDefined production.memory (panByteAlignHOL address)) = true :=
      fun hb => hd ((machineDomain_iff h _).mp hb)
    rcases hv : panValueWordHOL production.memory (panByteAlignHOL address) with ⟨v⟩
    rcases hx : exact.memory (panByteAlignHOL address) with ⟨w⟩
    simp [hd, hdp]

/-- **Read correspondence.**  The production `ExtCall` byte-array read is the
    `UInt8` projection of the exact `read_bytearray`, including failure. -/
theorem panSemTotalMachineReadBytes_eq
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ} (h : PanSemStateRelExec production exact)
    [DecidablePred exact.memaddrs] (address length : RiscV.Word 64) :
    panSemTotalMachineReadBytes production address length =
      (readBytearrayWordHOL (byteWidth := 8) address length.toNat
        (panMemLoadByteWord8HOL exact.memory exact.memaddrs exact.be)).map
        (List.map UInt8.ofBitVec) := by
  unfold panSemTotalMachineReadBytes
  rw [panReadBytearrayHOL_eq_word8_projection, panMemLoadByteWord8HOL_machine_eq h]


/-- Congruence of HOL `write_bytearray`: memories agreeing on the domain,
    written under equivalent domains, still agree on the domain. -/
theorem panWriteBytearrayWord8HOL_congr (address : RiscV.Word 64) (bytes : List (BitVec 8))
    (memory₁ memory₂ : RiscV.Word 64 → HolWordLab 64)
    (domain₁ domain₂ : RiscV.Word 64 → Prop) {_ : DecidablePred domain₁} [DecidablePred domain₂]
    (bigEndian : Bool) (hdomain : ∀ c, domain₁ c ↔ domain₂ c)
    (hmemory : ∀ c, domain₂ c → memory₁ c = memory₂ c) :
    ∀ c, domain₂ c →
      panWriteBytearrayWord8HOL address bytes memory₁ domain₁ bigEndian c =
        panWriteBytearrayWord8HOL address bytes memory₂ domain₂ bigEndian c := by
  induction bytes generalizing address with
  | nil => exact hmemory
  | cons byte rest ih =>
      intro c hc
      have hrest := ih (address + 1)
      simp only [panWriteBytearrayWord8HOL]
      generalize panWriteBytearrayWord8HOL (address + 1) rest memory₁ domain₁ bigEndian = w₁
        at hrest ⊢
      generalize panWriteBytearrayWord8HOL (address + 1) rest memory₂ domain₂ bigEndian = w₂
        at hrest ⊢
      simp only [panMemStoreByteWord8HOL]
      by_cases hal : domain₂ (panByteAlignHOL address)
      · have hal₁ : domain₁ (panByteAlignHOL address) := (hdomain _).mpr hal
        have hw := hrest _ hal
        rcases h₁ : w₁ (panByteAlignHOL address) with ⟨cell₁⟩
        rcases h₂ : w₂ (panByteAlignHOL address) with ⟨cell₂⟩
        rw [h₁, h₂] at hw
        cases hw
        simp only [hal, hal₁, if_true]
        by_cases hcur : c = panByteAlignHOL address
        · simp [hcur]
        · simp only [hcur, if_false]
          exact hrest c hc
      · have hal₁ : ¬ domain₁ (panByteAlignHOL address) := fun h => hal ((hdomain _).mp h)
        rcases h₁ : w₁ (panByteAlignHOL address) with ⟨cell₁⟩
        rcases h₂ : w₂ (panByteAlignHOL address) with ⟨cell₂⟩
        simp only [hal, hal₁, if_false]
        exact hmemory c hc

theorem byteToBits_eq_toBitVec : byteToBits = UInt8.toBitVec := by
  funext value
  show BitVec.ofNat 8 value.toBitVec.toNat = value.toBitVec
  simp

/-- **Write correspondence.**  The production `ExtCall` byte-array write stays
    `PanSemStateRelExec`-related to the exact `write_bytearray` of the same
    bytes. -/
theorem PanSemStateRelExec.machineWriteBytes
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ} (h : PanSemStateRelExec production exact)
    [DecidablePred exact.memaddrs] (address : RiscV.Word 64) (bytes : List UInt8) :
    PanSemStateRelExec (panSemTotalMachineWriteBytes production address bytes)
      { exact with
        memory := panWriteBytearrayWord8HOL address (bytes.map byteToBits)
          exact.memory exact.memaddrs exact.be } := by
  have hdom := machineDomain_iff h
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  refine ⟨hl, hg, hs, hc, he, ?_, hmd, hsm, hck, hbe, hffi, hb, ht⟩
  intro c hcd
  simp only [panSemTotalMachineWriteBytes]
  rw [panWriteBytearrayHOL_eq_word8_projection, byteToBits_eq_toBitVec, hbe]
  have hdom' : ∀ c', ((production.memaddrs c' &&
      decide (panValueWordDefined production.memory c' = true)) = true) ↔ exact.memaddrs c' := by
    intro c'
    simpa using hdom c'
  rw [panWriteBytearrayWord8HOL_congr address (bytes.map UInt8.toBitVec)
    (panValueWordHOL production.memory) exact.memory _ exact.memaddrs production.be hdom'
    (fun c' hc' => panValueWordHOL_eq_of_memoryRel hm c' ((hmd c').mpr hc')) c
    ((hmd c).mp hcd)]
  cases panWriteBytearrayWord8HOL address (bytes.map UInt8.toBitVec) exact.memory
    exact.memaddrs production.be c
  rfl

/-- The production `callFfi` of an `ExtCall` on any byte-ranged name agrees with
    HOL `call_FFI` on the encoded name and byte lists, assembling the per-outcome
    bridges of `FfiBridge.lean` (empty name, oracle final, length failure,
    success). -/
theorem callFfi_extCall_bridge (state : FfiState σ) (holState : HolFfiState σ)
    (hrel : FfiStateRel state holState) (name : String) (hname : NameRanged name)
    (configuration bytes : List UInt8) :
    FfiResultRel (callFfi state (.extCall name) configuration bytes)
      (callFFIHOL holState (.extCall (ofString name))
        (configuration.map byteToBits) (bytes.map byteToBits)) := by
  by_cases hne : name = ""
  · subst hne
    have hempty : ofString ("" : String) = MlString.implode [] := by
      simp only [ofString]; rfl
    rw [hempty]
    exact callFfi_empty_extCall_bridge state holState hrel configuration bytes
  · cases ho : state.oracle (.extCall name) state.state configuration bytes with
    | final outcome =>
        exact callFfi_extCall_oracleFinal_bridge state holState hrel name hname hne
          configuration bytes outcome ho
    | returned nextState nextBytes =>
        by_cases hlen : nextBytes.length = bytes.length
        · exact callFfi_extCall_success_bridge state holState hrel name hname hne
            configuration bytes nextState nextBytes ho hlen
        · exact callFfi_extCall_lengthFailure_bridge state holState hrel name hname hne
            configuration bytes nextState nextBytes ho hlen

theorem bytesRel_eq_map_byteToBits : ∀ (bytes : List UInt8) (holBytes : List (BitVec 8)),
    BytesRel bytes holBytes → holBytes = bytes.map byteToBits
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [BytesRel] at h
  | _ :: _, [], h => by simp [BytesRel] at h
  | byte :: bytes, holByte :: holBytes, h => by
      simp only [BytesRel, List.map_cons, List.cons.injEq] at h
      obtain ⟨hhead, htail⟩ := h
      rw [List.map_cons, bytesRel_eq_map_byteToBits bytes holBytes htail]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [byteToBits_toNat, hhead]

/-- Production/exact agreement for the `ExtCall` constructor
    (`evaluateHOLFiniteState_extCall_source`, HOL `evaluate_def` `ExtCall`): the
    four operand agreements, non-word failures, the byte-array read
    (`panSemTotalMachineReadBytes_eq`) with both reads failing together, the FFI
    result bridge (`callFfi_extCall_bridge`), `FinalFFI` with `empty_locals`, and
    the returned memory/FFI update (`PanSemStateRelExec.machineWriteBytes`).  No
    premise beyond `PanSemStateRelExec`/`PanSemStateRelExecRanged`. -/
theorem panSemTotalEvaluate_extCall_agree
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    PanSemTotalAgreeAt primitive
      (progOfHOL (.extCall function configuration configurationLength array arrayLength))
      (.extCall function configuration configurationLength array arrayLength)
      production exact := by
  letI : DecidablePred exact.memaddrs := fun a => Classical.propDecidable _
  have agree := fun (e : ExpHOL 64) => by
    have h := evalPanSemStateExp_agree production exact hrel hranged (expOfHOL e)
      (expOfHOL_byteRanged_bridge e)
    simp only [expToHOL_expOfHOL] at h
    exact h
  simp only [PanSemTotalAgreeAt]
  rw [progOfHOL, panSemTotalEvaluate, evaluateHOLFiniteState_extCall_source]
  unfold panSemTotalExtCallClause
  simp only [panSemTotalExprStep]
  rw [← agree configuration, ← agree configurationLength, ← agree array, ← agree arrayLength]
  rcases h1 : evalPanSemStateExp production (expOfHOL configuration) with _ | (a1 | _ | _) <;>
    rcases h2 : evalPanSemStateExp production (expOfHOL configurationLength) with
      _ | (l1 | _ | _) <;>
    rcases h3 : evalPanSemStateExp production (expOfHOL array) with _ | (a2 | _ | _) <;>
    rcases h4 : evalPanSemStateExp production (expOfHOL arrayLength) with _ | (l2 | _ | _) <;>
    simp only [Option.map_some, Option.map_none, panValueToHOL_word, panValueToHOL.eq_2,
      panValueToHOL.eq_3, panSemTotalExtCallStep]
  all_goals first
    | exact ⟨trivial, hrel⟩
    | skip
  rw [panSemTotalMachineReadBytes_eq hrel a1 l1, panSemTotalMachineReadBytes_eq hrel a2 l2]
  rcases hr1 : readBytearrayWordHOL (byteWidth := 8) a1 l1.toNat
      (panMemLoadByteWord8HOL exact.memory exact.memaddrs exact.be) with _ | b1 <;>
    rcases hr2 : readBytearrayWordHOL (byteWidth := 8) a2 l2.toNat
      (panMemLoadByteWord8HOL exact.memory exact.memaddrs exact.be) with _ | b2 <;>
    simp only [Option.map_some, Option.map_none]
  all_goals first
    | exact ⟨trivial, hrel⟩
    | skip
  have hb := callFfi_extCall_bridge production.ffi exact.ffi hrel.2.2.2.2.2.2.2.2.2.2.1
    (toStringOfBytes function) (nameRanged_toStringOfBytes_bridge function)
    (b1.map UInt8.ofBitVec) (b2.map UInt8.ofBitVec)
  simp only [ofString_toStringOfBytes, List.map_map, byteToBits_eq_toBitVec, Function.comp_def,
    List.map_id'] at hb
  revert hb
  cases callFfi production.ffi (FfiName.extCall (toStringOfBytes function))
      (b1.map UInt8.ofBitVec) (b2.map UInt8.ofBitVec) <;>
    cases callFFIHOL exact.ffi (HolFfiName.extCall function) b1 b2 <;>
    intro hb <;> simp only [FfiResultRel] at hb
  · rename_i newFfi newBytes holFfi holBytes
    obtain ⟨hf, hby⟩ := hb
    dsimp only
    rw [bytesRel_eq_map_byteToBits newBytes holBytes hby]
    exact ⟨trivial, (PanSemStateRelExec.machineWriteBytes hrel a2 newBytes).setFfi hf⟩
  · dsimp only
    exact ⟨hb, by
      simpa only [panEmptyLocals, toExact_emptyLocalsHOLFinite] using
        PanSemStateRelExec.emptyLocals hrel⟩

end Flapjack
