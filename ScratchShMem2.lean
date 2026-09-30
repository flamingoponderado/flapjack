import Flapjack.Pancake.Proofs.CrepInline

open Flapjack CrepSemHOLState

namespace Flapjack.CrepInlineExact

def SameExceptCode {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ) : Prop :=
  crepInlineStateRelCodeExact s t ∧ s.locals = t.locals

theorem same_setVar {width : Nat} [NeZero width] {σ : Type} (name : Nat)
    (value : HolWordLab width) (s t : CrepSemHOLState width σ) (h : SameExceptCode s t) :
    SameExceptCode (CrepSemHOLState.setVar name value s)
      (CrepSemHOLState.setVar name value t) := by
  obtain ⟨hst, hl⟩ := h
  obtain ⟨hg, hmem, hma, hsh, hcl, hbe, hffi, hba, hta⟩ := hst
  refine ⟨⟨hg, hmem, hma, hsh, hcl, hbe, hffi, hba, hta⟩, ?_⟩
  show (CrepSemHOLState.setVar name value s).locals =
    (CrepSemHOLState.setVar name value t).locals
  simp only [CrepSemHOLState.setVar, hl]

theorem same_emptyLocals {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ) (h : SameExceptCode s t) :
    SameExceptCode (CrepSemHOLState.emptyLocals s) (CrepSemHOLState.emptyLocals t) := by
  obtain ⟨hst, hl⟩ := h
  obtain ⟨hg, hmem, hma, hsh, hcl, hbe, hffi, hba, hta⟩ := hst
  refine ⟨⟨hg, hmem, hma, hsh, hcl, hbe, hffi, hba, hta⟩, ?_⟩
  show (CrepSemHOLState.emptyLocals s).locals = (CrepSemHOLState.emptyLocals t).locals
  simp only [CrepSemHOLState.emptyLocals]

theorem same_setFfi {width : Nat} [NeZero width] {σ : Type} (newFfi : HolFfiState σ)
    (s t : CrepSemHOLState width σ) (h : SameExceptCode s t) :
    SameExceptCode { s with ffi := newFfi } { t with ffi := newFfi } := by
  obtain ⟨hst, hl⟩ := h
  obtain ⟨hg, hmem, hma, hsh, hcl, hbe, hffi, hba, hta⟩ := hst
  refine ⟨⟨hg, hmem, hma, hsh, hcl, hbe, rfl, hba, hta⟩, ?_⟩
  show ({ s with ffi := newFfi } : CrepSemHOLState width σ).locals =
    ({ t with ffi := newFfi } : CrepSemHOLState width σ).locals
  simp only [hl]

theorem crepShMemLoadExactHOL_same {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (addr : BitVec width) (nb : Nat)
    (s t : CrepSemHOLState width σ) (h : SameExceptCode s t) :
    (@crepShMemLoadExactHOL width _ σ name addr nb s
        (fun a => Classical.propDecidable (s.shMemaddrs a))).1 =
        (@crepShMemLoadExactHOL width _ σ name addr nb t
          (fun a => Classical.propDecidable (t.shMemaddrs a))).1 ∧
      SameExceptCode
        (@crepShMemLoadExactHOL width _ σ name addr nb s
          (fun a => Classical.propDecidable (s.shMemaddrs a))).2
        (@crepShMemLoadExactHOL width _ σ name addr nb t
          (fun a => Classical.propDecidable (t.shMemaddrs a))).2 := by
  obtain ⟨⟨hg, hmem, hma, hsh, hcl, hbe, hffi, hba, hta⟩, hl⟩ := h
  have hbase : SameExceptCode s t := ⟨⟨hg, hmem, hma, hsh, hcl, hbe, hffi, hba, hta⟩, hl⟩
  have hA : s.shMemaddrs addr = t.shMemaddrs addr := congrFun hsh addr
  have hB : s.shMemaddrs (panByteAlignHOL addr) =
      t.shMemaddrs (panByteAlignHOL addr) := congrFun hsh _
  simp only [crepShMemLoadExactHOL]
  by_cases h0 : nb = 0
  · rw [if_pos h0, if_pos h0]
    by_cases hc : s.shMemaddrs addr
    · rw [if_pos hc, if_pos (hA ▸ hc), hffi]
      cases callFFIHOL t.ffi (HolFfiName.sharedMem HolShmemOp.mappedRead)
          [BitVec.ofNat 8 nb] ((crepClockWordToBytes addr).map UInt8.toBitVec) with
      | final e => exact ⟨rfl, same_emptyLocals s t hbase⟩
      | ret nf _ => exact ⟨rfl, same_setFfi nf _ _ (same_setVar name _ s t hbase)⟩
    · rw [if_neg hc, if_neg (fun ht => hc (hA ▸ ht))]
      exact ⟨rfl, hbase⟩
  · rw [if_neg h0, if_neg h0]
    by_cases hc : s.shMemaddrs (panByteAlignHOL addr)
    · rw [if_pos hc, if_pos (hB ▸ hc), hffi]
      cases callFFIHOL t.ffi (HolFfiName.sharedMem HolShmemOp.mappedRead)
          [BitVec.ofNat 8 nb] ((crepClockWordToBytes addr).map UInt8.toBitVec) with
      | final e => exact ⟨rfl, same_emptyLocals s t hbase⟩
      | ret nf _ => exact ⟨rfl, same_setFfi nf _ _ (same_setVar name _ s t hbase)⟩
    · rw [if_neg hc, if_neg (fun ht => hc (hB ▸ ht))]
      exact ⟨rfl, hbase⟩

theorem crepShMemStoreExactHOL_same {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (addr : BitVec width) (nb : Nat)
    (s t : CrepSemHOLState width σ) (h : SameExceptCode s t) :
    (@crepShMemStoreExactHOL width _ σ name addr nb s
        (fun a => Classical.propDecidable (s.shMemaddrs a))).1 =
        (@crepShMemStoreExactHOL width _ σ name addr nb t
          (fun a => Classical.propDecidable (t.shMemaddrs a))).1 ∧
      SameExceptCode
        (@crepShMemStoreExactHOL width _ σ name addr nb s
          (fun a => Classical.propDecidable (s.shMemaddrs a))).2
        (@crepShMemStoreExactHOL width _ σ name addr nb t
          (fun a => Classical.propDecidable (t.shMemaddrs a))).2 := by
  obtain ⟨⟨hg, hmem, hma, hsh, hcl, hbe, hffi, hba, hta⟩, hl⟩ := h
  have hbase : SameExceptCode s t := ⟨⟨hg, hmem, hma, hsh, hcl, hbe, hffi, hba, hta⟩, hl⟩
  have hA : s.shMemaddrs addr = t.shMemaddrs addr := congrFun hsh addr
  have hB : s.shMemaddrs (panByteAlignHOL addr) =
      t.shMemaddrs (panByteAlignHOL addr) := congrFun hsh _
  simp only [crepShMemStoreExactHOL]
  rw [hl]
  cases hloc : t.locals.lookup name with
  | none =>
      dsimp only
      exact ⟨rfl, hbase⟩
  | some v =>
      cases v with
      | word value =>
          dsimp only
          by_cases h0 : nb = 0
          · rw [if_pos h0, if_pos h0]
            by_cases hc : s.shMemaddrs addr
            · rw [if_pos hc, if_pos (hA ▸ hc), hffi]
              cases callFFIHOL t.ffi (HolFfiName.sharedMem HolShmemOp.mappedWrite)
                  [BitVec.ofNat 8 nb]
                  ((crepClockWordToBytes value ++ crepClockWordToBytes addr).map
                    UInt8.toBitVec) with
              | final e => exact ⟨rfl, hbase⟩
              | ret nf _ =>
                  exact ⟨rfl, ⟨⟨hg, hmem, hma, hsh, hcl, hbe, rfl, hba, hta⟩, rfl⟩⟩
            · rw [if_neg hc, if_neg (fun ht => hc (hA ▸ ht))]
              exact ⟨rfl, hbase⟩
          · rw [if_neg h0, if_neg h0]
            by_cases hc : s.shMemaddrs (panByteAlignHOL addr)
            · rw [if_pos hc, if_pos (hB ▸ hc), hffi]
              cases callFFIHOL t.ffi (HolFfiName.sharedMem HolShmemOp.mappedWrite)
                  [BitVec.ofNat 8 nb]
                  (((crepClockWordToBytes value).take nb ++
                    crepClockWordToBytes addr).map UInt8.toBitVec) with
              | final e => exact ⟨rfl, hbase⟩
              | ret nf _ =>
                  exact ⟨rfl, ⟨⟨hg, hmem, hma, hsh, hcl, hbe, rfl, hba, hta⟩, rfl⟩⟩
            · rw [if_neg hc, if_neg (fun ht => hc (hB ▸ ht))]
              exact ⟨rfl, hbase⟩

theorem crepShMemOpExactHOL_same {width : Nat} [NeZero width] {σ : Type}
    (op : WordMemOp) (name : Nat) (addr : BitVec width)
    (s t : CrepSemHOLState width σ) (h : SameExceptCode s t) :
    (@crepShMemOpExactHOL width _ σ op name addr s
        (fun a => Classical.propDecidable (s.shMemaddrs a))).1 =
        (@crepShMemOpExactHOL width _ σ op name addr t
          (fun a => Classical.propDecidable (t.shMemaddrs a))).1 ∧
      SameExceptCode
        (@crepShMemOpExactHOL width _ σ op name addr s
          (fun a => Classical.propDecidable (s.shMemaddrs a))).2
        (@crepShMemOpExactHOL width _ σ op name addr t
          (fun a => Classical.propDecidable (t.shMemaddrs a))).2 := by
  have hload (nb : Nat) := crepShMemLoadExactHOL_same name addr nb s t h
  have hstore (nb : Nat) := crepShMemStoreExactHOL_same name addr nb s t h
  cases op <;> simp only [crepShMemOpExactHOL] <;>
    first
      | exact hload 0 | exact hload 1 | exact hload 2 | exact hload 4
      | exact hstore 0 | exact hstore 1 | exact hstore 2 | exact hstore 4

end Flapjack.CrepInlineExact
