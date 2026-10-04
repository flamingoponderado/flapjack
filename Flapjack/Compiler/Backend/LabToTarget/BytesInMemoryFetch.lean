import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity
import Flapjack.Compiler.Backend.LabToTarget.FetchSuccessor
import Flapjack.Compiler.Backend.LabToTarget.FetchValidity
import Flapjack.Compiler.Backend.LabToTarget.Memory
import Flapjack.Compiler.Backend.LabToTarget.Navigation
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Misc.BytesInMem.Imp

/-! Original fetched-instruction byte placement (lab_to_targetProofScript.sml
1155-1258): a fetched source line has a similar, encoding-valid target line
whose bytes lie in memory at its physical position. All code-similarity,
encoding-validity and fetch hypotheses are retained; the machine configuration
is quantified as in the source, which reads only its target configuration. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps

/-- Similar lines agree on being labels; Flapjack infrastructure for the
`is_Label x2 = is_Label x1` step of the original proof. -/
theorem lineSimilar_isLabel {width : Nat} [NeZero width] (x y : LabLineHOL width)
    (h : lineSimilar x y) : isLabelHOL x = isLabelHOL y := by
  cases x <;> cases y <;> simp_all [lineSimilar, isLabelHOL]

/-- A valid line's physical length is its byte count; Flapjack infrastructure
(HOL unfolds `line_ok_def`, `line_length_def` and `line_bytes_def`). -/
theorem lineOk_lineLength {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat) (y : LabLineHOL width)
    (h : lineOk c labs ffis pos y) : lineLength y = (lineBytes y).length := by
  cases y with
  | label _ _ l => simp only [lineOk] at h; simp [lineLength, lineBytes, h.2]
  | asm _ bytes _ => rfl
  | labAsm _ _ bytes _ => rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem progToBytes_lemma {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (code2 code1 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pc : Nat) (i : LabLineHOL width) (pos : Nat) :
    codeSimilar code1 code2 ∧ allEncOk mc.target.config labs ffis pos code2 ∧
      asmFetchAux pc code1 = some i →
    ∃ bs j bs2,
      progToBytes code2 = bs ++ lineBytes j ++ bs2 ∧
      bs.length + pos = posVal pc pos code2 ∧
      bs.length + pos + (lineBytes j).length = posVal (pc + 1) pos code2 ∧
      lineSimilar i j ∧
      lineOk mc.target.config labs ffis (posVal pc pos code2) j := by
  induction code2 generalizing code1 pc pos with
  | nil =>
    rintro ⟨hsim, -, hf⟩
    cases code1 with
    | nil => simp [asmFetchAux] at hf
    | cons _ _ => exact hsim.elim
  | cons sec2 rest2 ih =>
    rcases sec2 with ⟨k, lines2⟩
    cases code1 with
    | nil => rintro ⟨hsim, -, -⟩; exact hsim.elim
    | cons sec1 rest1 =>
    rcases sec1 with ⟨k1, lines1⟩
    rintro ⟨⟨hrest, hlines, hk⟩, henc, hf⟩
    simp only at hlines hk
    induction lines2 generalizing lines1 pc pos with
    | nil =>
      cases hlines
      have he : allEncOk mc.target.config labs ffis pos rest2 := by
        rw [allEncOk] at henc; exact henc.2
      have hf' : asmFetchAux pc rest1 = some i := by simpa only [asmFetchAux] using hf
      obtain ⟨bs, j, bs2, h1, h2, h3, h4, h5⟩ := ih rest1 pc pos ⟨hrest, he, hf'⟩
      refine ⟨bs, j, bs2, ?_, ?_, ?_, h4, ?_⟩
      · simpa only [progToBytes] using h1
      · simpa only [posVal] using h2
      · simpa only [posVal] using h3
      · simpa only [posVal] using h5
    | cons y ys ihl =>
      cases hlines with
      | cons hxy hxs =>
      rename_i x xs
      rw [allEncOk] at henc
      obtain ⟨hy, htail⟩ := henc
      have hlab := lineSimilar_isLabel x y hxy
      have hlen := lineOk_lineLength _ _ _ _ _ hy
      by_cases hl : isLabelHOL y = true
      · have hx : isLabelHOL x = true := hlab ▸ hl
        have hf' : asmFetchAux pc (⟨k1, xs⟩ :: rest1) = some i := by
          simpa only [asmFetchAux, hx, ↓reduceIte] using hf
        obtain ⟨bs, j, bs2, h1, h2, h3, h4, h5⟩ :=
          ihl pc (pos + lineLength y) xs hxs htail hf'
        have hb : lineBytes y = [] := by cases y <;> simp_all [isLabelHOL, lineBytes]
        rw [hb, List.length_nil] at hlen
        rw [hlen, Nat.add_zero] at h2 h3 h5
        refine ⟨bs, j, bs2, ?_, ?_, ?_, h4, ?_⟩
        · simp only [progToBytes, hb, List.nil_append]; exact h1
        · rw [posVal, if_pos hl, hlen, Nat.add_zero]; exact h2
        · rw [posVal, if_pos hl, hlen, Nat.add_zero]; exact h3
        · rw [posVal, if_pos hl, hlen, Nat.add_zero]; exact h5
      · have hx : ¬ isLabelHOL x = true := hlab ▸ hl
        cases pc with
        | zero =>
          have hi : i = x := by
            simpa only [asmFetchAux, hx, ↓reduceIte, Bool.false_eq_true,
              Option.some.injEq, eq_comm] using hf
          subst hi
          have hz := posVal_zeroAt mc.target.config labs ffis _ _ (pos + lineLength y) htail
          refine ⟨[], y, progToBytes (⟨k, ys⟩ :: rest2), ?_, ?_, ?_, hxy, ?_⟩
          · simp [progToBytes]
          · simp [posVal, hl]
          · rw [hlen] at hz
            simp only [posVal, if_neg hl, Nat.add_one_sub_one, hlen]
            simp [hz]
          · simpa [posVal, hl] using hy
        | succ n =>
          have hf' : asmFetchAux n (⟨k1, xs⟩ :: rest1) = some i := by
            simpa only [asmFetchAux, hx, ↓reduceIte, Bool.false_eq_true,
              Nat.add_one_ne_zero, Nat.add_one_sub_one] using hf
          obtain ⟨bs, j, bs2, h1, h2, h3, h4, h5⟩ :=
            ihl n (pos + lineLength y) xs hxs htail hf'
          refine ⟨lineBytes y ++ bs, j, bs2, ?_, ?_, ?_, h4, ?_⟩
          · simp only [progToBytes, h1, List.append_assoc]
          · simp only [posVal, if_neg hl, Nat.add_one_ne_zero, ↓reduceIte,
              Nat.add_one_sub_one, List.length_append]
            omega
          · simp only [posVal, if_neg hl, Nat.add_one_ne_zero, ↓reduceIte,
              Nat.add_one_sub_one, List.length_append]
            omega
          · simpa only [posVal, if_neg hl, Nat.add_one_ne_zero, ↓reduceIte,
              Nat.add_one_sub_one] using h5

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (code1 code2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pc : Nat) (i : LabLineHOL width) (p : BitVec width) (m : BitVec width → BitVec 8)
    (dm dm1 : BitVec width → Prop) :
    codeSimilar code1 code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      asmFetchAux pc code1 = some i ∧ bytesInMemHOL p (progToBytes code2) m dm dm1 →
    ∃ j,
      bytesInMemHOL (p + BitVec.ofNat width (posVal pc 0 code2)) (lineBytes j) m dm dm1 ∧
      lineOk mc.target.config labs ffis (posVal pc 0 code2) j ∧
      posVal (pc + 1) 0 code2 = posVal pc 0 code2 + (lineBytes j).length ∧
      lineSimilar i j := by
  rintro ⟨hsim, henc, hf, hmem⟩
  obtain ⟨bs, j, bs2, h1, h2, h3, h4, h5⟩ :=
    progToBytes_lemma mc labs ffis code2 code1 pc i 0 ⟨hsim, henc, hf⟩
  rw [h1, bytesInMem_append, bytesInMem_append] at hmem
  simp only [Nat.add_zero] at h2 h3
  refine ⟨j, ?_, h5, by omega, h4⟩
  rw [← h2]; exact hmem.1.2

/-- The fetched-line byte placement specialised to a labSem state; Flapjack
infrastructure shared by the original per-instruction lemmas, which each
begin by instantiating `IMP_bytes_in_memory` at `s1.code` and `s1.pc`. -/
theorem imp_bytesInMemory_state {width : Nat} [NeZero width] {S Q C F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width C F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (i : LabLineHOL width)
    (h : codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some i) :
    ∃ j,
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) (lineBytes j) t1.mem
        t1.memDomain (fun a => s1.memDomain a = true) ∧
      lineOk mc.target.config labs ffis (posVal s1.pc 0 code2) j ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + (lineBytes j).length ∧
      lineSimilar i j :=
  imp_bytesInMemory mc labs ffis s1.code code2 s1.pc i p t1.mem t1.memDomain _
    ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

/-- A NOP-padded encoding places its leading instruction encoding in memory;
Flapjack infrastructure for the `enc_with_nop_thm`/`bytes_in_memory_APPEND`
steps of the original proofs. -/
theorem bytesInMem_encWithNop {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (instruction : HolAsm width) (bytes : List (BitVec 8)) (a : BitVec width)
    (m : BitVec width → BitVec 8) (dm dm1 : BitVec width → Prop)
    (henc : encWithNop c.encode instruction bytes) (hmem : bytesInMemHOL a bytes m dm dm1) :
    bytesInMemoryHOL a (c.encode instruction) m dm := by
  obtain ⟨n, rfl⟩ := (encWithNop_iff _ _ _).mp henc
  exact ((bytesInMemory_append _ _ _ _ _).mp (bytesInMem_impliesMemory _ _ _ _ _ hmem)).1

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_jumpReg {width : Nat} [NeZero width] {S Q C F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width C F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (r1 : Nat) (l : List (BitVec 8)) (n : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.asm (.asmi (.jumpReg r1)) l n) →
    bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2))
      (mc.target.config.encode (.jumpReg r1)) t1.mem t1.memDomain ∧
    asmOkExact (.jumpReg r1) mc.target.config = true := by
  intro h
  obtain ⟨j, hmem, hok, -, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | labAsm => exact hsim.elim
  | asm b bytes len =>
    simp only [lineSimilar] at hsim
    subst hsim
    simp only [lineOk, cbwToAsmHOL] at hok
    exact ⟨bytesInMem_encWithNop _ _ _ _ _ _ _ hok.1 hmem, hok.2.2⟩

/-- Label-target lines are valid only through a successful label lookup;
Flapjack infrastructure for the `lab_lookup_IMP` steps of the original
`Jump`/`JumpCmp`/`LocValue` lemmas. -/
theorem lineOk_labelTarget {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (a : AsmWithLab HolCmp (HolRegImm width) MlString) (w : BitVec width)
    (bytes : List (BitVec 8)) (len : Nat)
    (ha : (∃ t, a = .jump t) ∨ (∃ cmp r ri t, a = .jumpCmp cmp r ri t) ∨
      (∃ r t, a = .locValue r t))
    (h : lineOk c labs ffis pos (.labAsm a w bytes len)) :
    let w1 := BitVec.ofNat width (findPos (getLabel a) labs) - BitVec.ofNat width pos
    encWithNop c.encode (labInst w1 a) bytes ∧ bytes.length = len ∧
      asmOkExact (labInst w1 a) c = true := by
  rcases ha with ⟨t, rfl⟩ | ⟨cmp, r, ri, t, rfl⟩ | ⟨r, t, rfl⟩ <;>
  · rcases t with ⟨l1, l2⟩
    simp only [lineOk, getLabel] at h
    split at h
    · exact h.elim
    · next x hx =>
      simp only [getLabel, labLookup_implies_findPos l1 l2 labs x hx]
      exact h

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_jump {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (jtarget : Lab) (l : BitVec width) (bytes : List (BitVec 8))
    (n : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.labAsm (.jump jtarget) l bytes n) →
    ∃ tt enc,
      tt = BitVec.ofNat width (findPos jtarget labs) -
        BitVec.ofNat width (posVal s1.pc 0 code2) ∧
      enc = mc.target.config.encode (.jump tt) ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) enc t1.mem
        t1.memDomain ∧
      asmOkExact (.jump tt) mc.target.config = true := by
  intro h
  obtain ⟨j, hmem, hok, -, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | asm => exact hsim.elim
  | labAsm a w bytes' len =>
    simp only [lineSimilar] at hsim
    subst hsim
    have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inl ⟨jtarget, rfl⟩) hok
    exact ⟨_, _, rfl, rfl, bytesInMem_encWithNop _ _ _ _ _ _ _ hv.1 hmem, hv.2.2⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_jumpCmp {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (cmp : HolCmp) (rr : Nat) (ri : HolRegImm width) (jtarget : Lab)
    (l : BitVec width) (bytes : List (BitVec 8)) (n : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.labAsm (.jumpCmp cmp rr ri jtarget) l bytes n) →
    ∃ tt enc,
      tt = BitVec.ofNat width (findPos jtarget labs) -
        BitVec.ofNat width (posVal s1.pc 0 code2) ∧
      enc = mc.target.config.encode (.jumpCmp cmp rr ri tt) ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) enc t1.mem
        t1.memDomain ∧
      asmOkExact (.jumpCmp cmp rr ri tt) mc.target.config = true := by
  intro h
  obtain ⟨j, hmem, hok, -, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | asm => exact hsim.elim
  | labAsm a w bytes' len =>
    simp only [lineSimilar] at hsim
    subst hsim
    have hv := lineOk_labelTarget _ _ _ _ _ _ _ _
      (Or.inr (Or.inl ⟨cmp, rr, ri, jtarget, rfl⟩)) hok
    exact ⟨_, _, rfl, rfl, bytesInMem_encWithNop _ _ _ _ _ _ _ hv.1 hmem, hv.2.2⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_jumpCmp_1 {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (cmp : HolCmp) (rr : Nat) (ri : HolRegImm width) (jtarget : Lab)
    (l : BitVec width) (bytes : List (BitVec 8)) (n : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.labAsm (.jumpCmp cmp rr ri jtarget) l bytes n) →
    ∃ tt bytes,
      tt = BitVec.ofNat width (findPos jtarget labs) -
        BitVec.ofNat width (posVal s1.pc 0 code2) ∧
      encWithNop mc.target.config.encode (.jumpCmp cmp rr ri tt) bytes ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes.length ∧
      asmOkExact (.jumpCmp cmp rr ri tt) mc.target.config = true := by
  intro h
  obtain ⟨j, hmem, hok, hpos, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | asm => exact hsim.elim
  | labAsm a w bytes' len =>
    simp only [lineSimilar] at hsim
    subst hsim
    have hv := lineOk_labelTarget _ _ _ _ _ _ _ _
      (Or.inr (Or.inl ⟨cmp, rr, ri, jtarget, rfl⟩)) hok
    exact ⟨_, bytes', rfl, hv.1, bytesInMem_impliesMemory _ _ _ _ _ hmem, hpos, hv.2.2⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_call {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (ww : Lab) (l : BitVec width) (bytes : List (BitVec 8)) (n : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.labAsm (.call ww) l bytes n) → False := by
  intro h
  obtain ⟨j, -, hok, -, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | asm => exact hsim.elim
  | labAsm a w bytes' len =>
    simp only [lineSimilar] at hsim
    subst hsim
    simp [lineOk] at hok

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_locValue {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (reg l1 l2 : Nat) (l : BitVec width) (bytes : List (BitVec 8))
    (n : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.labAsm (.locValue reg (.lab l1 l2)) l bytes n) →
    ∃ tt bytes,
      tt = BitVec.ofNat width (findPos (.lab l1 l2) labs) -
        BitVec.ofNat width (posVal s1.pc 0 code2) ∧
      encWithNop mc.target.config.encode (.loc reg tt) bytes ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes.length ∧
      asmOkExact (.loc reg tt) mc.target.config = true := by
  intro h
  obtain ⟨j, hmem, hok, hpos, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | asm => exact hsim.elim
  | labAsm a w bytes' len =>
    simp only [lineSimilar] at hsim
    subst hsim
    have hv := lineOk_labelTarget _ _ _ _ _ _ _ _
      (Or.inr (Or.inr ⟨reg, .lab l1 l2, rfl⟩)) hok
    exact ⟨_, bytes', rfl, hv.1, bytesInMem_impliesMemory _ _ _ _ _ hmem, hpos, hv.2.2⟩

/-- Shared shape of the original `Inst` and `Cbw` lemmas: an `Asm` line's
padded encoding, both memory views, successor position and validity;
Flapjack infrastructure. -/
theorem imp_bytesInMemory_asmLine {width : Nat} [NeZero width] {S Q C F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width C F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (b : AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (bytes : List (BitVec 8)) (len : Nat)
    (h : codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.asm b bytes len)) :
    ∃ bytes,
      encWithNop mc.target.config.encode (cbwToAsmHOL b) bytes ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain ∧
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain (fun a => s1.memDomain a = true) ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes.length ∧
      asmOkExact (cbwToAsmHOL b) mc.target.config = true := by
  obtain ⟨j, hmem, hok, hpos, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | labAsm => exact hsim.elim
  | asm b' bytes' len' =>
    simp only [lineSimilar] at hsim
    subst hsim
    simp only [lineOk] at hok
    exact ⟨bytes', hok.1, bytesInMem_impliesMemory _ _ _ _ _ hmem, hmem, hpos, hok.2.2⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_inst {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (i : HolInst width) (bytes : List (BitVec 8)) (len : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.asm (.asmi (.inst i)) bytes len) →
    ∃ bytes,
      encWithNop mc.target.config.encode (.inst i) bytes ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain ∧
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain (fun a => s1.memDomain a = true) ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes.length ∧
      asmOkExact (.inst i) mc.target.config = true :=
  fun h => imp_bytesInMemory_asmLine mc labs ffis s1 code2 p t1 _ bytes len h

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_cbw {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (r1 r2 : Nat) (bytes : List (BitVec 8)) (len : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.asm (.cbw r1 r2) bytes len) →
    ∃ bytes,
      encWithNop mc.target.config.encode (.inst (.mem .store8 r2 (.addr r1 0))) bytes ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain ∧
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain (fun a => s1.memDomain a = true) ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes.length ∧
      asmOkExact (.inst (.mem .store8 r2 (.addr r1 0))) mc.target.config = true :=
  fun h => imp_bytesInMemory_asmLine mc labs ffis s1 code2 p t1 _ bytes len h

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_callFFI {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (name : MlString) (l : BitVec width) (bytes : List (BitVec 8))
    (n : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.labAsm (.callFFI name) l bytes n) →
    ∃ tt enc,
      tt = 0 - BitVec.ofNat width (posVal s1.pc 0 code2 +
        (3 + getFfiIndex ffis (.extCall name)) * ffiOffset) ∧
      enc = mc.target.config.encode (.jump tt) ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) enc t1.mem
        t1.memDomain ∧
      asmOkExact (.jump tt) mc.target.config = true := by
  intro h
  obtain ⟨j, hmem, hok, -, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | asm => exact hsim.elim
  | labAsm a w bytes' len =>
    simp only [lineSimilar] at hsim
    subst hsim
    simp only [lineOk] at hok
    exact ⟨_, _, rfl, rfl, bytesInMem_encWithNop _ _ _ _ _ _ _ hok.1 hmem, hok.2.2⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_halt {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (l : BitVec width) (bytes : List (BitVec 8)) (n : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.labAsm .halt l bytes n) →
    ∃ tt enc,
      tt = 0 - BitVec.ofNat width (posVal s1.pc 0 code2 + ffiOffset) ∧
      enc = mc.target.config.encode (.jump tt) ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) enc t1.mem
        t1.memDomain ∧
      asmOkExact (.jump tt) mc.target.config = true := by
  intro h
  obtain ⟨j, hmem, hok, -, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | asm => exact hsim.elim
  | labAsm a w bytes' len =>
    simp only [lineSimilar] at hsim
    subst hsim
    simp only [lineOk] at hok
    exact ⟨_, _, rfl, rfl, bytesInMem_encWithNop _ _ _ _ _ _ _ hok.1 hmem, hok.2.2⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_install {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (c : BitVec width) (l : List (BitVec 8)) (n : Nat) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some (.labAsm .install c l n) →
    ∃ tt enc,
      tt = 0 - BitVec.ofNat width (posVal s1.pc 0 code2 + 2 * ffiOffset) ∧
      enc = mc.target.config.encode (.jump tt) ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) enc t1.mem
        t1.memDomain ∧
      asmOkExact (.jump tt) mc.target.config = true := by
  intro h
  obtain ⟨j, hmem, hok, -, hsim⟩ := imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ h
  cases j with
  | label => exact hsim.elim
  | asm => exact hsim.elim
  | labAsm a w bytes' len =>
    simp only [lineSimilar] at hsim
    subst hsim
    simp only [lineOk] at hok
    exact ⟨_, _, rfl, rfl, bytesInMem_encWithNop _ _ _ _ _ _ _ hok.1 hmem, hok.2.2⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetchAux_posVal_lengthEq {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (bytes' : List (BitVec 8)) (pc n : Nat) (code2 : LabProgHOL width)
    (line : LabLineHOL width) :
    asmFetchAux pc code2 = some line ∧ allEncOk conf labs ffis n code2 ∧
      posVal (pc + 1) n code2 = bytes'.length + posVal pc n code2 →
    (lineBytes line).length = bytes'.length := by
  rintro ⟨hf, henc, hpos⟩
  have := asmFetchAux_posVal_successor pc n code2 n conf labs ffis line ⟨henc, hf⟩
  omega

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_bytesInMemory_shareMem {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (mop : HolMemop) (r : Nat) (ad : HolAddr width)
    (l : List (BitVec 8)) (n : Nat) :
    asmFetchAux s1.pc s1.code = some (.asm (.shareMem mop r ad) l n) ∧
      codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) →
    ∃ bytes,
      asmFetchAux s1.pc code2 = some (.asm (.shareMem mop r ad) bytes bytes.length) ∧
      encWithNop mc.target.config.encode (.inst (.mem mop r ad)) bytes ∧
      bytesInMemoryHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain ∧
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes t1.mem
        t1.memDomain (fun a => s1.memDomain a = true) ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes.length ∧
      asmOkExact (.inst (.mem mop r ad)) mc.target.config = true := by
  rintro ⟨hf, hsim, henc, hmem⟩
  obtain ⟨j, hmemj, hok, hpos, hsimj⟩ :=
    imp_bytesInMemory_state mc labs ffis s1 code2 p t1 _ ⟨hsim, henc, hmem, hf⟩
  cases j with
  | label => exact hsimj.elim
  | labAsm => exact hsimj.elim
  | asm b bytes len =>
  simp only [lineSimilar] at hsimj
  subst hsimj
  simp only [lineOk, cbwToAsmHOL] at hok
  obtain ⟨hwith, hlen, hasm⟩ := hok
  -- The target fetch at the same index is a similar, valid `Asm` line.
  have hrel := codeSimilar_asmFetchAux s1.pc s1.code code2 hsim
  rw [hf] at hrel
  obtain ⟨y0, hy0, hsim0⟩ : ∃ y0, asmFetchAux s1.pc code2 = some y0 ∧
      lineSimilar (.asm (.shareMem mop r ad) l n) y0 := by
    revert hrel
    cases asmFetchAux s1.pc code2 with
    | none => intro h; cases h
    | some y0 => intro h; cases h with | some h => exact ⟨y0, rfl, h⟩
  have hok0 := allEncOk_fetch_lineOk mc.target.config labs ffis s1.pc 0 code2 y0 ⟨henc, hy0⟩
  cases y0 with
  | label => exact hsim0.elim
  | labAsm => exact hsim0.elim
  | asm b0 bytes0 len0 =>
  simp only [lineSimilar] at hsim0
  subst hsim0
  simp only [lineOk, cbwToAsmHOL] at hok0
  have hl0 := asmFetchAux_posVal_lengthEq mc.target.config labs ffis bytes s1.pc 0 code2 _
    ⟨hy0, henc, by rw [hpos]; simp [lineBytes, Nat.add_comm]⟩
  simp only [lineBytes] at hl0
  -- Equal-length padded encodings of the same instruction coincide.
  have hbytes : bytes0 = bytes := by
    obtain ⟨k0, hk0⟩ := (encWithNop_iff _ _ _).mp hok0.1
    obtain ⟨k, hk⟩ := (encWithNop_iff _ _ _).mp hwith
    by_cases hz : (mc.target.config.encode (.inst .skip)).length = 0
    · have hnil : mc.target.config.encode (.inst .skip) = [] := List.length_eq_zero_iff.mp hz
      rw [hk0, hk, hnil]; simp
    · have hl : (List.replicate k0 (mc.target.config.encode (.inst .skip))).flatten.length =
          (List.replicate k (mc.target.config.encode (.inst .skip))).flatten.length := by
        rw [hk0, hk] at hl0; simpa using hl0
      have hmul : k0 * (mc.target.config.encode (.inst .skip)).length =
          k * (mc.target.config.encode (.inst .skip)).length := by simpa using hl
      have : k0 = k := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hz) hmul
      rw [hk0, hk, this]
  subst hbytes
  refine ⟨bytes0, ?_, hwith, bytesInMem_impliesMemory _ _ _ _ _ hmemj, hmemj, hpos, hasm⟩
  rw [hy0, hok0.2.1]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "bytes_in_mem_IMP_memory" (words_as_type_indexed_bitvec)]
theorem bytesInMem_impliesMemory_change {width : Nat} [NeZero width]
    (dm1 : BitVec width → Prop) (m m1 : BitVec width → BitVec 8) (dm : BitVec width → Prop)
    (xs : List (BitVec 8)) (a : BitVec width) :
    (∀ a, ¬ dm1 a → m a = m1 a) → bytesInMemHOL a xs m dm dm1 →
      bytesInMemoryHOL a xs m1 dm := by
  intro hm
  induction xs generalizing a with
  | nil => intro _; trivial
  | cons x xs ih =>
    rintro ⟨hd, hx, hv, ht⟩
    exact ⟨(hm a hx).symm.trans hv, hd, ih (a + 1) ht⟩

end Flapjack.Compiler.Backend.LabToTarget
