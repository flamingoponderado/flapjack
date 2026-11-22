module

public import Flapjack.Compiler.Backend.DataToWord.Compile
public import Flapjack.Compiler.Backend.DataToWord.Proofs.StubFacts
public import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileConventions.Output

@[expose] public section

set_option autoImplicit false

/-! Label preservation of the whole data-to-word compiler
(`data_to_wordProofScript.sml`, `data_to_word_compile_lab_pres`). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Encoders.Asm

/-- Pairing the entries of two tables with the same keys whose label lists are
related pointwise (Flapjack infrastructure). -/
theorem forall₂_labelsRel_mem {width : Nat} :
    ∀ (A B : List (Nat × Nat × WordLangProgHOL (BitVec width))),
      B.map Prod.fst = A.map Prod.fst →
      List.Forall₂ labelsRel (A.map fun p => extractLabels p.2.2)
        (B.map fun p => extractLabels p.2.2) →
      ∀ e ∈ B, ∃ d ∈ A, d.1 = e.1 ∧ labelsRel (extractLabels d.2.2) (extractLabels e.2.2) := by
  intro A
  induction A with
  | nil => intro B _ h; cases B <;> simp_all
  | cons a A ih =>
    intro B hk h e he
    cases B with
    | nil => simp at he
    | cons b B =>
      simp only [List.map_cons, List.cons.injEq] at hk
      simp only [List.map_cons, List.forall₂_cons] at h
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨a, by simp, hk.1.symm, h.1⟩
      · obtain ⟨d, hd, h1, h2⟩ := ih B hk.2 h.2 e he
        exact ⟨d, by simp [hd], h1, h2⟩

/-- Exact HOL `data_to_word_compile_lab_pres`. The `let (c, p)` pattern binds
the compiler's result pair (the unused column list is `_c`), the inner `EVERY`s
are membership foralls, `ALL_DISTINCT` is `List.Nodup` and `extract_labels` is
the reviewed `extractLabels`. As in HOL, the stub table is taken at the input
`data_conf`; its keys do not depend on the floating-point flags `compile`
sets. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml"
  "data_to_word_compile_lab_pres" (words_as_type_indexed_bitvec)]
theorem dataToWord_compileLabPres {width : Nat} [NeZero width] (dataConf : Config)
    (wordConf : WordToWord.Config) (asmConf : AsmConfigExact width)
    (prog : List (Nat × Nat × DataLang.Prog)) :
    let (_c, p) := compile dataConf wordConf asmConf prog
    p.map Prod.fst =
        (stubs dataConf : List (Nat × Nat × WordLangProgHOL (BitVec width))).map Prod.fst ++
          prog.map Prod.fst ∧
      ∀ e ∈ p,
        let labs := extractLabels e.2.2
        (∀ q ∈ labs, q.1 = e.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧ labs.Nodup := by
  simp only [compile]
  generalize hdc : ({ dataConf with
    hasFpOps := decide (1 < asmConf.fpRegCount)
    hasFpTern := decide (asmConf.isa = .armv7 ∧ 2 < asmConf.fpRegCount) } : Config) = dc
  generalize hdp : stubs (width := width) dc ++ prog.map (compilePart dc) = datap
  have hgood : ∀ d ∈ datap, (∀ q ∈ extractLabels d.2.2, q.1 = d.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧
      (extractLabels d.2.2).Nodup ∧ noShareInstSubprogsHOL d.2.2 = true := by
    rw [← hdp]
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · have := stubs_good dc d hd
      exact ⟨this.1.1, this.1.2, this.2⟩
    · obtain ⟨⟨name, arity, body⟩, _, rfl⟩ := List.mem_map.1 hd
      simp only [compilePart]
      have hl := dataToWord_labPresLem (width := width) dc name 2 body (by decide)
      rcases hc : compileControl (width := width) dc name 2 body with ⟨cp, l'⟩
      rw [hc] at hl
      obtain ⟨_, hl2, hl3⟩ := hl
      refine ⟨fun q hq => ?_, hl3, comp_noShareInst dc name 2 body cp l' hc⟩
      have := hl2 q hq
      exact ⟨this.1, by omega, by omega⟩
  obtain ⟨hfst, hrel, -⟩ :=
    WordToWord.CompileConventions.compileToWordConventions wordConf asmConf datap
    (fun d hd => .inl (hgood d hd).2.2)
  rcases hout : WordToWord.compile wordConf asmConf datap with ⟨c, p⟩
  rw [hout] at hfst hrel
  refine ⟨?_, ?_⟩
  · simp only at hfst ⊢
    rw [hfst, ← hdp, List.map_append, stubsFst_eq, stubsFst_eq, List.map_map]
    congr 1
  · intro e he
    obtain ⟨d, hd, h1, h2⟩ := forall₂_labelsRel_mem datap p hfst hrel e he
    obtain ⟨g1, g2, -⟩ := hgood d hd
    refine ⟨fun q hq => ?_, h2.1 g2⟩
    have := g1 q (h2.2 q hq)
    rw [h1] at this
    exact this

end Flapjack.Compiler.Backend.DataToWord.Proofs
