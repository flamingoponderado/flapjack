module

public import Flapjack.Pancake.WordConvs.LabelSafety
public import Flapjack.Pancake.Proofs.WordConvs.GoodHandlersTail
public import Flapjack.Pancake.Proofs.WordConvs.SSACodeLabels
public import Flapjack.Pancake.Proofs.WordConvs.InstSelectCodeLabels
public import Flapjack.Pancake.Proofs.WordConvs.ThreeToTwoCodeLabels
public import Flapjack.Pancake.Proofs.WordConvs.UnreachCodeLabels
public import Flapjack.Pancake.Proofs.WordConvs.WordAlloc
public import Flapjack.Pancake.Proofs.WordConvs.WordCse
public import Flapjack.Pancake.Proofs.WordConvs.CopyProp
public import Flapjack.Pancake.Proofs.WordConvs.RemoveDead
public import Flapjack.Pancake.Proofs.WordConvs.RemoveMustTerminate
public import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.CompileExp

@[expose] public section

/-!
Whole-program code-label safety through `word_to_word`, the
`word_good_code_labels_word_to_word_incr_helper` / `_incr` /
`_word_to_word` family of `wordConvsProofScript.sml:3037-3102`. Kept in a
sibling module so the `Set`-based statements stay out of the `word_to_word`
passes' environments.
-/

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Backend.WordUnreach
  Flapjack.Compiler.Encoders.Asm

/-- Flapjack infrastructure: HOL's per-element step of
`word_good_code_labels_word_to_word_incr_helper`. The whole `compile_single`
chain (then `remove_must_terminate`) keeps only source code labels. -/
theorem getCodeLabels_fullCompileSingle {width : Nat} [NeZero width]
    (tra : Bool) (regCount1 ralg : Nat) (asmC : AsmConfigExact width)
    (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    getCodeLabelsHOL
        (Compiler.Backend.WordToWord.fullCompileSingle tra regCount1 ralg asmC p).2.2 ⊆
      getCodeLabelsHOL p.1.2.2 := by
  rcases p with ⟨⟨name, arity, prog⟩, col⟩
  simp only [Compiler.Backend.WordToWord.fullCompileSingle,
    Compiler.Backend.WordToWord.compileSingle]
  rw [getCodeLabels_removeMustTerminate, getCodeLabels_wordAlloc]
  refine Set.Subset.trans (getCodeLabels_removeDeadProg _) ?_
  refine Set.Subset.trans (getCodeLabels_removeUnreach _) ?_
  rw [getCodeLabels_threeToTwoRegProg, word_get_code_labels_copy_prop]
  refine Set.Subset.trans (word_get_code_labels_word_common_subexp_elim _) ?_
  refine Set.Subset.trans (getCodeLabels_removeDeadProg _) ?_
  rw [codeLabels_fullSsaCcTrans, instSelect_codeLabels]
  exact Flapjack.WordConvs.WordSimpLabels.getCodeLabels_compileExp prog

/-- Flapjack infrastructure: the compiled rows keep only their source rows'
code-label sets, so the union over the output list is contained in the union
over the input list. HOL derives this inside the incr_helper subset argument. -/
private theorem sUnion_labels_compileSingle {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (oracles : List (Option (Spt Nat))) (tra : Bool) (regCount1 ralg : Nat)
    (asmC : AsmConfigExact width) :
    Set.sUnion {labels | labels ∈
        ((progs.zip oracles).map
          (Compiler.Backend.WordToWord.fullCompileSingle tra regCount1 ralg asmC)).map
          (fun row => getCodeLabelsHOL row.2.2)} ⊆
      Set.sUnion {labels | labels ∈ progs.map (fun row => getCodeLabelsHOL row.2.2)} := by
  intro x hx
  simp only [Set.mem_sUnion] at hx ⊢
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrow
  have hp1 : p.1 ∈ progs := (List.of_mem_zip hp).1
  refine ⟨getCodeLabelsHOL p.1.2.2, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨p.1, hp1, rfl⟩
  · exact getCodeLabels_fullCompileSingle tra regCount1 ralg asmC p hxt

/-- Flapjack infrastructure: the compiled rows' owner names are exactly the
source rows' names, so the owner set is unchanged. HOL derives this inside the
incr_helper subset argument. -/
private theorem names_compileSingle_eq {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (oracles : List (Option (Spt Nat))) (tra : Bool) (regCount1 ralg : Nat)
    (asmC : AsmConfigExact width) (hlen : progs.length = oracles.length) :
    ((progs.zip oracles).map
        (Compiler.Backend.WordToWord.fullCompileSingle tra regCount1 ralg asmC)).map
        Prod.fst =
      progs.map Prod.fst := by
  induction progs generalizing oracles with
  | nil =>
    cases oracles with
    | nil => rfl
    | cons o os =>
      simp only [List.length_nil, List.length_cons] at hlen
      omega
  | cons p ps ih =>
    cases oracles with
    | nil =>
      simp only [List.length_nil, List.length_cons] at hlen
      omega
    | cons o os =>
      simp only [List.zip_cons_cons, List.map_cons,
        Compiler.Backend.WordToWord.fullCompileSingle,
        Compiler.Backend.WordToWord.compileSingle]
      rw [ih os (by simpa using hlen)]

/-- Original per-oracle whole-program label safety through `full_compile_single`
for equal-length oracle lists. HOL's free `progs tra reg_count1 ralg asm_c` are
explicit and `oracles` is universal. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_code_labels_word_to_word_incr_helper" (words_as_type_indexed_bitvec)]
theorem goodCodeLabels_wordToWord_incrHelper {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) (elabs : Set Nat)
    (tra : Bool) (regCount1 ralg : Nat) (asmC : AsmConfigExact width) :
    ∀ oracles : List (Option (Spt Nat)), progs.length = oracles.length →
      goodCodeLabelsHOL progs elabs →
      goodCodeLabelsHOL
        ((progs.zip oracles).map
          (Compiler.Backend.WordToWord.fullCompileSingle tra regCount1 ralg asmC)) elabs := by
  intro oracles hlen hg
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    exact goodHandlers_wordToWord_incrHelper progs tra regCount1 ralg asmC oracles hlen
      (List.all_eq_true.mp hg.1)
  · rw [names_compileSingle_eq progs oracles tra regCount1 ralg asmC hlen]
    exact Set.Subset.trans (sUnion_labels_compileSingle progs oracles tra regCount1 ralg asmC)
      hg.2

/-- Flapjack infrastructure: zipping a list with its own `none` oracles is the
same as pairing every element with `none`. HOL uses `ZIP_MAP`. -/
private theorem zip_none_map {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    progs.zip (progs.map fun _ => (none : Option (Spt Nat))) =
      progs.map (fun p => (p, (none : Option (Spt Nat)))) := by
  induction progs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.zip_cons_cons]
    rw [ih]

/-- Original whole-program label safety through the incremental (NONE-oracle)
`full_compile_single` map. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_code_labels_word_to_word_incr" (words_as_type_indexed_bitvec)]
theorem goodCodeLabels_wordToWord_incr {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) (elabs : Set Nat)
    (tra : Bool) (regCount1 ralg : Nat) (asmC : AsmConfigExact width) :
    goodCodeLabelsHOL progs elabs →
      goodCodeLabelsHOL
        (progs.map (fun p =>
          Compiler.Backend.WordToWord.fullCompileSingle tra regCount1 ralg asmC (p, none)))
        elabs := by
  intro hg
  have hlen : progs.length =
      (progs.map fun _ => (none : Option (Spt Nat))).length := by simp
  have h := goodCodeLabels_wordToWord_incrHelper progs elabs tra regCount1 ralg asmC
    (progs.map fun _ => (none : Option (Spt Nat))) hlen hg
  rw [zip_none_map] at h
  simpa only [List.map_map, Function.comp_def] using h

/-- Original whole-program label safety of the complete `word_to_word` pass. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_code_labels_word_to_word" (words_as_type_indexed_bitvec)]
theorem goodCodeLabels_wordToWord {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) (elabs : Set Nat)
    (wc : Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact width) :
    goodCodeLabelsHOL progs elabs →
      goodCodeLabelsHOL (Compiler.Backend.WordToWord.compile wc ac progs).2 elabs := by
  intro hg
  exact goodCodeLabels_wordToWord_incrHelper progs elabs _ _ _ ac _
    (Compiler.Backend.WordToWord.compile_zip_length wc progs).symm hg

end Flapjack.WordConvs
