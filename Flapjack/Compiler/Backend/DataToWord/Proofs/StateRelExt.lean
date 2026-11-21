module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.WordToWord.Compile

@[expose] public section

/-! The extended data-to-word state relation, relating a data state to a word
state whose code has been compiled by `word_to_word`
(`data_to_wordProofScript.sml` lines 1190-1206 and 1291-1303). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.WordToWord

namespace reviewedStateRelExtMap
/-- Canonical roundtrip for the word state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedStateRelExtMap

/-- HOL `state_rel_ext`: some word state `t` is related to `s` with an empty
location stack, and `u` is `t` with its code replaced by a `word_to_word`
compilation `l` of `t.code`, its termination depth reset, and its compiler
and oracle obtained by composing with `full_compile_single`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "state_rel_ext_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def stateRelExt {width : Nat} [NeZero width] {C F : Type} (c : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (u : WordSemStateFiniteExact width C F) : Prop :=
  ∃ (t : WordSemStateFiniteExact width C F) (l : Spt (Nat × WordLangProgHOL (BitVec width))),
    stateRel c l1 l2 s t none [] ∧
    sptDomain t.code = sptDomain l ∧
    t.termdep > 1 ∧
    (∃ (tt : Bool) (kk aa : Nat) (co : Compiler.Encoders.Asm.AsmConfigExact width),
      u.compileOracle =
        Prod.map id (List.map (fun p => fullCompileSingle tt kk aa co (p, none))) ∘ t.compileOracle ∧
      t.compile = (fun conf progs =>
        u.compile conf (progs.map (fun p => fullCompileSingle tt kk aa co (p, none))))) ∧
    (∀ (n : Nat) (v : Nat × WordLangProgHOL (BitVec width)), sptLookup n t.code = some v →
      ∃ (t' : Bool) (k' a' : Nat) (c' : Compiler.Encoders.Asm.AsmConfigExact width)
        (col : Option (Spt Nat)),
        sptLookup n l = some (fullCompileSingle t' k' a' c' ((n, v), col)).2) ∧
    u = { t with code := l, termdep := 0, compile := u.compile, compileOracle := u.compileOracle }

/-- Replacing both clocks by the same value preserves the extended relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "state_rel_ext_with_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRelExt_withClock {width : Nat} [NeZero width] {C F : Type} (a : Flapjack.Compiler.Backend.DataToWord.Config) (b c : Nat)
    (s1 : Flapjack.Compiler.Backend.DataSem.State C F) (s2 : WordSemStateFiniteExact width C F) (k : Nat)
    (h : stateRelExt a b c s1 s2) :
    stateRelExt a b c { s1 with clock := k } { s2 with clock := k } := by
  obtain ⟨t, l, rel, dom, depth, ⟨tt, kk, aa, co, horacle, hcompile⟩, hcode, hu⟩ := h
  refine ⟨{ t with clock := k }, l, stateRel_withClock a b c s1 t none [] k rel, dom, depth,
    ⟨tt, kk, aa, co, horacle, hcompile⟩, hcode, ?_⟩
  rw [hu]

end Flapjack.Compiler.Backend.DataToWord.Proofs
