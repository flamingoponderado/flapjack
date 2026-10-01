import Flapjack.Compiler.Backend.WordAlloc.ReadsExp
import Flapjack.Compiler.Backend.WordAlloc.Expressions

namespace Flapjack.WordAlloc

/-- Literal read-list set/live-tree domain equality, with no input invariant.
The standard positive-width word translation is the only carrier qualification. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_reads_exp_get_live_exp"
  (words_as_type_indexed_bitvec)]
theorem getReadsExpGetLiveExp {width : Nat} [NeZero width]
    (expression : WordLangExpHOL (BitVec width)) :
    (fun key => key ∈ getReadsExpHOL expression) = sptDomain (getLiveExp expression) := by
  have h : ∀ key, key ∈ getReadsExpHOL expression ↔ sptDomain (getLiveExp expression) key := by
    refine WordLangExpHOL.rec
      (motive_1 := fun e => ∀ key, key ∈ getReadsExpHOL e ↔ sptDomain (getLiveExp e) key)
      (motive_2 := fun es => ∀ key, key ∈ (es.map getReadsExpHOL).flatten ↔
        sptDomain (bigUnion (es.map getLiveExp)) key)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression
    · intro value key
      simp [getReadsExpHOL, getLiveExp, sptDomain]
    · intro name key
      simp only [getReadsExpHOL, getLiveExp, List.mem_singleton]
      change key = name ↔ sptMem key (sptInsert name () .ln)
      rw [sptMem_sptInsert]
      simp [sptMem, sptDomain]
    · intro store key
      simp [getReadsExpHOL, getLiveExp, sptDomain]
    · intro address ih key
      simpa only [getReadsExpHOL, getLiveExp] using ih key
    · intro operator arguments ih key
      simpa only [getReadsExpHOL, getLiveExp] using ih key
    · intro operator left right ihLeft ihRight key
      simp only [getReadsExpHOL, getLiveExp, List.mem_append, sptDomain_sptUnion,
        ihLeft key, ihRight key]
    · intro key
      simp [bigUnion, sptDomain]
    · intro head tail ihHead ihTail key
      change key ∈ getReadsExpHOL head ++ (tail.map getReadsExpHOL).flatten ↔
        sptDomain (sptUnion (getLiveExp head) (bigUnion (tail.map getLiveExp))) key
      simp only [List.mem_append, sptDomain_sptUnion, ihHead key, ihTail key]
  funext key
  exact propext (h key)

end Flapjack.WordAlloc
