import Flapjack.Pancake.Semantics.LoopProps.CutSets

namespace Flapjack

/-- Exact HOL `loopProps$comp_syntax_ok_def` over `HolLoopProg` and
    `NumSet = Spt Unit`, following every defining clause at
    `cakeml/pancake/semantics/loopPropsScript.sml:57-73`. The HOL result is a
    Boolean; in Lean the logic-level existential in the `If` clause is
    reflected to `Bool` with classical `decide`. The `Seq` clause threads
    `cutSetsHOL live first` into its second conjunct, the `Loop` clause checks
    both stored live sets against the input and recurses at `liveIn`, and the
    `If` clause retains HOL's existential fold characterization. Only HOL's
    positive word-width parameter is represented by `BitVec width` here.

    This is a proof-side definition, not the executable list-backed
    `loopCompSyntaxOk` used by production. In particular, it makes no claim
    that the compiler routes through this exact carrier. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syntax_ok_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compSyntaxOkHOLExact {width : Nat} [NeZero width]
    (live : NumSet) : HolLoopProg width → Bool
  | .skip => true
  | .assign _ _ => true
  | .loop liveIn body liveOut => by
      classical
      exact decide (live = liveIn ∧ live = liveOut ∧
        compSyntaxOkHOLExact liveIn body = true)
  | .arith _ => true
  | .break _ => true
  | .locValue _ _ => true
  | .load32 _ _ => true
  | .loadByte _ _ => true
  | .seq first second => by
      classical
      exact decide (compSyntaxOkHOLExact live first = true ∧
        compSyntaxOkHOLExact (cutSetsHOL live first) second = true)
  | .ite _ _ _ thenBranch elseBranch liveOut => by
      classical
      exact decide (compSyntaxOkHOLExact live thenBranch = true ∧
        compSyntaxOkHOLExact live elseBranch = true ∧
        ∃ names : List Nat,
          liveOut = names.foldl (fun current name => sptInsert name () current) live)
  | _ => false

end Flapjack
