import Flapjack.Compiler.Backend.WordSimp
import Flapjack.RiscV.WordFuseConditions
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

/-! Full executed/native push-out-if correspondence on the actual codec image.
The two program carriers differ, so this is untagged Flapjack infrastructure,
not a restricted HOL correctness theorem. Both transformed body and termination
flag are transported; only the input encoding is assumed. The executed generic
WordProg operation and the width-indexed native operation have distinct
carriers. This theorem supplies their codec bridge; reviewed-definition runtime
adoption remains a separate inventory obligation, and no performance exception
is claimed here.
-/
namespace Flapjack.Compiler.Backend.WordSimp
open RiscV

/-- The actual recursive production pass preserves every represented payload
and computes the same termination flag as the reviewed native definition.
In a terminating Seq, its second child remains untouched, exactly as in HOL. -/
theorem pushOutIfAux_production {width : Nat} [NeZero width] :
    ∀ (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width)),
      wordLangProgToHOL program = some native →
      (wordLangProgToHOL (wordPushOutIfAux program).1).map
        (fun result => (result, (wordPushOutIfAux program).2)) = some (pushOutIfAux native) := by
  intro program
  induction hsize : sizeOf program using Nat.strongRecOn generalizing program with
  | ind n ih =>
    intro native encoded
    have ih' : ∀ q : WordProg (BitVec width), sizeOf q < sizeOf program →
        ∀ nq, wordLangProgToHOL q = some nq →
          (wordLangProgToHOL (wordPushOutIfAux q).1).map
            (fun result => (result, (wordPushOutIfAux q).2)) = some (pushOutIfAux nq) :=
      fun q hq => ih _ (hsize ▸ hq) q rfl
    clear ih hsize
    have child : ∀ q : WordProg (BitVec width), sizeOf q < sizeOf program →
        ∀ nq, wordLangProgToHOL q = some nq →
          ∃ actualOut nativeOut flag,
            wordPushOutIfAux q = (actualOut, flag) ∧
            pushOutIfAux nq = (nativeOut, flag) ∧
            wordLangProgToHOL actualOut = some nativeOut := by
      intro q hq nq eq
      cases transformed : wordPushOutIfAux q with
      | mk actualOut flag =>
        obtain ⟨nativeOut, result, same⟩ := Option.map_eq_some_iff.mp
          (by simpa only [transformed, Prod.fst, Prod.snd] using ih' q hq nq eq)
        exact ⟨actualOut, nativeOut, flag, rfl, same.symm, result⟩
    cases program with
    | seq first second =>
      cases hf : wordLangProgToHOL first with
      | none => simp [wordLangProgToHOL, hf] at encoded
      | some nf =>
        cases hs : wordLangProgToHOL second with
        | none => simp [wordLangProgToHOL, hf, hs] at encoded
        | some ns =>
          simp [wordLangProgToHOL, hf, hs] at encoded
          subst native
          obtain ⟨a, na, ba, ha, hna, hea⟩ := child first (by simp; omega) nf hf
          obtain ⟨b, nb, bb, hb, hnb, heb⟩ := child second (by simp; omega) ns hs
          cases ba <;> cases bb <;>
            simp [wordPushOutIfAux, pushOutIfAux, ha, hb, hna, hnb,
              wordLangProgToHOL, hea, heb, hs]
    | ite op condition right first second =>
      cases hf : wordLangProgToHOL first with
      | none => simp [wordLangProgToHOL, hf] at encoded
      | some nf =>
        cases hs : wordLangProgToHOL second with
        | none => simp [wordLangProgToHOL, hf, hs] at encoded
        | some ns =>
          simp [wordLangProgToHOL, hf, hs] at encoded
          subst native
          obtain ⟨a, na, ba, ha, hna, hea⟩ := child first (by simp; omega) nf hf
          obtain ⟨b, nb, bb, hb, hnb, heb⟩ := child second (by simp; omega) ns hs
          cases ba <;> cases bb <;>
            simp [wordPushOutIfAux, pushOutIfAux, ha, hb, hna, hnb,
              wordLangProgToHOL, hea, heb]
    | mustTerminate body =>
      cases he : wordLangProgToHOL body with
      | none => simp [wordLangProgToHOL, he] at encoded
      | some nb =>
        simp only [wordLangProgToHOL, he, Option.map_some, Option.some.injEq] at encoded
        subst native
        obtain ⟨a, na, flag, ha, hna, hea⟩ := child body (by simp) nb he
        simp [wordPushOutIfAux, pushOutIfAux, ha, hna, wordLangProgToHOL, hea]
    | loop names body exitNames =>
      cases he : wordLangProgToHOL body with
      | none => simp [wordLangProgToHOL, he] at encoded
      | some nb =>
        simp [wordLangProgToHOL, he] at encoded
        subst native
        obtain ⟨a, na, flag, ha, hna, hea⟩ := child body (by simp; omega) nb he
        simp [wordPushOutIfAux, pushOutIfAux, ha, hna, wordLangProgToHOL, hea]
    | inst instruction =>
      cases he : wordLangInstToHOL instruction with
      | none => simp [wordLangProgToHOL, he] at encoded
      | some ni =>
        simp only [wordLangProgToHOL, he, Option.map_some, Option.some.injEq] at encoded
        subst native
        simp [wordPushOutIfAux, pushOutIfAux, wordLangProgToHOL, he]
    | call returns target arguments handler =>
      clear ih' child
      rcases returns with _ | ⟨values, sets, body, l1, l2⟩ <;>
        rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩
      · simp [wordLangProgToHOL] at encoded
        subst native
        simp [wordPushOutIfAux, pushOutIfAux, wordLangProgToHOL]
      · cases hh : wordLangProgToHOL handlerBody with
        | none => simp [wordLangProgToHOL, hh] at encoded
        | some nh =>
          simp [wordLangProgToHOL, hh] at encoded
          subst native
          simp [wordPushOutIfAux, pushOutIfAux, wordLangProgToHOL, hh]
      · cases hr : wordLangProgToHOL body with
        | none => simp [wordLangProgToHOL, hr] at encoded
        | some nr =>
          simp [wordLangProgToHOL, hr] at encoded
          subst native
          simp [wordPushOutIfAux, pushOutIfAux, wordLangProgToHOL, hr]
      · cases hr : wordLangProgToHOL body with
        | none => simp [wordLangProgToHOL, hr] at encoded
        | some nr =>
          cases hh : wordLangProgToHOL handlerBody with
          | none => simp [wordLangProgToHOL, hr, hh] at encoded
          | some nh =>
            simp [wordLangProgToHOL, hr, hh] at encoded
            subst native
            simp [wordPushOutIfAux, pushOutIfAux, wordLangProgToHOL, hr, hh]
    | _ =>
      clear ih' child
      cases native <;> simp_all [wordLangProgToHOL, wordPushOutIfAux, pushOutIfAux]

/-- Complete public pass transport from the input codec image. No successful
output, desired post-state, or target evaluation is assumed. -/
theorem pushOutIf_production {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    wordLangProgToHOL (wordPushOutIf program) = some (pushOutIf native) := by
  have full := congrArg (Option.map Prod.fst) (pushOutIfAux_production program native encoded)
  simpa [wordPushOutIf, pushOutIf, Option.map_map, Function.comp_def] using full

end Flapjack.Compiler.Backend.WordSimp
