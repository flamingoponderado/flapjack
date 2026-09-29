import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.CompHOLImage

/-!
# Executable source route through exact `loop_to_word$comp_func`

This is the production-facing adapter from the executable `LoopProg` carrier
to the reviewed fixed-width HOL `comp_func`, then to the executable `WordProg`
carrier. The exact path is available precisely when every expression has an
exact HOL source representation. Executable-only `.crepOp` and `.cmp` syntax
is kept on the legacy extension path; this is a source-language distinction,
not a performance exception. Pancake-originating callers are separately
required to establish the exact-source guard before claiming this route.
-/

namespace Flapjack

open Flapjack.LoopToWord

private def loopProgFfiNamesByteRanged : LoopProg α → Bool
  | .seq first second =>
      loopProgFfiNamesByteRanged first && loopProgFfiNamesByteRanged second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopProgFfiNamesByteRanged thenBranch && loopProgFfiNamesByteRanged elseBranch
  | .loop _ body _ | .mark body => loopProgFfiNamesByteRanged body
  | .call _ _ _ handler =>
      match handler with
      | none => true
      | some (_, handlerBody, returnBody, _) =>
          loopProgFfiNamesByteRanged handlerBody && loopProgFfiNamesByteRanged returnBody
  | .ffi name _ _ _ _ _ => name.toList.all (fun character => character.toNat < 256)
  | _ => true

/-- Run exact HOL `comp_func` on an executable source body when the body has an
exact `HolLoopProg` representation. Failure here means the input contains
executable-only Loop syntax; production callers may retain the extension
compiler for that distinct syntax. The exact result is projected through the
fixed-width WordLang-to-WordProg adapter. -/
def loopToWordCompFuncViaHOL {width : Nat} [NeZero width]
    (name : Nat) (params : List Nat) (body : LoopProg (BitVec width)) :
    Option (WordProg (BitVec width)) :=
  if loopProgFfiNamesByteRanged body then do
    let exactBody ← executableLoopProgToHol body
    wordLangProgFromHOL (loopToWordCompFuncHOL name params exactBody)
  else
    none

/-- Exact HOL formal-register projection using the same exact `make_ctxt`
used by `comp_func`. It is paired with the exact body whenever the codec guard
selects the HOL route. -/
def loopToWordCompParametersViaHOL {width : Nat} [NeZero width]
    (params : List Nat) (body : LoopProg (BitVec width)) : Option (List Nat) := do
  if !loopProgFfiNamesByteRanged body then none else pure ()
  let exactBody ← executableLoopProgToHol body
  let variables := fromNumSetHOL
    (sptDifference (accVarsHOL exactBody (.ln : Spt Unit)) (toNumSetHOL params))
  let context := makeCtxtHOL 2 (params ++ variables) (.ln : Spt Nat)
  pure (params.map (Flapjack.LoopToWord.findVarHOL context))

/-- For a successful source encoding with byte-ranged FFI names, exact
`comp_func` always projects to the executable WordProg carrier. This follows
from the universal image theorem for `compHOL`; it rules out treating target
projection failure as a routine fallback condition on faithful source
programs. -/
theorem loopToWordCompFuncViaHOL_ne_none_of_encode_and_byte_names
    {width : Nat} [NeZero width] (name : Nat) (params : List Nat)
    (body : LoopProg (BitVec width)) (exactBody : HolLoopProg width)
    (hencode : executableLoopProgToHol body = some exactBody)
    (hnames : loopProgFfiNamesByteRanged body = true) :
    loopToWordCompFuncViaHOL name params body ≠ none := by
  unfold loopToWordCompFuncViaHOL
  rw [hnames]
  simp only [if_pos]
  rw [hencode]
  unfold loopToWordCompFuncHOL
  exact wordLangProgFromHOL_compHOL_ne_none
    (makeCtxtHOL 2 (params ++ fromNumSetHOL
      (sptDifference (accVarsHOL exactBody (.ln : Spt Unit))
        (toNumSetHOL params))) (.ln : Spt Nat))
    exactBody (name, 2)

/-- The executed wrapper takes the exact route on encodable programs, while
preserving the wider production extension for syntax with no HOL preimage or
byte-range-safe FFI representation. For the guarded encodable case, projection
success follows from `loopToWordCompFuncViaHOL_ne_none_of_encode_and_byte_names`. -/
def loopToWordCompFuncRouted {width : Nat} [NeZero width]
    (name : Nat) (params : List Nat) (body : LoopProg (BitVec width)) :
    WordProg (BitVec width) :=
  (loopToWordCompFuncViaHOL name params body).getD
    (loopToWordCompFunc name params body)

/-- Formal names chosen by the same guarded route as the body compiler. -/
def loopToWordCompParametersRouted {width : Nat} [NeZero width]
    (params : List Nat) (body : LoopProg (BitVec width)) : List Nat :=
  (loopToWordCompParametersViaHOL params body).getD
    (loopToWordCompParameters params body)

/-- When both the source encoder and the exact target projection succeed, the
routed production result is that exact projected HOL output; the compatibility
compiler is not selected. The projection premise is discharged from the
universal `compHOL` image theorem for faithful source programs. -/
theorem loopToWordCompFuncRouted_eq_projected_of_encode
    {width : Nat} [NeZero width] (name : Nat) (params : List Nat)
    (body : LoopProg (BitVec width)) (exactBody : HolLoopProg width)
    (output : WordProg (BitVec width))
    (hencode : executableLoopProgToHol body = some exactBody)
    (hnames : loopProgFfiNamesByteRanged body = true)
    (hproject : wordLangProgFromHOL (loopToWordCompFuncHOL name params exactBody) =
      some output) :
    loopToWordCompFuncRouted name params body =
      output := by
  simp [loopToWordCompFuncRouted, loopToWordCompFuncViaHOL,
    hnames, hencode, hproject]

/-- The selected production route is the projection of the exact HOL-shaped
`comp_func` result on every encoded program whose FFI names satisfy the byte
boundary. The witness includes successful projection, discharged by the
universal compiler-image theorem rather than an unproved caller assumption. -/
theorem loopToWordCompFuncRouted_projects_compHOL
    {width : Nat} [NeZero width] (name : Nat) (params : List Nat)
    (body : LoopProg (BitVec width)) (exactBody : HolLoopProg width)
    (hencode : executableLoopProgToHol body = some exactBody)
    (hnames : loopProgFfiNamesByteRanged body = true) :
    ∃ output, wordLangProgFromHOL (loopToWordCompFuncHOL name params exactBody) =
        some output ∧ loopToWordCompFuncRouted name params body = output := by
  let projected := wordLangProgFromHOL
    (loopToWordCompFuncHOL name params exactBody)
  have hproject : projected ≠ none := by
    simpa [projected, loopToWordCompFuncHOL] using
      wordLangProgFromHOL_compHOL_ne_none
        (makeCtxtHOL 2 (params ++ fromNumSetHOL
          (sptDifference (accVarsHOL exactBody (.ln : Spt Unit))
            (toNumSetHOL params))) (.ln : Spt Nat))
        exactBody (name, 2)
  cases hprojected : projected with
  | none => exact False.elim (hproject hprojected)
  | some output =>
      have hprojected' : wordLangProgFromHOL
          (loopToWordCompFuncHOL name params exactBody) = some output := by
        simpa [projected] using hprojected
      exact ⟨output, hprojected',
        loopToWordCompFuncRouted_eq_projected_of_encode
          name params body exactBody output hencode hnames hprojected'⟩

end Flapjack
