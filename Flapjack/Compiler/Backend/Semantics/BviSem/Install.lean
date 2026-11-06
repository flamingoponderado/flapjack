import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyAux
import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions

/-! BVI code installation. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem

namespace InstallCarrier
/-- Canonical reference-map state roundtrip for BVI installation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end InstallCarrier

/-- Install a compiled program only when the decoded buffers, lengths, code
names, callback result and shifted oracle agree. The result error payload
type is independent, as in the captured original. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "do_install_def"
  (fmap_as_finite_support := [refs])]
noncomputable def doInstall {C F R : Type} (args : List Value) (s : BviState C F) :
    Flapjack.SemanticPrimitivesHOL.Result (Value × BviState C F) R := by
  classical
  let fail : Flapjack.SemanticPrimitivesHOL.Result (Value × BviState C F) R := .err (.abort .typeError)
  exact match args with
  | [v1, v2, .number len1, .number len2] =>
    match valueToBytes v1, valueToWords v2 with
    | some bytes, some data =>
      if len1 ≠ Int.ofNat bytes.length ∨ len2 ≠ Int.ofNat data.length then fail else
      let (cfg, progs) := s.compileOracle 0
      let newOracle := fun n => s.compileOracle (n + 1)
      if (∀ entry ∈ progs, sptLookup entry.1 s.code = none) ∧
          (progs.map Prod.fst).Nodup then
        match s.compile cfg progs, progs with
        | some (bytes', data', cfg'), (key, _) :: _ =>
          if bytes = bytes' ∧ data = data' ∧ (newOracle 0).1 = cfg' then
            .val (.codePtr key, { s with
              code := sptUnion s.code (sptFromAList progs)
              compileOracle := newOracle })
          else fail
        | _, _ => fail
      else fail
    | _, _ => fail
  | _ => fail

end Flapjack.Compiler.Backend.BviSem
