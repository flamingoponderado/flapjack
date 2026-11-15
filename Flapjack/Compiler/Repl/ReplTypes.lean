module

public import Flapjack.TypeSoundInvariants
public import Flapjack.PrimTypesHOL.Types

@[expose] public section

/-! Primitive type-environment facts used by the compiler and REPL proofs. -/
namespace Flapjack.Compiler.Repl.ReplTypes
open Flapjack.NamespaceHOL Flapjack.PrimTypesHOL Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants

@[hol "cakeml/compiler/repl/repl_typesScript.sml" "tenv_ok_prim_tenv"]
theorem tenvOkPrimTenv : tenvOk primTenv := by
  unfold tenvOk tenvValOk tenvCtorOk tenvAbbrevOk
  simp only [nsAll, primTenv, alistToNs, nsEmpty]
  constructor
  · intro id v h
    cases id <;> simp [nsLookup] at h
  · constructor
    · intro id v h
      cases id with
      | long m id => simp [nsLookup] at h
      | short name =>
        simp only [nsLookup, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h
        simp only [List.lookup] at h
        repeat' (split at h <;> simp_all)
        all_goals subst v
        all_goals simp_all [checkFreevars, checkFreevarsList]
    · intro id v h
      cases id with
      | long m id => simp [nsLookup] at h
      | short name =>
        simp only [nsLookup, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h
        simp only [List.lookup] at h
        repeat' (split at h <;> simp_all)
        all_goals subst v
        all_goals simp_all [checkFreevars, checkFreevarsList]

end Flapjack.Compiler.Repl.ReplTypes
