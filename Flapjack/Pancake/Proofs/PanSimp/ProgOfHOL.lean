import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanLang.ProgHOLInduction

/-!
Flapjack-specific representation bridges for the exact HOL `pan_simp` pass.

These results connect the `ProgHOL` ports to the production `Prog` helpers.
They are not HOL declarations themselves and therefore carry no `@[hol]`
tag.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Decode of the exact HOL `SmartSeq_def` agrees with production `smartSeq`.
This is Flapjack-specific codec infrastructure: HOL defines `SmartSeq` on
`ProgHOL`, but has no separate theorem about the Lean `progOfHOL` decoder. -/
theorem progOfHOL_smartSeqHOL {width : Nat} [NeZero width]
    (pre program : ProgHOL width) :
    progOfHOL (smartSeqHOL pre program) =
      smartSeq (progOfHOL pre) (progOfHOL program) := by
  cases pre <;> simp [smartSeqHOL, smartSeq, progOfHOL]
  case call info name args =>
    cases info with
    | none => simp [progOfHOL.eq_13]
    | some info =>
      obtain ⟨kind, handler⟩ := info
      cases handler with
      | none => simp [progOfHOL.eq_14]
      | some handler =>
        obtain ⟨eid, vname, body⟩ := handler
        simp [progOfHOL.eq_15]

/-- `toStringOfBytes` is injective because `ofString` is its left inverse.
This local statement avoids an import of the downstream PanGlobals module. -/
theorem panSimpToStringOfBytes_injective : Function.Injective toStringOfBytes := by
  intro left right heq
  have := congrArg ofString heq
  simpa [ofString_toStringOfBytes] using this

@[simp] theorem panSimpToStringOfBytes_eq_iff (left right : MlS) :
    toStringOfBytes left = toStringOfBytes right ↔ left = right := by
  constructor
  · exact fun h => panSimpToStringOfBytes_injective h
  · intro h
    cases h
    rfl

/-- Flapjack-specific decoding of HOL `Prog.call` metadata to production
metadata. There is no separate HOL declaration for this codec helper. -/
def progCallInfoOfHOL {width : Nat} [NeZero width] :
    Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)) →
      Option (Option (VarKind × String) × Option (String × String × Prog (BitVec width)))
  | none => none
  | some (kindOpt, none) =>
      some (kindOpt.map (fun entry => (entry.1, toStringOfBytes entry.2)), none)
  | some (kindOpt, some (eid, vname, body)) =>
      some (kindOpt.map (fun entry => (entry.1, toStringOfBytes entry.2)),
        some (toStringOfBytes eid, toStringOfBytes vname, progOfHOL body))

/-- Every exact HOL call decodes to the production call with decoded names,
arguments, and optional handler body. This is Flapjack-specific codec
infrastructure with no separate HOL original. -/
theorem progOfHOL_call {width : Nat} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (name : MlS) (args : List (ExpHOL width)) :
    progOfHOL (.call info name args) =
      Prog.call (progCallInfoOfHOL info) (toStringOfBytes name) (args.map expOfHOL) := by
  cases info with
  | none => simp [progCallInfoOfHOL, progOfHOL.eq_13]
  | some info =>
      obtain ⟨kindOpt, handlerOpt⟩ := info
      cases handlerOpt with
      | none => simp [progCallInfoOfHOL, progOfHOL.eq_14]
      | some handler =>
          obtain ⟨eid, vname, body⟩ := handler
          simp [progCallInfoOfHOL, progOfHOL.eq_15]

/-- Flapjack-specific codec equation for the Call clause of HOL
`seq_assoc_def`. When a handler is present, the only recursive obligation is
that its body commutes with `seqAssocHOL`; the theorem has no separate HOL
original and therefore carries no `@[hol]` tag. -/
theorem progOfHOL_seqAssocHOL_call {width : Nat} [NeZero width]
    (pre : ProgHOL width)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (name : MlS) (args : List (ExpHOL width))
    (handlerBridge : ∀ {returns eid vname body},
      info = some (returns, some (eid, vname, body)) →
        progOfHOL (seqAssocHOL .skip body) = seqAssoc .skip (progOfHOL body)) :
    progOfHOL (seqAssocHOL pre (.call info name args)) =
      seqAssoc (progOfHOL pre)
        (.call (progCallInfoOfHOL info) (toStringOfBytes name) (args.map expOfHOL)) := by
  cases info with
  | none =>
      simp [seqAssocHOL, seqAssoc, progOfHOL_smartSeqHOL, progOfHOL_call,
        progCallInfoOfHOL]
  | some info =>
      obtain ⟨returns, handler⟩ := info
      cases handler with
      | none =>
          simp [seqAssocHOL, seqAssoc, progOfHOL_smartSeqHOL, progOfHOL_call,
            progCallInfoOfHOL]
      | some handler =>
          obtain ⟨eid, vname, body⟩ := handler
          have hbody := handlerBridge (returns := returns) (eid := eid)
            (vname := vname) (body := body) rfl
          simp [seqAssocHOL, seqAssoc, progOfHOL_smartSeqHOL, progOfHOL_call,
            progCallInfoOfHOL, hbody]

/-- Flapjack-specific representation bridge for HOL `seq_call_ret_def`.
HOL has no separate theorem about the `ProgHOL` decoder. This proof compares
the exact MlString guard with production String equality through the codec
lemma above; it is not a tagged HOL declaration. -/
theorem progOfHOL_seqCallRetHOL {width : Nat} [NeZero width]
    (program : ProgHOL width) :
    progOfHOL (seqCallRetHOL program) = seqCallRet (progOfHOL program) := by
  cases program with
  | seq first second =>
      cases first with
      | call info function arguments =>
          cases info with
          | none => cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
          | some info =>
              obtain ⟨kindOpt, handlerOpt⟩ := info
              cases kindOpt with
              | none =>
                  cases handlerOpt with
                  | none => cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
                  | some handler =>
                      obtain ⟨eid, vname, body⟩ := handler
                      cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
              | some kindName =>
                  obtain ⟨kind, returnName⟩ := kindName
                  cases handlerOpt with
                  | some handler =>
                      obtain ⟨eid, vname, body⟩ := handler
                      cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
                  | none =>
                      cases kind with
                      | global => cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
                      | «local» =>
                          cases second with
                          | «return» value =>
                              cases value with
                              | var returnedKind returnedName =>
                                  cases returnedKind with
                                  | global =>
                                      simp [seqCallRetHOL, seqCallRet, progOfHOL, expOfHOL]
                                  | «local» =>
                                      by_cases h : returnName = returnedName
                                      · simp [seqCallRetHOL, seqCallRet, progOfHOL, expOfHOL, h]
                                      · simp [seqCallRetHOL, seqCallRet, progOfHOL, expOfHOL, h,
                                          panSimpToStringOfBytes_eq_iff]
                              | _ => simp [seqCallRetHOL, seqCallRet, progOfHOL, expOfHOL]
                          | call info name args =>
                              simp [seqCallRetHOL, seqCallRet, progOfHOL, progOfHOL_call,
                                progCallInfoOfHOL]
                          | _ => simp [seqCallRetHOL, seqCallRet, progOfHOL]
      | _ => cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
  | call info name args =>
      cases info with
      | none => simp [seqCallRetHOL, seqCallRet, progOfHOL]
      | some info =>
          obtain ⟨kindOpt, handlerOpt⟩ := info
          cases handlerOpt with
          | none => simp [seqCallRetHOL, seqCallRet, progOfHOL]
          | some handler =>
              obtain ⟨eid, vname, body⟩ := handler
              simp [seqCallRetHOL, seqCallRet, progOfHOL]
  | _ => simp [seqCallRetHOL, seqCallRet, progOfHOL]

/-- Flapjack-specific full codec bridge for HOL `seq_assoc_def`: decoding the
exact `seqAssocHOL` agrees with production `seqAssoc` on decoded programs.
HOL has no separate theorem about the `ProgHOL` decoder. The proof uses the
Lean-only strong `sizeOf` induction `progHOL_sizeOf_induction` because
`seqAssocHOL` is well-founded, not structurally, recursive. -/
theorem progOfHOL_seqAssocHOL {width : Nat} [NeZero width]
    (pre program : ProgHOL width) :
    progOfHOL (seqAssocHOL pre program) =
      seqAssoc (progOfHOL pre) (progOfHOL program) := by
  suffices h : ∀ program : ProgHOL width,
      ∀ pre, progOfHOL (seqAssocHOL pre program) =
        seqAssoc (progOfHOL pre) (progOfHOL program) from h program pre
  refine progHOL_sizeOf_induction
    (motive := fun program => ∀ pre, progOfHOL (seqAssocHOL pre program) =
      seqAssoc (progOfHOL pre) (progOfHOL program)) ?_
  intro program ih pre
  cases program with
  | skip => simp [seqAssocHOL, seqAssoc, progOfHOL]
  | dec name shape value body =>
      simp only [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL,
        ih body (by decreasing_trivial) .skip]
      try rfl
  | seq first second =>
      simp only [seqAssocHOL, seqAssoc, progOfHOL,
        ih second (by decreasing_trivial) (seqAssocHOL pre first),
        ih first (by decreasing_trivial) pre]
      try rfl
  | ite condition thenBranch elseBranch =>
      simp only [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL,
        ih thenBranch (by decreasing_trivial) .skip,
        ih elseBranch (by decreasing_trivial) .skip]
      try rfl
  | «while» condition body =>
      simp only [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL,
        ih body (by decreasing_trivial) .skip]
      try rfl
  | call info name args =>
      rw [progOfHOL_call]
      rw [progOfHOL_seqAssocHOL_call (pre := pre) (info := info) (name := name)
        (args := args) (fun {returns eid vname body} hmem =>
          by
            subst hmem
            exact ih body (by decreasing_trivial) .skip |> fun h => by
              simpa [progOfHOL] using h)]
  | decCall name shape function args body =>
      simp only [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL,
        ih body (by decreasing_trivial) .skip]
      try rfl
  | annot tag text => simp [seqAssocHOL, seqAssoc, progOfHOL]
  | assign kind name value => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | primitive name operator args => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | store address value => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | store32 address value => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | storeByte address value => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | «break» => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | «continue» => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | extCall function configuration configurationLength array arrayLength =>
      simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | raise exception value => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | «return» value => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | shMemLoad size kind name address =>
      simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | shMemStore size address value =>
      simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]
  | tick => simp [seqAssocHOL, seqAssoc, progOfHOL, progOfHOL_smartSeqHOL]

/-- Flapjack-specific codec bridge for HOL `ret_to_tail_def`: decoding the
exact `retToTailHOL` agrees with production `retToTail`. No separate HOL
theorem; proved by strong `sizeOf` induction over `ProgHOL`. -/
theorem progOfHOL_retToTailHOL {width : Nat} [NeZero width]
    (program : ProgHOL width) :
    progOfHOL (retToTailHOL program) = retToTail (progOfHOL program) := by
  suffices h : ∀ program : ProgHOL width,
      progOfHOL (retToTailHOL program) = retToTail (progOfHOL program) from h program
  refine progHOL_sizeOf_induction (motive := fun program =>
    progOfHOL (retToTailHOL program) = retToTail (progOfHOL program)) ?_
  intro program ih
  cases program with
  | skip => simp [retToTailHOL, retToTail, progOfHOL]
  | dec name shape value body =>
      simp only [retToTailHOL, retToTail, progOfHOL, ih body (by decreasing_trivial)]
      try rfl
  | seq first second =>
      simp only [retToTailHOL, retToTail, progOfHOL, progOfHOL_seqCallRetHOL,
        ih first (by decreasing_trivial), ih second (by decreasing_trivial)]
      try rfl
  | ite condition thenBranch elseBranch =>
      simp only [retToTailHOL, retToTail, progOfHOL,
        ih thenBranch (by decreasing_trivial), ih elseBranch (by decreasing_trivial)]
      try rfl
  | «while» condition body =>
      simp only [retToTailHOL, retToTail, progOfHOL, ih body (by decreasing_trivial)]
      try rfl
  | call info name args =>
      cases info with
      | none => simp [retToTailHOL, retToTail, progOfHOL]
      | some returnsHandler =>
          obtain ⟨returns, handler⟩ := returnsHandler
          cases handler with
          | none => simp [retToTailHOL, retToTail, progOfHOL]
          | some handlerData =>
              obtain ⟨eid, vname, body⟩ := handlerData
              simp only [retToTailHOL, retToTail, progOfHOL,
                ih body (by decreasing_trivial)]
              try rfl
  | decCall name shape function args body =>
      simp only [retToTailHOL, retToTail, progOfHOL, ih body (by decreasing_trivial)]
      try rfl
  | annot tag text => simp [retToTailHOL, retToTail, progOfHOL]
  | assign kind name value => simp [retToTailHOL, retToTail, progOfHOL]
  | primitive name operator args => simp [retToTailHOL, retToTail, progOfHOL]
  | store address value => simp [retToTailHOL, retToTail, progOfHOL]
  | store32 address value => simp [retToTailHOL, retToTail, progOfHOL]
  | storeByte address value => simp [retToTailHOL, retToTail, progOfHOL]
  | «break» => simp [retToTailHOL, retToTail, progOfHOL]
  | «continue» => simp [retToTailHOL, retToTail, progOfHOL]
  | extCall function configuration configurationLength array arrayLength =>
      simp [retToTailHOL, retToTail, progOfHOL]
  | raise exception value => simp [retToTailHOL, retToTail, progOfHOL]
  | «return» value => simp [retToTailHOL, retToTail, progOfHOL]
  | shMemLoad size kind name address => simp [retToTailHOL, retToTail, progOfHOL]
  | shMemStore size address value => simp [retToTailHOL, retToTail, progOfHOL]
  | tick => simp [retToTailHOL, retToTail, progOfHOL]

/-- Flapjack-specific codec bridge for HOL `compile_def`: decoding the exact
`panSimpCompileHOL` agrees with the executed production `panSimpProg`. -/
theorem progOfHOL_panSimpCompileHOL {width : Nat} [NeZero width]
    (program : ProgHOL width) :
    progOfHOL (panSimpCompileHOL program) = panSimpProg (progOfHOL program) := by
  rw [panSimpCompileHOL, progOfHOL_retToTailHOL, progOfHOL_seqAssocHOL]
  simp only [panSimpProg, progOfHOL]

/-- Flapjack-specific codec bridge for HOL `compile_prog_def`: mapping the
exact `panSimpDeclsHOL` through `declOfHOL` agrees with the executed
production `panSimpDecls`. -/
theorem progOfHOL_panSimpDeclsHOL {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) :
    (panSimpDeclsHOL declarations).map (fun d => declOfHOL d) =
      panSimpDecls (declarations.map (fun d => declOfHOL d)) := by
  induction declarations with
  | nil => simp [panSimpDeclsHOL, panSimpDecls]
  | cons declaration declarations ih =>
      cases declaration with
      | function d =>
          simp only [panSimpDeclsHOL, List.map_cons]
          rw [ih]
          simp [panSimpDecls, declOfHOL, funDeclOfHOL, progOfHOL_panSimpCompileHOL]
      | decl shape name value =>
          simp only [panSimpDeclsHOL, List.map_cons]
          rw [ih]
          simp [panSimpDecls, declOfHOL]
      | exnDecl exceptionName shape =>
          simp only [panSimpDeclsHOL, List.map_cons]
          rw [ih]
          simp [panSimpDecls, declOfHOL]
      | name struct fields =>
          simp only [panSimpDeclsHOL, List.map_cons]
          rw [ih]
          simp [panSimpDecls, declOfHOL]

end Flapjack
