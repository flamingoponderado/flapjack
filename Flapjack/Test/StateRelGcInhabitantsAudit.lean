import Flapjack.HolRef.StateRelGcInhabitantsAudit
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelGc
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcLemma

open Lean Meta Flapjack

private theorem good {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2] :
    ∃ (_t2 : T2) (wl : Nat) (_w1 : W1) (_w2 : W2), wl = 0 :=
  ⟨Classical.choice inferInstance, 0, Classical.choice inferInstance, Classical.choice inferInstance, rfl⟩

private theorem badUsed {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2] :
    ∃ (_t2 : T2) (_w1 : W1) (_w2 : W2), _t2 = _t2 :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, rfl⟩

private theorem badExtra {T2 W1 W2 X : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2] [Nonempty X] :
    ∃ (_t2 : T2) (_w1 : W1) (_w2 : W2), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, trivial⟩

private theorem badDomain {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2] :
    ∃ (_t2 : T2) (_w1 : W1) (_w2 : W1), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, trivial⟩

private theorem badNestedDomain {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2] :
    ∃ (_t2 : T2) (_w1 : W1) (_w2 : W2) (_h : Nonempty Nat), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, ⟨0⟩, trivial⟩

private theorem badNestedUse {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2] :
    ∃ (_t2 : T2) (_w1 : W1) (_w2 : W2) (_h : _t2 = _t2), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, rfl, trivial⟩

private theorem badExplicitInstance {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2]
    (_h : Nonempty Nat) : ∃ (_t2 : T2) (_w1 : W1) (_w2 : W2), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, trivial⟩

private abbrev HiddenNE (X : Type) := Nonempty X
private def HiddenNERegular (X : Type) : Prop := Nonempty X
private theorem badAlias {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2]
    (_h : HiddenNE Nat) : ∃ (_t2 : T2) (_w1 : W1) (_w2 : W2), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, trivial⟩

private theorem badNestedAlias {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2] :
    ∃ (_t2 : T2) (_w1 : W1) (_w2 : W2) (_h : HiddenNE Nat), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, ⟨0⟩, trivial⟩

private theorem badForall {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2] :
    ∀ (_t2 : T2), ∃ (_w1 : W1) (_w2 : W2), True :=
  fun _ => ⟨Classical.choice inferInstance, Classical.choice inferInstance, trivial⟩

private theorem badWitnessName {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2] :
    ∃ (_other : T2) (_w1 : W1) (_w2 : W2), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, trivial⟩

private theorem badDuplicateInstance {T2 W1 W2 : Type} [Nonempty T2] [Nonempty W1] [Nonempty W2]
    [Inhabited T2] : ∃ (_t2 : T2) (_w1 : W1) (_w2 : W2), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, trivial⟩

private theorem badProp {T2 W1 W2 : Prop} [Nonempty T2] [Nonempty W1] [Nonempty W2] :
    ∃ (_t2 : T2) (_w1 : W1) (_w2 : W2), True :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, Classical.choice inferInstance, trivial⟩

private partial def alterBinder (e : Expr) (index : Nat)
    (change : Name → Expr → BinderInfo → Name × Expr × BinderInfo) : Expr :=
  match e with
  | .forallE name domain body bi =>
    if index == 0 then
      let (newName, newDomain, newInfo) := change name domain bi
      .forallE newName newDomain body newInfo
    else .forallE name domain (alterBinder body (index - 1) change) bi
  | .mdata md inner => .mdata md (alterBinder inner index change)
  | _ => e

private partial def alterExistential (e : Expr) (index : Nat)
    (change : Name → Expr → Name × Expr) : Expr :=
  match e with
  | .app (.app (.const ``Exists levels) ty) (.lam name domain body bi) =>
    if index == 0 then
      let (newName, newDomain) := change name domain
      .app (.app (.const ``Exists levels) newDomain) (.lam newName newDomain body bi)
    else .app (.app (.const ``Exists levels) ty)
      (.lam name domain (alterExistential body (index - 1) change) bi)
  | .mdata md inner => .mdata md (alterExistential inner index change)
  | _ => e

run_meta do
  for (name, expected) in #[(``good, true), (``badUsed, false), (``badExtra, false),
      (``badDomain, false), (``badNestedDomain, false), (``badNestedUse, false),
      (``badExplicitInstance, false), (``badAlias, false), (``badNestedAlias, false),
      (``badForall, false), (``badWitnessName, false), (``badDuplicateInstance, false),
      (``badProp, false)] do
    let info ← getConstInfo name
    let problems ← stateRelGcInhabitantProblems info.type
    if problems.isEmpty != expected then throwError "audit {name}: unexpected {problems}"
  let info ← getConstInfo ``Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.stateRel_gcGen
  let problems ← stateRelGcTelescopeProblems info.type
  unless problems.isEmpty do throwError "target telescope rejected: {problems}"
  let hidden := mkApp (mkConst ``HiddenNERegular) (mkConst ``Nat)
  let mutations := #[
    alterBinder info.type 3 (fun _ t b => (`C, t, b)),
    alterBinder info.type 0 (fun n t _ => (n, t, .default)),
    alterBinder info.type 0 (fun n _ b => (n, mkSort .zero, b)),
    alterBinder info.type 1 (fun n _ b => (n, mkConst ``True, b)),
    alterBinder info.type 2 (fun n _ b => (n, mkSort .zero, b)),
    alterBinder info.type 3 (fun n _ b => (n, mkSort .zero, b)),
    alterBinder info.type 17 (fun n _ b => (n, hidden, b)),
    alterBinder info.type 18 (fun n t b => (n, mkApp2 (mkConst ``And) t hidden, b))]
  for changed in mutations do
    if (← stateRelGcTelescopeProblems changed).isEmpty then
      throwError "target audit accepted a changed telescope"
  forallTelescope info.type fun args result => do
    for changedResult in #[
        alterExistential result 0 (fun _ ty => (`wrongWitness, ty)),
        alterExistential result 3 (fun name _ => (name, hidden))] do
      let changed ← mkForallFVars args changedResult
      if (← stateRelGcTelescopeProblems changed).isEmpty then
        throwError "target audit accepted a changed existential"
    withLocalDeclD `extra (mkConst ``True) fun extra => do
      let changed ← mkForallFVars (args.push extra) result
      if (← stateRelGcTelescopeProblems changed).isEmpty then
        throwError "target audit accepted an extra premise"

run_meta do
  let info ← getConstInfo ``Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.gcLemma_gen
  let problems ← gcLemmaGenTelescopeProblems info.type
  unless problems.isEmpty do throwError "GC lemma telescope rejected: {problems}"
  let hidden := mkApp (mkConst ``HiddenNERegular) (mkConst ``Nat)
  let mutations := #[
    alterBinder info.type 3 (fun _ t b => (`C, t, b)),
    alterBinder info.type 0 (fun n t _ => (n, t, .default)),
    alterBinder info.type 1 (fun n _ b => (n, mkConst ``True, b)),
    alterBinder info.type 4 (fun n _ b => (n, mkSort .zero, b)),
    alterBinder info.type 17 (fun n _ b => (n, mkConst ``Nat, b)),
    alterBinder info.type 19 (fun n t b => (n, mkApp2 (mkConst ``And) t hidden, b))]
  for changed in mutations do
    if (← gcLemmaGenTelescopeProblems changed).isEmpty then
      throwError "GC lemma audit accepted a changed telescope"
  forallTelescope info.type fun args result => do
    let unfolded ← whnf result
    for changedResult in #[
        alterExistential unfolded 4 (fun _ ty => (`wrongWitness, ty)),
        alterExistential unfolded 3 (fun name _ => (name, hidden))] do
      let changed ← mkForallFVars args changedResult
      if (← gcLemmaGenTelescopeProblems changed).isEmpty then
        throwError "GC lemma audit accepted a changed existential"
    let hiddenType := mkApp (mkConst ``Nonempty [0]) (mkConst ``Nat)
    let hiddenValue ← mkAppM ``Nonempty.intro #[mkNatLit 0]
    let hiddenLet := Expr.letE `hidden hiddenType hiddenValue result false
    let changed ← mkForallFVars args hiddenLet
    if (← gcLemmaGenTelescopeProblems changed).isEmpty then
      throwError "GC lemma audit accepted hidden inhabitance in a let binding"
    withLocalDeclD `extra (mkConst ``True) fun extra => do
      let changed ← mkForallFVars (args.push extra) result
      if (← gcLemmaGenTelescopeProblems changed).isEmpty then
        throwError "GC lemma audit accepted an extra premise"
