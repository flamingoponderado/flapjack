import Flapjack.Pancake.PanToCrep.Compile

/-!
# Function-name invariants for the Pancake-to-Crep compiler

CakeML's `pan_to_crep` correctness development keeps the compiled function
table keyed by distinct names.  `compileFunctionsSource` filters non-function
declarations while preserving each function declaration's name, so the
invariant is a direct but useful bridge between a source declaration list and
the table consumed by call correctness.
-/

namespace Flapjack

def functionDeclarationNames : List (Decl α) → List FunName
  | [] => []
  | .function declaration :: declarations =>
      declaration.name :: functionDeclarationNames declarations
  | _ :: declarations => functionDeclarationNames declarations
termination_by declarations => sizeOf declarations

/-! The source function list underlying Cake's `functions` projection.  Keeping
    the declaration itself, rather than only its name, makes the indexed
    provenance of `compile_to_crep` explicit. -/
def functionDeclarations : List (Decl α) → List (FunDecl α)
  | [] => []
  | .function declaration :: declarations =>
      declaration :: functionDeclarations declarations
  | _ :: declarations => functionDeclarations declarations
termination_by declarations => sizeOf declarations

/-! Counterpart of Cake's `el_compile_prog_el_prog_eq`
    (`pan_to_crepProofScript.sml:4589-4601`) for the source-shaped compiler.
    `compileFunctionsSource` filters non-function declarations, so the
    function declaration at an index and the compiled function at that index
    remain paired.  This is the indexed table-provenance fact needed before
    lifting source state semantics through `compile_to_crep`. -/
theorem compileFunctionsSource_getElem?_origin
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    {n : Nat} {function : CompiledFunction α}
    (hcompiled : (compileFunctionsSource context declarations)[n]? = some function) :
    ∃ declaration : FunDecl α,
      (functionDeclarations declarations)[n]? = some declaration ∧
      function = compileFunDeclSource context declaration := by
  induction declarations generalizing n function with
  | nil =>
      simp [compileFunctionsSource] at hcompiled
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          cases n with
          | zero =>
              simp only [compileFunctionsSource, List.getElem?_cons_zero] at hcompiled
              simp only [Option.some.injEq] at hcompiled
              subst function
              exact ⟨declaration, by simp [functionDeclarations], rfl⟩
          | succ n =>
              have htail :
                  (compileFunctionsSource context declarations)[n]? = some function := by
                simpa [compileFunctionsSource] using hcompiled
              obtain ⟨found, hfound, horigin⟩ := ih htail
              exact ⟨found, by simpa [functionDeclarations] using hfound, horigin⟩
      | decl shape name value =>
          have htail :
              (compileFunctionsSource context declarations)[n]? = some function := by
            simpa [compileFunctionsSource] using hcompiled
          obtain ⟨found, hfound, horigin⟩ := ih htail
          exact ⟨found, by simpa [functionDeclarations] using hfound, horigin⟩
      | exnDecl exception shape =>
          have htail :
              (compileFunctionsSource context declarations)[n]? = some function := by
            simpa [compileFunctionsSource] using hcompiled
          obtain ⟨found, hfound, horigin⟩ := ih htail
          exact ⟨found, by simpa [functionDeclarations] using hfound, horigin⟩
      | name struct fields =>
          have htail :
              (compileFunctionsSource context declarations)[n]? = some function := by
            simpa [compileFunctionsSource] using hcompiled
          obtain ⟨found, hfound, horigin⟩ := ih htail
          exact ⟨found, by simpa [functionDeclarations] using hfound, horigin⟩

/-! The same indexed provenance at the public `compileToCrep` boundary. -/
theorem compileToCrep_getElem?_origin
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    {n : Nat} {function : CompiledFunction α}
    (hcompiled : (compileToCrep context declarations)[n]? = some function) :
    ∃ declaration : FunDecl α,
      (functionDeclarations declarations)[n]? = some declaration ∧
      function = compileFunDeclSource
        { context with functions := functionInfos declarations } declaration := by
  apply compileFunctionsSource_getElem?_origin
    ({ context with functions := functionInfos declarations }) declarations
  simpa [compileToCrep] using hcompiled

end Flapjack
