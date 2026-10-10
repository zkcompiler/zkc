import Zkc.Source.Definitions

/-! Capture-safe changes of definition scope, separate from value-variable renaming.

The preservation premise concerns the actual selected callee bodies. Matching
signatures alone do not make two definitions interchangeable.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {language : Language} {interface : PIR.Signature}
variable {scope target : List (DefinitionSignature language.Ty)}

def Region.renameDefinitions (references : Renaming scope target) {Γ : List language.Ty}
    {ty : language.Ty} :
    Region (language.withDefinitions scope) Γ ty → Region (language.withDefinitions target) Γ ty
  | .ret value => .ret value
  | .stop reason => .stop reason
  | .letOp (.primitive op) args next =>
      .letOp (.primitive op) args (next.renameDefinitions references)
  | .letOp (.call callee) args next =>
      .letOp (.call (references callee)) args (next.renameDefinitions references)
  | .branch condition yes no =>
      .branch condition (yes.renameDefinitions references) (no.renameDefinitions references)
  | .iterate count initial body next =>
      .iterate count initial (body.renameDefinitions references) (next.renameDefinitions references)
  | .bind body next =>
      .bind (body.renameDefinitions references) (next.renameDefinitions references)

theorem Region.denote_renameDefinitions (base : Interpretation language interface)
    (sourceDefinitions : Definitions language scope)
    (targetDefinitions : Definitions language target)
    (references : Renaming scope target)
    (calls : ∀ {signature : DefinitionSignature language.Ty} (ref : Var scope signature)
      (args : Values base.Value signature.arguments),
      targetDefinitions.operation base (.call (references ref)) args =
        sourceDefinitions.operation base (.call ref) args)
    {Γ : List language.Ty} {ty : language.Ty}
    (body : Region (language.withDefinitions scope) Γ ty) (env : Environment base.Value Γ) :
    (body.renameDefinitions references).denote (targetDefinitions.meaning base) env =
      body.denote (sourceDefinitions.meaning base) env := by
  induction body using Region.rec (language := language.withDefinitions scope) with
  | ret value => rfl
  | stop reason => rfl
  | letOp op args next ih =>
      cases op with
      | primitive op =>
          simp only [renameDefinitions, denote, Definitions.meaning,
            Definitions.operation_primitive]
          congr 1
          funext value
          exact ih (env.push value)
      | call ref =>
          simp only [renameDefinitions, denote, Definitions.meaning, calls]
          congr 1
          funext value
          exact ih (env.push value)
  | branch condition yes no yesIH noIH =>
      simp only [renameDefinitions, denote, yesIH, noIH]
  | iterate count initial body next bodyIH nextIH =>
      simp only [renameDefinitions, denote, bodyIH, nextIH]
  | bind body next bodyIH nextIH =>
      simp only [renameDefinitions, denote, bodyIH, nextIH]

/-- Adding a definition preserves every earlier body at its shifted reference. -/
theorem Region.denote_weakenDefinitions (base : Interpretation language interface)
    (definitions : Definitions language scope) (signature : DefinitionSignature language.Ty)
    (added : Region (language.withDefinitions scope) signature.arguments signature.result)
    {Γ : List language.Ty} {ty : language.Ty}
    (body : Region (language.withDefinitions scope) Γ ty) (env : Environment base.Value Γ) :
    (body.renameDefinitions Renaming.weaken).denote
        ((definitions.snoc signature added).meaning base) env =
      body.denote (definitions.meaning base) env :=
  denote_renameDefinitions base definitions (definitions.snoc signature added)
    Renaming.weaken (fun _ _ => rfl) body env

end Zkc.Source
