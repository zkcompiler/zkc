import Zkc.Source.DefinitionRenaming

/-! Optional inlining of an actual stored definition.

Both value captures and callee references are renamed. The caller continuation
is kept once using `Region.bind`; complete stopped executions are preserved.
This law does not authorize erasing call-site observations added by another
profile, bypassing role admission or replacing a callee with a same-typed body.
-/

set_option autoImplicit false

namespace Zkc.Compiler

open Zkc.Source

variable {language : Language} {interface : PIR.Signature}
variable {scope : List (DefinitionSignature language.Ty)}
variable {signature : DefinitionSignature language.Ty} {Γ : List language.Ty} {ty : language.Ty}

/-- Inline the newest definition. Stored body and actual argument map are explicit. -/
def inlineDefinition
    (body : Region (language.withDefinitions scope) signature.arguments signature.result)
    (args : Operands Γ signature.arguments)
    (next : Region (language.withDefinitions (signature :: scope)) (signature.result :: Γ) ty) :
    Region (language.withDefinitions (signature :: scope)) Γ ty :=
  .bind ((body.renameDefinitions Renaming.weaken).rename args.get) next

theorem denote_inlineDefinition (base : Interpretation language interface)
    (definitions : Definitions language scope)
    (body : Region (language.withDefinitions scope) signature.arguments signature.result)
    (args : Operands Γ signature.arguments)
    (next : Region (language.withDefinitions (signature :: scope)) (signature.result :: Γ) ty)
    (env : Environment base.Value Γ) :
    (inlineDefinition body args next).denote ((definitions.snoc signature body).meaning base) env =
      (Region.letOp (language := language.withDefinitions (signature :: scope))
        (.call .here) args next).denote ((definitions.snoc signature body).meaning base) env := by
  simp only [inlineDefinition, Region.denote, Definitions.meaning, Definitions.operation]
  congr 1
  rw [Region.denote_rename, Region.denote_weakenDefinitions]
  congr 1
  funext result value
  exact (Operands.get_eval env args value).symm

/-- Equality includes outcome, post-state and the whole event list for every handler. -/
theorem run_inlineDefinition (base : Interpretation language interface)
    (definitions : Definitions language scope)
    (body : Region (language.withDefinitions scope) signature.arguments signature.result)
    (args : Operands Γ signature.arguments)
    (next : Region (language.withDefinitions (signature :: scope)) (signature.result :: Γ) ty)
    {S E : Type} (handler : PIR.Handler interface S E)
    (env : Environment base.Value Γ) (state : S) :
    ((inlineDefinition body args next).denote
        ((definitions.snoc signature body).meaning base) env).run handler state =
      ((Region.letOp (language := language.withDefinitions (signature :: scope))
        (.call .here) args next).denote
        ((definitions.snoc signature body).meaning base) env).run handler state := by
  rw [denote_inlineDefinition]

end Zkc.Compiler
