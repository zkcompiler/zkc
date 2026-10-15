module

public import Zkc.Source.Structured.Linking
public import Zkc.Source.Region

@[expose] public section

/-! Helper inlining in the shared region carrier. The premise identifies the
complete helper process at every actual argument tuple. Neither successful
lookup nor a Math annotation alone supplies that equation or implies totality.
The result retains stops, ordered results and the caller's lexical suffix. -/

namespace Zkc.Source.Structured

variable {F : Type} [CommRing F] [DecidableEq F]

/-- Replace one helper invocation with its renamed body under an explicit
lookup/body equation. Empty result lists and stopping bodies need no special
case: both sides bind the complete process to the same continuation. -/
theorem inline_invoke (table : Meanings F) (helper : Helper)
    (body : Region dialect helper.inputs helper.outputs)
    (lookup : ∀ actual : Values (scalarAssignment F) helper.inputs,
      invoke table helper actual = body.denote (meaning F table) actual.get)
    {Γ out : List Ty} (arguments : Operands Γ helper.inputs)
    (next : Region dialect (helper.outputs ++ Γ) out) :
    Region.Equivalent (meaning F table)
      (.letOp (.invoke helper) arguments .nil next)
      (.bind (body.rename arguments.get) next) := by
  intro env
  change (invoke table helper (Operands.eval env arguments)).bind
      (fun values => next.denote (meaning F table) (env.prepend values)) =
    ((body.rename arguments.get).denote (meaning F table) env).bind
      (fun values => next.denote (meaning F table) (env.prepend values))
  rw [lookup, Region.denote_rename]
  have actuals : @Eq (Environment (scalarAssignment F) helper.inputs)
      (Operands.eval env arguments).get (fun value => env (arguments.get value)) := by
    funext ty value
    exact Operands.get_eval env arguments value
  rw [actuals]

/-- Checked declaration membership and exact raw body equality discharge the
lookup premise, using the existing linking and helper-table frame laws. -/
theorem Payload.inline_body_view (payload : Payload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (body : Region dialect definition.inputs definition.outputs)
    (exactRaw : definition.raw = body.erase)
    {Γ out : List Ty} (arguments : Operands Γ definition.inputs)
    (next : Region dialect (definition.outputs ++ Γ) out) :
    Region.Equivalent (meaning F (payload.meanings F))
      (.letOp (.invoke definition.helper) arguments .nil next)
      (.bind (body.rename arguments.get) next) :=
  inline_invoke (payload.meanings F) definition.helper body
    (payload.invoke_body_view definition member body exactRaw) arguments next

end Zkc.Source.Structured
