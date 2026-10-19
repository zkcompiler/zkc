module

public import Zkc.Source.Structured.Linking
public meta import Lean.Elab.Tactic.Basic

@[expose] public section

namespace Zkc.Source.Structured

/-- Construct an association from an actual declaration and its exact ABI and
raw tree. The typed view's input and output contexts are fixed by that ABI. -/
theorem BodyIn.of_mem {definitions : List CheckedDefinition}
    {definition : CheckedDefinition} {helper : Helper}
    {body : Region dialect helper.inputs helper.outputs}
    (member : definition ∈ definitions) (signature : definition.helper = helper)
    (exactRaw : definition.raw = body.erase) : BodyIn definitions helper body :=
  ⟨definition, member, signature, exactRaw⟩

/-- Reordering declarations preserves exact association. Invocation still
requires a separate linking proof for the reordered list. -/
theorem BodyIn.perm {definitions reordered : List CheckedDefinition}
    {helper : Helper} {body : Region dialect helper.inputs helper.outputs}
    (association : BodyIn definitions helper body) (order : definitions.Perm reordered) :
    BodyIn reordered helper body := by
  obtain ⟨definition, member, signature, exactRaw⟩ := association
  exact BodyIn.of_mem (order.mem_iff.mp member) signature exactRaw

/-- Prove membership in a concrete list using only its constructors. No equality
decision procedure or evaluation of an entire imported unit is used. -/
syntax "structured_mem" : tactic
macro_rules
  | `(tactic| structured_mem) =>
    `(tactic| first
      | exact List.mem_cons_self
      | (apply List.mem_cons_of_mem; structured_mem))

/-- Associate an explicit checked declaration with the goal's typed body.
Membership is constructed from the list; the full signature and raw body must
both be definitionally equal. A matching name alone cannot close this tactic. -/
macro "exact_body " definition:term : tactic =>
  `(tactic| exact BodyIn.of_mem (definition := $definition)
    (by structured_mem) (by rfl) (by rfl))

end Zkc.Source.Structured
