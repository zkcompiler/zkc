module

public import Zkc.Source.Structured.DomainLinking

@[expose] public section

/-! Present operands connect the two actual nominal helper tables.

Each declaration captures the same prefix on both sides. The proof uses the
existing region evaluator and preserves the entire process, including every
stop and every possible reply to an observation. No helper result law is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Source.Structured.Evaluation
variable (model : DomainModel) {interface : PIR.Signature}

/-- Exact kept-helper semantics on present inputs, including Math helpers.
The original definitions supply both closures and their dependency prefixes.
Optional Math inputs and transformed/inlined helper bodies are not covered.
-/
theorem component_invoke_closed (definitions : List CheckedDefinition) (helper : Helper)
    (arguments : Values model.Value helper.inputs) :
    componentOperationOn model (.silent interface)
        (definitions.foldl (ComponentTablesOn.extend model (.silent interface)) ⟨[], []⟩)
        (.invoke helper) arguments.present .nil =
      ((invoke (definitions.foldl (extendMeaningsOn model SiteObservations.closed) [])
        helper arguments).interpret (closedLift (I := interface))).bind
          (fun results => .done results.present) := by
  refine (componentOperationOn_adequate model (.silent interface) _
    (ComponentTablesOn.adequate_fold model _ _ ComponentTablesOn.adequate_empty definitions)
    (.invoke helper) arguments .nil).trans ?_
  change (invoke _ helper arguments).bind _ = _
  rw [closed_invoke_componentTablesOn]
  rfl

end Zkc.Source.Structured.Evaluation
