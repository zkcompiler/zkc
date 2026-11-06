module

public import Zkc.Source.Structured.OracleBody
public import Zkc.Source.Structured.ReferenceLaws

@[expose] public section

/-! Install an ordinary mathematical rule into a virtual oracle's closed
helper environment. Complete concrete inputs and the actual captured source
definitions are required. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

theorem OracleMathEnvironment.invokePresent {I : PIR.Signature} {model : DomainModel} {helper : Helper}
    (math : OracleMathEnvironment) (law : ReferenceLaw model helper.inputs helper.outputs)
    (associated : BodyIn math.definitions helper law.body) (args : Values model.Value helper.inputs)
    (requires : law.Requires (closedMeaningsOn model math.definitions) args) :
    invoke (math.tables model I).components helper args.present =
      (primitiveOutcome (law.reference args) : PIR.Process I (Values model.Value helper.outputs)).bind
        fun values ↦ .done values.present := by
  have adequate := Evaluation.ComponentTablesOn.adequate_fold model (SiteObservations.silent I)
    ⟨[], []⟩ Evaluation.ComponentTablesOn.adequate_empty math.definitions
  exact (adequate helper args).trans (congrArg
    (fun p : PIR.Process I (Values model.Value helper.outputs) ↦ p.bind (fun values ↦ .done values.present))
    (law.invokeOn math.definitions math.linked associated args requires))

theorem OracleMathEnvironment.invokeReturned {I : PIR.Signature} {model : DomainModel} {helper : Helper}
    (math : OracleMathEnvironment) (law : ReferenceLaw model helper.inputs helper.outputs)
    (associated : BodyIn math.definitions helper law.body) (args : Values model.Value helper.inputs)
    (requires : law.Requires (closedMeaningsOn model math.definitions) args)
    (output : Values model.Value helper.outputs) (returned : law.reference args = .returned output) :
    invoke (math.tables model I).components helper args.present = .done output.present := by
  rw [math.invokePresent law associated args requires, returned]
  rfl

end Zkc.Source.Structured
