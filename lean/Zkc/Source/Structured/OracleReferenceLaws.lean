module

public import Zkc.Source.Structured.ProtocolEmbeddingSource
public import Zkc.Source.Structured.ReferenceLaws

@[expose] public section

/-! Reuse an ordinary mathematical body law in the lazy logical-oracle participant.
The actual retained helper closure supplies both evaluations. The all-concrete operand
boundary is explicit; no law is claimed for arbitrary deferred table data. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.ReferenceLaw
open ProtocolEmbedding

/-- Install an existing mathematical companion law on concrete values in the actual
Oracle helper table. The enclosing protocol may contain Oracle effects. Only its Math
closure is checked for the ordinary fragment, and its original premises stay unchanged. -/
theorem invokeOracleConcrete {model : DomainModel} {helper : Helper}
    (law : ReferenceLaw model helper.inputs helper.outputs)
    (payload : UnitPayload) (self : Nat)
    (math : helper.kind = .math)
    (fragment : MathFragment payload.definitions)
    (linked : DeclarationsLinked [] payload.definitions)
    (associated : BodyIn payload.definitions helper law.body)
    (arguments : Values model.Value helper.inputs)
    (premises : law.Requires
      (payload.definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      arguments) :
    Structured.invoke (payload.oracleCalculations model self) helper
      (ProtocolValue.embedComponents arguments.present) =
      (primitiveOutcome (law.reference arguments) :
        PIR.Process (OracleProtocol.Interface model) (Values model.Value helper.outputs)).bind
        (fun results ↦ .done (ProtocolValue.embedComponents results.present)) := by
  have related := payload_math_related payload model self fragment helper math arguments.present
  rw [ordinary_tables_adequate payload model helper arguments] at related
  have installed := law.invokeOn (I := OracleProtocol.Interface model)
    payload.definitions linked associated arguments premises
  dsimp only [ordinaryTables] at related
  rw [installed] at related
  simpa only [PIR.Process.bind_assoc, PIR.Process.bind] using related

end Zkc.Source.Structured.ReferenceLaw
