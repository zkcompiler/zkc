module

public import Zkc.IR.Source.Structured.OracleProtocol
public import Zkc.IR.Source.Structured.OracleLaws

@[expose] public section

/-! Oracle action laws for the value-parameterized residual normalizer. The target is the
existing PIR.Process. Callback and suffix proofs compose through Region.Derivation;
these laws neither select whole-body meanings nor require concrete holder data. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace OracleProtocol

variable (model : DomainModel)

theorem operationLaw (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (Interface model))
    (protocols : ProtocolTable (ProtocolValue model.toCarriers) (Interface model))
    (context : ProtocolContext) (op : OracleOp) (location : OracleLocation)
    (args : Values (Component (ProtocolValue model.toCarriers)) op.arguments) :
    ((algebra model self ordinary helpers).meaning protocols context self).OperationLaw
      (fun action ↦ .call action .done) (.oracle op location) args .nil
      (.call (.oracle ⟨op, location, self, context.roles, args⟩) .done) :=
  RegionMeaning.OperationLaw.identity
    (meaning := (algebra model self ordinary helpers).meaning protocols context self)
    (ProtocolOp.oracle op location) args .nil rfl

/-- Every logical constructor, query, shape action and sequence action has the same typed
local rule. The actual handler retains its refusal/stop/poststate behavior. -/
theorem normalize_oracle (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (Interface model))
    (protocols : ProtocolTable (ProtocolValue model.toCarriers) (Interface model))
    (context : ProtocolContext) {inputs outputs : List Ty} (op : OracleOp)
    (location : OracleLocation) (args : Operands inputs op.arguments)
    (next : Region protocolDialect (op.results ++ inputs) outputs)
    (env : Environment (Component (ProtocolValue model.toCarriers)) inputs) :
    (NormalForm.normalizeActions
      ((algebra model self ordinary helpers).meaning protocols context self)
      (.letOp (.oracle op location) args .nil next) env).process =
    .call (.oracle ⟨op, location, self, context.roles, Operands.eval env args⟩)
      (fun values ↦ (NormalForm.normalizeActions
        ((algebra model self ordinary helpers).meaning protocols context self)
        next (env.prepend values)).process) := rfl

/-- A complete generic source-body certificate. In particular the suffix is required for
all handler replies, with every optional component retained, rather than only honest reads. -/
def normalize {inputs outputs : List Ty} (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (Interface model))
    (protocols : ProtocolTable (ProtocolValue model.toCarriers) (Interface model))
    (context : ProtocolContext) (body : Region protocolDialect inputs outputs)
    (env : Environment (Component (ProtocolValue model.toCarriers)) inputs) :=
  NormalForm.normalizeActions ((algebra model self ordinary helpers).meaning protocols context self)
    body env

/-- Ordered logical audit events are part of this equality, separate from a public transcript. -/
theorem normalize_run {inputs outputs : List Ty} (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (Interface model))
    (protocols : ProtocolTable (ProtocolValue model.toCarriers) (Interface model))
    (context : ProtocolContext) (body : Region protocolDialect inputs outputs)
    (env : Environment (Component (ProtocolValue model.toCarriers)) inputs)
    {S E : Type} (handler : PIR.Handler (Interface model) S E) (state : S) :
    ((normalize model self ordinary helpers protocols context body env).process).run handler state =
      (body.denote ((algebra model self ordinary helpers).meaning protocols context self) env).run
        handler state :=
  (normalize model self ordinary helpers protocols context body env).run handler state

end OracleProtocol
end Zkc.Source.Structured
