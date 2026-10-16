module

public import Zkc.Source.Structured.Operations
public import Zkc.Source.Structured.ProtocolSignature

@[expose] public section

namespace Zkc.Source.Structured

/-- The open calculation boundary excludes Local calls and closed control.
Exact signatures retain the kind; a hand-built Local reference cannot inhabit
this view. Admission separately checks the kind of every stored helper body. -/
def Op.isCalculation : Op → Bool
  | .indexConstant .. | .indexEqual | .fieldConstant .. | .fieldAdd .. | .fieldSubtract .. | .fieldMultiply .. |
    .fieldEqual .. | .groupIdentity .. | .groupAdd .. | .groupScale .. | .groupEqual .. |
    .booleanConstant .. | .booleanAnd | .booleanOr | .booleanXor | .booleanEqual |
    .booleanNotEqual | .select .. | .boundedAt .. => true
  | .invoke helper => helper.kind == .math
  | .fold spec => spec.kind == .math
  | _ => false

theorem Op.calculation_no_regions (op : Op) (allowed : op.isCalculation = true) :
    op.regions = [] := by
  cases op <;> simp_all [Op.isCalculation, Op.regions]

/-- Protocol roots have their own operation family, on the same Region carrier.
Role indices are resolved against the containing root's roster, never global. -/
inductive ProtocolOp where
  | calculate (op : Op) (allowed : op.isCalculation = true)
  | localCall (helper : Helper) (localKind : helper.kind = .local) (owner : Nat) (site : String)
  | guard (owner : Nat) (site : String)
  | exchange (type : Ty) (sender receiver : Nat) (site : String)
  | restrict (type : Ty) (roles : List Nat)
  | draw (owner : Nat) (field site : String)
  | statement (relation : String) (types : List Ty) (selectors : List String) (acceptance : Nat)
  | mark (site : String)
  | protocolApply (callee : ProtocolSignature) (roles : List Nat) (site : String)

def ProtocolOp.arguments : ProtocolOp → List Ty
  | .calculate op _ => op.arguments
  | .localCall helper .. => helper.inputs
  | .protocolApply callee .. => callee.inputs
  | .guard .. => [.boolean]
  | .exchange ty .. | .restrict ty .. => [ty]
  | .draw _ field _ => [.service ("random." ++ field ++ "/0")]
  | .statement _ types .. => types
  | .mark _ => []

def ProtocolOp.results : ProtocolOp → List Ty
  | .calculate op _ => op.results
  | .localCall helper .. => helper.outputs
  | .protocolApply callee .. => callee.outputs
  | .guard .. | .statement .. | .mark _ => []
  | .exchange ty .. | .restrict ty .. => [ty]
  | .draw _ field _ => [.field field]

def ProtocolOp.helpers : ProtocolOp → List Helper
  | .calculate op _ => op.helpers
  | .localCall helper .. => [helper]
  | _ => []

def ProtocolOp.protocols : ProtocolOp → List ProtocolSignature
  | .protocolApply callee .. => [callee]
  | _ => []

/-- Current operations have no callbacks; future callbacks use the same carrier. -/
def ProtocolOp.regions : ProtocolOp → List (List Ty × List Ty)
  | _ => []

abbrev protocolDialect : Dialect :=
  ⟨Ty, ProtocolOp, ProtocolOp.arguments, ProtocolOp.results, ProtocolOp.regions⟩

end Zkc.Source.Structured
