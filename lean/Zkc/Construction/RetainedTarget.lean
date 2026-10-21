module

public import Zkc.Construction.Compiled
public import Zkc.Source.Structured.ContractMeaning

@[expose] public section

/-! Deterministic application meaning at a compiled policy boundary. A target
selects an actual clause and formula of the admitted Entry. Parameters and
statements are read only from policy publications; witnesses are shared logical
assignments to private producer inputs. No execution or reachability claim is
made by this reading. -/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source Zkc.Source.Structured

/-- The supported endpoint boundary is deliberately narrow. Every purpose must
be present and recognized. Witnesses cannot alias a published input, even at a
different role. All other arguments are publications at the validator role. -/
def targetSelectorsSupported {signature : ProtocolSignature} :
    Policy → List String → {types : List Ty} → Values (BoundarySelector signature) types → Bool
  | _, [], _, .nil => true
  | policy, purpose :: purposes, _, .cons selector rest =>
      (match selector.port with
      | .input ref =>
          match purpose with
          | "parameter" | "statement" =>
              signature.roles.get selector.role == policy.validator && policy.publicInputs.contains ref.index
          | "witness" =>
              signature.roles.get selector.role == policy.producer && !policy.publicInputs.contains ref.index
          | _ => false
      | .output _ => false) && targetSelectorsSupported policy purposes rest
  | _, _, _, _ => false

/-- A retained Boolean formula target of the admitted Entry, with an exact
policy layout and acceptance selector. Unsupported boundaries have no value of
this type. Its meaning is independent of any probabilistic evidence. -/
structure RetainedTarget {snapshot : Structured.Snapshot} (imported : Structured.Imported snapshot)
    (policy : Policy) (publics : List Ty) where
  owner : ContractBinding imported
  entry : owner.protocol = imported.program.payload.entry
  clauseIndex : Fin owner.contract.clauses.length
  target : (owner.clause clauseIndex).kind = .target
  noResidual : (owner.clause clauseIndex).residual = none
  decision : (owner.clause clauseIndex).decision =
    some ⟨.output, policy.acceptance, policy.validator⟩
  application : ApplicationBinding owner (owner.clause clauseIndex).subject
  formula : FormulaBinding imported application.relation
  booleanOutput : application.relation.declaration.outputs = [.boolean]
  publicTypes : publics = policy.publicInputs.filterMap (imported.program.payload.entry.inputs[·]?)
  publicArity : publics.length = policy.publicInputs.length
  supported : targetSelectorsSupported policy application.relation.declaration.purposes application.selectors = true

namespace RetainedTarget
variable {snapshot : Structured.Snapshot} {imported : Structured.Imported snapshot}
  {policy : Policy} {publics : List Ty} (target : RetainedTarget imported policy publics)
  {F G : Type}

/-- Witness coordinates preserve type, input position and role. Repeated
selectors share a value. Missing coordinates do not satisfy the relation. -/
abbrev Witness (F G : Type) :=
  (type : Ty) → BoundarySelector target.owner.protocol.signature type → Option (assignment F G type)

/-- A typed input read uses the original input's index in the policy's ordered
publications. It never consults a witness or a mathematical model decoder. -/
def published (_target : RetainedTarget imported policy publics)
    (statement : Values (assignment F G) publics) (type : Ty) (index : Nat) :
    Option (assignment F G type) := do
  let position ← policy.publicInputs.idxOf? index
  let value ← (encodeValues statement)[position]?
  Value.decode type value

def publishedInputs (target : RetainedTarget imported policy publics)
    (statement : Values (assignment F G) publics) :
    (types : List Ty) → Nat → Values (Component (assignment F G)) types
  | [], _ => .nil
  | type :: rest, index => .cons (target.published statement type index)
      (publishedInputs target statement rest (index + 1))

/-- The policy boundary contains the validator's published inputs and no
outputs. The target's support proof rules out reading any other boundary port. -/
def boundary (statement : Values (assignment F G) publics) :
    BoundaryValuation (assignment F G) target.owner.protocol.inputs target.owner.protocol.outputs where
  inputs self :=
    if target.owner.protocol.roles[self]? = some policy.validator then
      target.publishedInputs statement target.owner.protocol.inputs 0
    else Values.absent (assignment F G) _
  outputs _ := Values.absent (assignment F G) _

/-- Parameters have exactly the policy's meaning. The only authored part is the
witness assignment, and support checking prevents it from replacing a public. -/
def assignments (statement : Values (assignment F G) publics) (witness : target.Witness F G) :
    LogicalAssignments (assignment F G) target.owner ⟨target.owner.protocolIndex.val, []⟩ where
  parameters type selector := match selector.port with
    | .input ref => target.published statement type ref.index
    | .output _ => none
  witnesses := witness

def arguments (statement : Values (assignment F G) publics) (witness : target.Witness F G) :
    Option (Values (assignment F G) target.application.relation.declaration.inputs) :=
  target.application.read {} (target.boundary statement) (target.assignments statement witness)

variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- Truth requires an actual ordered application read and a completed true
formula invocation. A stop is not identified with a completed false result. -/
def Holds (statement : Values (assignment F G) publics) (witness : target.Witness F G) : Prop :=
  ∃ arguments, target.arguments statement witness = some arguments ∧
    target.formula.invokeRelation arguments = .done (target.booleanOutput.symm ▸ .cons true .nil)

/-- Once the exact ordered application read is proved, relation truth is the
actual formula invocation. Reusing this implication does not discharge the
public-input or witness-selection correspondence itself. -/
theorem holds_iff_of_arguments
    (statement : Values (assignment F G) publics) (witness : target.Witness F G)
    (inputs : Values (assignment F G) target.application.relation.declaration.inputs)
    (read : target.arguments statement witness = some inputs) :
    target.Holds statement witness ↔
      target.formula.invokeRelation inputs = .done (target.booleanOutput.symm ▸ .cons true .nil) := by
  simp only [Holds, read, Option.some.injEq]
  constructor
  · rintro ⟨arguments, rfl, truth⟩
    exact truth
  · intro truth
    exact ⟨inputs, rfl, truth⟩

/-- Negation of existence of a target witness, over all shared logical witness
assignments. It does not quantify an authored witness embedding or a parameter. -/
def FalseStatement (statement : Values (assignment F G) publics) : Prop :=
  ¬ ∃ witness, target.Holds statement witness

end RetainedTarget
end Zkc.Construction
