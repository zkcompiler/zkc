module

public import Zkc.Source.Structured.ComponentExport
public import Zkc.Source.Structured.ContractComposition
public import Zkc.Source.Structured.RelationMeaning
public import Zkc.Obligations.ClaimRelation

@[expose] public section

/-! Kernel-facing bridges for associated component exports. No wire name,
canonical route, or open search proposal is a mathematical law. These records
select existing checked applications, assignments, relation meanings and helper
processes. The library supplies the remaining laws. -/
namespace Zkc.Source.Structured
open Zkc.Source

variable {snapshot : Snapshot} {imported : Imported snapshot}
  {wire : ComponentExport.Export}

/-- A proposal binds to the real typed occurrence, including its complete SSA
context, operands and role substitution. The derived context is selected from
the exact recomputation; it is not a subject-owned routing table. -/
structure CallProposalBinding (associated : ComponentExport.Associated snapshot wire)
    (index : Fin wire.proposals.length) where
  contextIndex : Fin associated.derived.calls.length
  contextHeader : (associated.derived.calls.get contextIndex).proposal.caller = (wire.proposals.get index).caller
  contextSite : (associated.derived.calls.get contextIndex).proposal.site = (wire.proposals.get index).site
  contextTypes : List Ty
  context_eq : (associated.derived.calls.get contextIndex).types = contextTypes
  callee : ContractBinding imported
  call : CheckedApplication callee contextTypes
  caller_eq : (wire.proposals.get index).caller = call.caller.protocol.name
  callee_eq : (wire.proposals.get index).callee = callee.protocol.name
  site_eq : (wire.proposals.get index).site = call.site
  operands_eq : (wire.proposals.get index).operands = call.operands.indices
  roles_eq : (wire.proposals.get index).roles =
    call.roles.map (fun role => call.caller.protocol.signature.roles[role]?.getD "")

namespace CallProposalBinding

def proposal {associated : ComponentExport.Associated snapshot wire} {index : Fin wire.proposals.length}
    (_binding : CallProposalBinding (imported := imported) associated index) : CallProposal :=
  wire.proposals.get index

def context {associated : ComponentExport.Associated snapshot wire} {index : Fin wire.proposals.length}
    (binding : CallProposalBinding (imported := imported) associated index) : ComponentRoutes.ProposalContext :=
  associated.derived.calls.get binding.contextIndex

variable {associated : ComponentExport.Associated snapshot wire} {index : Fin wire.proposals.length}
  (binding : CallProposalBinding (imported := imported) associated index)
  {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
  {invocation : InvocationCoordinate}
  (protocolContext : ProtocolContext)
  (boundary : BoundaryValuation (assignment F G) binding.call.caller.protocol.inputs binding.call.caller.protocol.outputs)
  (assignments : LogicalAssignments (assignment F G) binding.call.caller invocation)
  (observations : Nat → Environment (Component (assignment F G)) binding.contextTypes)

/-- Resolution uses the existing assignment reader and actual helper invocation.
`open` explicitly delegates to Lean. Every non-open runtime value needs a typed
`some` observation. There is no default value and no second term evaluator.
The consumer must relate `observations` to its reached execution. -/
inductive SourceResolution : {type : Ty} → InstantiationSource →
    AssignmentSource (assignment F G) binding.call.caller type → Type where
  | open {type} (selected : AssignmentSource (assignment F G) binding.call.caller type) :
      SourceResolution (.open) selected
  | parameter {type} (selector : BoundarySelector binding.call.caller.protocol.signature type) :
      SourceResolution (.parameter selector.erase) (.parameter selector)
  | witness {type} (selector : BoundarySelector binding.call.caller.protocol.signature type) :
      SourceResolution (.witness selector.erase) (.witness selector)
  | operand {type} (ref : Var binding.callee.protocol.inputs type)
      (holder : Fin binding.call.caller.protocol.signature.roles.length)
      (value : assignment F G type)
      (observed : observations (protocolContext.roles holder) (binding.call.operands.get ref) = some value) :
      SourceResolution (.operand ref.index (binding.call.caller.protocol.signature.roles.get holder)) (.supplied value)
  | result {type} (actionIndex : Fin binding.context.visible.length)
      (port : Nat) (ref : Var binding.contextTypes type)
      (sameIndex : ref.index = (binding.context.visible.get actionIndex).offset + port)
      (sameType : (binding.context.visible.get actionIndex).types[port]? = some type)
      (holder : Fin binding.call.caller.protocol.signature.roles.length)
      (value : assignment F G type)
      (observed : observations (protocolContext.roles holder) ref = some value) :
      SourceResolution (.result (binding.context.visible.get actionIndex).site port
        (binding.call.caller.protocol.signature.roles.get holder)) (.supplied value)
  | math {type} (helperIndex : Fin imported.program.payload.definitions.length)
      (mathKind : (imported.program.payload.definitions.get helperIndex).kind = .math)
      (arguments : List InstantiationSource)
      (sources : Values (AssignmentSource (assignment F G) binding.call.caller)
        (imported.program.payload.definitions.get helperIndex).inputs)
      (count : arguments.length = (imported.program.payload.definitions.get helperIndex).inputs.length)
      (resolved : ∀ {argumentType} (ref : Var (imported.program.payload.definitions.get helperIndex).inputs argumentType),
        SourceResolution (arguments[ref.index]?.getD .open) (sources.get ref))
      (values : Values (assignment F G) (imported.program.payload.definitions.get helperIndex).inputs)
      (defined : ∀ {argumentType} (ref : Var (imported.program.payload.definitions.get helperIndex).inputs argumentType),
        (sources.get ref).read protocolContext boundary assignments = some (values.get ref))
      (results : Values (assignment F G) (imported.program.payload.definitions.get helperIndex).outputs)
      (returned : invoke (closedMeanings imported.program.payload.definitions)
        (imported.program.payload.definitions.get helperIndex).helper values = .done results)
      (output : Var (imported.program.payload.definitions.get helperIndex).outputs type) :
      SourceResolution (.math (imported.program.payload.definitions.get helperIndex).name output.index arguments)
        (.supplied (results.get output))

/-- One instantiation of the existing logical assignment. Repeated selectors
read the same chosen source. Availability at a continuing call remains an
explicit obligation; an open/unavailable source does not discharge it. -/
structure ResolvedInstantiation where
  assignment : AssignmentInstantiation (assignment F G) binding.call
  parameters : ∀ {type} (selector : BoundarySelector binding.callee.protocol.signature type)
    (slot : InstantiationSlot), slot ∈ binding.proposal.slots → slot.purpose = "parameter" →
    slot.selector = selector.erase → SourceResolution binding protocolContext boundary assignments observations
      slot.source (assignment.parameters type selector)
  witnesses : ∀ {type} (selector : BoundarySelector binding.callee.protocol.signature type)
    (slot : InstantiationSlot), slot ∈ binding.proposal.slots → slot.purpose = "witness" →
    slot.selector = selector.erase → SourceResolution binding protocolContext boundary assignments observations
      slot.source (assignment.witnesses type selector)

end CallProposalBinding

namespace SeamRoute

def subroutes (route : SeamRoute) : List SeamRoute :=
  route :: match route with
    | .pure _ _ _ _ arguments | .terminal _ _ _ _ arguments
    | .action _ _ _ _ arguments => arguments.flatMap subroutes
    | _ => []

end SeamRoute

/-- The source operation must call this exact helper in its admitted mode.
A Local call also retains the holder whose runtime values it can observe. -/
inductive HelperCall (helper : Helper) (holder : String) : Descriptor → Prop where
  | math (kind : helper.kind = .math) : HelperCall helper holder (.call helper.name)
  | local (kind : helper.kind = .local) : HelperCall helper holder (.localCall helper.name holder)

/-- A selected exact Math or Local body in an associated pure row. Its source/target relation
bindings and the registered mathematical map are indices supplied by the
library, so this evidence cannot assign different relation meanings. -/
structure PureSeamBinding (associated : ComponentExport.Associated snapshot wire)
    (row : Fin wire.seams.length) where
  helperIndex : Fin imported.program.payload.definitions.length
  position : List Nat
  result : Nat
  role : String
  operation : Descriptor
  invocation : HelperCall (imported.program.payload.definitions.get helperIndex).helper role operation
  arguments : List SeamRoute
  occurs : SeamRoute.pure operation
    position result role arguments ∈ (wire.seams.get row).routes.flatMap SeamRoute.subroutes

/-- A fixed encoding connects the request's meaning to an independently fixed
claim. Every affirmative witness must be in the encoding domain. Outside that
domain no claim witness can be manufactured by a vacuous local equation. -/
def RelationMeaning.RealizesClaim {application : RelationApplication}
    {relation : RelationBinding snapshot application} {model : DomainModel}
    {registry : OpaqueRegistry model.Value} (meaning : RelationMeaning imported relation model.Value registry)
    {S W : Type} (claim : Obligations.ClaimRelation S W)
    (booleanOutput : relation.declaration.outputs = [.boolean])
    (encode : S → W → Values model.Value relation.declaration.inputs)
    (domain : S → W → Prop) : Prop :=
  ∀ statement witness, claim.Holds statement witness ↔
    domain statement witness ∧ meaning.HoldsOn booleanOutput (encode statement witness)

/-- Rejection on the encoding domain follows from disjointness, without
assuming that the claim's possibly gapped No side is the complement of Yes. -/
theorem RelationMeaning.RealizesClaim.rejects_no {application : RelationApplication}
    {relation : RelationBinding snapshot application} {model : DomainModel}
    {registry : OpaqueRegistry model.Value} {meaning : RelationMeaning imported relation model.Value registry}
    {S W : Type} {claim : Obligations.ClaimRelation S W}
    {booleanOutput : relation.declaration.outputs = [.boolean]}
    {encode : S → W → Values model.Value relation.declaration.inputs} {domain : S → W → Prop}
    (law : meaning.RealizesClaim claim booleanOutput encode domain)
    (statement : S) (witness : W) (no : claim.No statement) (inside : domain statement witness) :
    ¬ meaning.HoldsOn booleanOutput (encode statement witness) :=
  fun truth => claim.no_excludes statement witness no ((law statement witness).mpr ⟨inside, truth⟩)

/-- Totality and the readback square concern the actual selected helper process.
No transport is a separate field, even when Yes predicates are equivalent. No
claim below converts a gapped No set into the complement of Yes. -/
structure PureSeamLaw {associated : ComponentExport.Associated snapshot wire}
    {row : Fin wire.seams.length} (binding : PureSeamBinding (imported := imported) associated row)
    {left right : RelationApplication}
    (source : RelationBinding snapshot left) (target : RelationBinding snapshot right)
    {S W T U : Type} (sourceRelation : Obligations.ClaimRelation S W)
    (targetRelation : Obligations.ClaimRelation T U) (map : S → T)
    {model : DomainModel} {registry : OpaqueRegistry model.Value}
    (domain : Values model.Value (imported.program.payload.definitions.get binding.helperIndex).inputs → Prop)
    (runtimeMap : Values model.Value (imported.program.payload.definitions.get binding.helperIndex).inputs →
      Values model.Value (imported.program.payload.definitions.get binding.helperIndex).outputs)
    (sourceReadback : Values model.Value (imported.program.payload.definitions.get binding.helperIndex).inputs → Option S)
    (targetReadback : Values model.Value (imported.program.payload.definitions.get binding.helperIndex).outputs → Option T)
    (sourceMeaning : RelationMeaning imported source model.Value registry)
    (targetMeaning : RelationMeaning imported target model.Value registry)
    (sourceOutput : source.declaration.outputs = [.boolean])
    (targetOutput : target.declaration.outputs = [.boolean])
    (sourceEncoding : S → W → Values model.Value source.declaration.inputs)
    (targetEncoding : T → U → Values model.Value target.declaration.inputs)
    (sourceDomain : S → W → Prop) (targetDomain : T → U → Prop) where
  sourceRealizes : sourceMeaning.RealizesClaim sourceRelation sourceOutput sourceEncoding sourceDomain
  targetRealizes : targetMeaning.RealizesClaim targetRelation targetOutput targetEncoding targetDomain
  /-- The caller must establish this domain at the reached state, independently
  of the false-claim premise. Outside it the actual helper may stop. -/
  total : ∀ arguments, domain arguments → invoke (closedMeaningsOn model imported.program.payload.definitions)
    (imported.program.payload.definitions.get binding.helperIndex).helper arguments = .done (runtimeMap arguments)
  defined : ∀ arguments, domain arguments → ∃ statement, sourceReadback arguments = some statement
  readback : ∀ arguments statement, domain arguments → sourceReadback arguments = some statement →
    targetReadback (runtimeMap arguments) = some (map statement)
  yes : ∀ statement, sourceRelation.token.Yes statement ↔ targetRelation.token.Yes (map statement)
  no : sourceRelation.SoundLink targetRelation map

/-- A terminal's Boolean reaches acceptance only directly or through actual
conjunction nodes. Merely occurring under another Boolean operation is not an
acceptance link. -/
inductive AcceptancePath (terminal : SeamRoute) : SeamRoute → Prop where
  | here : AcceptancePath terminal terminal
  | left {first second : SeamRoute} (position : List Nat) (port : Nat) (role : String)
      (path : AcceptancePath terminal first) :
      AcceptancePath terminal (.pure .booleanAnd position port role [first, second])
  | right {first second : SeamRoute} (position : List Nat) (port : Nat) (role : String)
      (path : AcceptancePath terminal second) :
      AcceptancePath terminal (.pure .booleanAnd position port role [first, second])

/-- Apply the structural path to actual Boolean observations. The only
operation equation used is the admitted conjunction; no route evaluator or
alternative logical store is introduced. -/
theorem AcceptancePath.sound {terminal root : SeamRoute} (path : AcceptancePath terminal root)
    (observed : SeamRoute → Bool)
    (conjunction : ∀ position port role first second,
      observed (.pure .booleanAnd position port role [first, second]) =
        (observed first && observed second)) :
    observed root = true → observed terminal = true := by
  induction path with
  | here => exact id
  | left position port role path ih =>
    intro accepted
    rw [conjunction] at accepted
    simp only [Bool.and_eq_true_iff] at accepted
    exact ih accepted.1
  | right position port role path ih =>
    intro accepted
    rw [conjunction] at accepted
    simp only [Bool.and_eq_true_iff] at accepted
    exact ih accepted.2

/-- A terminal key contains the exact admitted helper and the actual route to a
checked acceptance output. A same-named body from another unit cannot fill it. -/
structure TerminalSeamBinding (associated : ComponentExport.Associated snapshot wire)
    (row : Fin wire.seams.length) where
  helperIndex : Fin imported.program.payload.definitions.length
  position : List Nat
  result : Nat
  role : String
  operation : Descriptor
  invocation : HelperCall (imported.program.payload.definitions.get helperIndex).helper role operation
  arguments : List SeamRoute
  output : Var (imported.program.payload.definitions.get helperIndex).outputs .boolean
  output_eq : output.index = result
  terminal : (wire.seams.get row).kind = .terminal
  exit : ∃ port clause, (wire.seams.get row).endpoint = .output port clause
  acceptance : ∃ root ∈ (wire.seams.get row).routes, AcceptancePath
    (.terminal operation
      position result role arguments) root
  occurs : SeamRoute.terminal operation
    position result role arguments ∈ (wire.seams.get row).routes.flatMap SeamRoute.subroutes

/-- The library's terminal adequacy law is about the exact selected helper.
Stops supply no accepting result. Definedness and the selected relation are
explicit; an absent readback cannot manufacture truth. -/
structure TerminalSeamLaw {associated : ComponentExport.Associated snapshot wire}
    {row : Fin wire.seams.length} (binding : TerminalSeamBinding (imported := imported) associated row)
    {application : RelationApplication} (relation : RelationBinding snapshot application)
    {S W : Type} (meaning : Obligations.ClaimRelation S W)
    {model : DomainModel} {registry : OpaqueRegistry model.Value}
    (domain : Values model.Value (imported.program.payload.definitions.get binding.helperIndex).inputs → Prop)
    (readback : Values model.Value (imported.program.payload.definitions.get binding.helperIndex).inputs → Option S)
    (relationMeaning : RelationMeaning imported relation model.Value registry)
    (booleanOutput : relation.declaration.outputs = [.boolean])
    (encoding : S → W → Values model.Value relation.declaration.inputs)
    (encodingDomain : S → W → Prop) where
  realizes : relationMeaning.RealizesClaim meaning booleanOutput encoding encodingDomain
  defined : ∀ arguments, domain arguments → ∃ statement, readback arguments = some statement
  adequate : ∀ arguments results, domain arguments →
    invoke (closedMeaningsOn model imported.program.payload.definitions)
      (imported.program.payload.definitions.get binding.helperIndex).helper arguments = .done results →
    results.get binding.output = true →
    ∃ statement, readback arguments = some statement ∧ meaning.token.Yes statement

end Zkc.Source.Structured
