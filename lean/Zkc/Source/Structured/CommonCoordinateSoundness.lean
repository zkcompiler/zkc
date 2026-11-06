module

public import Zkc.Source.Structured.CommonCoordinatePrefix
public import Zkc.Source.Structured.CommonCoordinateInputs
public import Zkc.Source.Structured.CommonCoordinateAuthority

@[expose] public section

/-! Agreement at a certified, reached source operation. The term and its finite demands
are read from the actual sequenceAt operand in the indexed retained-body certificate.
The premises concern input/counter observations and exact source prefixes, not the target
coordinate equality, delivery honesty, availability, or family data/handle consistency. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm

variable {snapshot : Snapshot} {definitions : List CheckedProtocol} {pair : Pair}
  {scope : Scope} {inputs outputs : List Ty} {roles : Nat → Nat} {cursor : Cursor}
  {origins : Origins scope} {kind : OracleKind} {maximum : Nat} {selected : List Nat}
  {location : OracleLocation} {args : Operands inputs [.oracleSequence kind maximum, .index]}
  {next : Region protocolDialect (.oracle kind :: inputs) outputs} {env : Symbols scope inputs}

/-- Finite certificate authority at the actual source operand; no term is proposed by
this theorem's caller. A certificate for a different body cannot inhabit this type. -/
theorem Plan.coordinate_known
    (plan : Plan snapshot definitions pair roles cursor origins
      (.letOp (.oracle (.sequenceAt kind maximum selected) location) args .nil next) env)
    (active : pair.selected roles selected = true) :
    ∃ term, env.get (args.get (.there .here)) = some term := by
  cases plan with
  | step leaf noRegions checked tail =>
    change (!(pair.selected roles selected) ||
      ((args.eval env.get).get (.there .here)).isSome) = true at checked
    rw [active, Operands.get_eval] at checked
    cases known : env.get (args.get (.there .here)) with
    | none => simp [known] at checked
    | some term => exact ⟨term, rfl⟩

/-- The common-input requirement is generated from the source-bound coordinate symbol.
Unknown operands have no demands but cannot pass a jointly selected certificate. -/
def coordinateDemands (env : Symbols scope inputs)
    (args : Operands inputs [.oracleSequence kind maximum, .index]) : List Nat :=
  ((env.get (args.get (.there .here))).map demanded).getD []

variable {model : DomainModel}

/-- One generic source-bound soundness theorem, independent of protocol names. Both roles
reach the same indexed body/application/repeat prefix; their preceding external replies
may differ arbitrarily. Common observations compare actual root input values and reached
counter binders. Counts need not agree, and absent coordinates remain absent. -/
theorem Plan.reached_agreement (context : ProtocolContext)
    (plan : Plan snapshot definitions pair context.roles cursor origins
      (.letOp (.oracle (.sequenceAt kind maximum selected) location) args .nil next) env)
    (active : pair.selected context.roles selected = true)
    (matchedPrefix : List Boundary)
    (leftStart rightStart : Frame snapshot definitions pair model)
    (leftObservations rightObservations : Observations model scope)
    (leftValues rightValues : Values (Component (ProtocolValue model.toCarriers)) inputs)
    (leftTable rightTable : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (leftOrdinary rightOrdinary : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (leftHelpers rightHelpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model))
    (leftPath : Prefix pair.left leftOrdinary leftHelpers leftStart
      (frame context plan leftObservations leftValues leftTable matchedPrefix))
    (rightPath : Prefix pair.right rightOrdinary rightHelpers rightStart
      (frame context plan rightObservations rightValues rightTable matchedPrefix))
    (leftInitial : leftStart.Matched) (rightInitial : rightStart.Matched)
    (common : AgreeOn model (coordinateDemands env args) leftObservations rightObservations) :
    ((args.eval leftValues.get).get (.there .here)).bind ProtocolValue.toConcrete =
      ((args.eval rightValues.get).get (.there .here)).bind ProtocolValue.toConcrete := by
  obtain ⟨term, known⟩ := plan.coordinate_known active
  have left : Matches env leftObservations leftValues :=
    leftPath.readback pair.left leftOrdinary leftHelpers (Or.inl rfl) leftInitial
  have right : Matches env rightObservations rightValues :=
    rightPath.readback pair.right rightOrdinary rightHelpers (Or.inr rfl) rightInitial
  rw [Operands.get_eval, Operands.get_eval,
    left _ term known, right _ term known]
  apply observe_agreement
  intro slot position member
  apply common position
  simpa only [coordinateDemands, known, Option.map_some, Option.getD_some] using member

/-- Start from actual root input components, not an assumed invariant at a later point. -/
def rootFrame (definition : CheckedProtocol)
    (plan : RootPlan snapshot definitions definition pair) (self : Nat)
    (values : Values (Component (ProtocolValue model.toCarriers)) definition.inputs)
    (protocols : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model)) :
    Frame snapshot definitions pair model :=
  frame {} plan (inputObservations values)
    (maskValues self (({} : ProtocolContext).mapScopes definition.inputScopes) values) protocols

/-- The root frame uses the exact existing Oracle function process, including output
masks and every stop. Action normalization supplies this structural equality. -/
theorem rootFrame_process (definition : CheckedProtocol)
    (plan : RootPlan snapshot definitions definition pair) (self : Nat)
    (values : Values (Component (ProtocolValue model.toCarriers)) definition.inputs)
    (protocols : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model)) :
    (OracleProtocol.algebra model self ordinary helpers).denote definition protocols {} self values =
      ((rootFrame definition plan self values protocols).body.denote
        ((OracleProtocol.algebra model self ordinary helpers).meaning protocols {} self)
        (rootFrame definition plan self values protocols).values.get).bind fun result ↦
          .done (maskValues self (({} : ProtocolContext).mapScopes definition.outputScopes) result) := by
  dsimp only [ProtocolAlgebra.denote, rootFrame, frame]
  erw [normalizeActions_process]
  rfl

/-- Root specialization discharges the initial invariant by reading actual inputs.
No equality about a later source coordinate is accepted as an initial premise. -/
theorem RootPlan.reached_agreement (definition : CheckedProtocol)
    (root : RootPlan snapshot definitions definition pair) (context : ProtocolContext)
    (plan : Plan snapshot definitions pair context.roles cursor origins
      (.letOp (.oracle (.sequenceAt kind maximum selected) location) args .nil next) env)
    (active : pair.selected context.roles selected = true)
    (matchedPrefix : List Boundary)
    (leftInputs rightInputs : Values (Component (ProtocolValue model.toCarriers)) definition.inputs)
    (leftRootTable rightRootTable leftTable rightTable :
      ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (leftObservations rightObservations : Observations model scope)
    (leftValues rightValues : Values (Component (ProtocolValue model.toCarriers)) inputs)
    (leftOrdinary rightOrdinary : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (leftHelpers rightHelpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model))
    (leftPath : Prefix pair.left leftOrdinary leftHelpers
      (rootFrame definition root pair.left leftInputs leftRootTable)
      (frame context plan leftObservations leftValues leftTable matchedPrefix))
    (rightPath : Prefix pair.right rightOrdinary rightHelpers
      (rootFrame definition root pair.right rightInputs rightRootTable)
      (frame context plan rightObservations rightValues rightTable matchedPrefix))
    (common : AgreeOn model (coordinateDemands env args) leftObservations rightObservations) :
    ((args.eval leftValues.get).get (.there .here)).bind ProtocolValue.toConcrete =
      ((args.eval rightValues.get).get (.there .here)).bind ProtocolValue.toConcrete := by
  apply plan.reached_agreement context active matchedPrefix _ _ _ _ _ _ _ _
    leftOrdinary rightOrdinary leftHelpers rightHelpers leftPath rightPath
  · intro ty position term known
    exact masked_input_readback pair pair.left (Or.inl rfl) {} definition.inputScopes leftInputs
      position term known
  · intro ty position term known
    exact masked_input_readback pair pair.right (Or.inr rfl) {} definition.inputScopes rightInputs
      position term known
  · exact common

end Zkc.Source.Structured.CommonCoordinate
