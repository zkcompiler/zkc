module

public import Zkc.Core.Specialize
public import Zkc.Core.Declaration

public section

/-! The Fiat–Shamir step over a whole program.

The step threads one transcript state per transcript role (`Core/Thread.lean`,
`Core/Specialize.lean`) and supplies the rule for the operations it rewrites:

- the entry: each transcript role makes its state and absorbs the statement, the inputs
  of the entry that prover and verifier share, each role from its own copy; the entry
  keeps its header;
- an exchange from the prover to the verifier: the exchange, then each of the two
  absorbs the value;
- a draw by one transcript role with the other as its only receiver: each of the two
  derives the coin; nothing is drawn and nothing is exchanged.

A suite is rows of the package behind one interface. For a site it gives what one role
does to absorb or derive, and the step does not know which kind of suite answered:

- a catalogue suite has a row that absorbs per message type and a row that derives per
  law; every absorbed or derived value carries a label, a literal of the suite's label
  type. The start row takes the proof identity, also a literal. The step adds the start,
  the statement and the labels.
- a source suite has one function per site and a start function of the statement. The
  step calls them and adds nothing.

A label is the statement's position, or the definition, the site and the transcript roles
of the image, always. It names neither the path of applications nor an iteration.

An exchange or a draw between exactly one transcript role and another online role is
refused: the other role's message would reach a transcript role without being absorbed.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The label of an absorbed or derived value. -/
inductive Label where
  | statement (position : Nat)
  | site (definition site : Nat) (roles : TranscriptRoles)
  deriving Repr, DecidableEq

/-- The label of a site of a definition's image: the definition's identity, the site and
the image's transcript roles. -/
def Place.label (place : Place) (site : Nat) : Label :=
  .site place.definition site place.roles

/-- The numbers a label is written as. -/
def Label.data : Label → List Nat
  | .statement position => [0, position]
  | .site definition number roles => [1, definition, number, roles.prover, roles.verifier]

/-- What one role does to absorb a value of a type: the label as a literal of the
suite's label type and the catalogue's absorbing row, or a function of the package. -/
inductive Absorber (operations : List OperationSignature) (functions : List FunctionHeader)
    (state type : Ty) where
  | row (label : Nat) (name : List Nat)
      (absorb : Var operations ⟨[state, .nominal label, type], [state], .pure⟩)
      (applies : OperationSignature.applies ⟨[state, .nominal label, type], [state], .pure⟩ = true)
  | handler (callee : Var functions ⟨[state, type], [state], false⟩)

/-- What one role does to derive a coin of a type. -/
inductive Deriver (operations : List OperationSignature) (functions : List FunctionHeader)
    (state output : Ty) where
  | row (label : Nat) (name : List Nat)
      (derive : Var operations ⟨[state, .nominal label], [output, state], .pure⟩)
      (applies : OperationSignature.applies ⟨[state, .nominal label], [output, state], .pure⟩ = true)
  | handler (callee : Var functions ⟨[state], [output, state], false⟩)

/-- How a role's state starts: the catalogue's start row applied to the proof identity,
after which the step absorbs the statement; or a function of the statement. -/
inductive Starter (operations : List OperationSignature) (functions : List FunctionHeader)
    (state : Ty) (statement : List Ty) where
  | separator (label : Nat) (identity : List Nat)
      (row : Var operations ⟨[.nominal label], [state], .pure⟩)
      (applies : OperationSignature.applies ⟨[.nominal label], [state], .pure⟩ = true)
  | handler (callee : Var functions ⟨statement, [state], false⟩)

/-- A suite: the type of the transcript state and what a role does at the start, at an
absorbed value and at a derived coin. -/
structure Suite (operations : List OperationSignature) (functions : List FunctionHeader) where
  state : Ty
  start : (statement : List Ty) → Option (Starter operations functions state statement)
  absorb : Label → (type : Ty) → Option (Absorber operations functions state type)
  derive : Label → (law : Nat) → (output : Ty) →
    Option (Deriver operations functions state output)

section Emit

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

local notation "𝒟" => ProtocolDialect operations functions protocols deployed

/-- One role absorbs a value into its state. -/
@[expose] def Absorber.emit {state type : Ty} (absorber : Absorber operations functions state type)
    (role : Nat) {Δ : List Located} (current : Var Δ ⟨state, role⟩) (value : Var Δ ⟨type, role⟩) :
    Emitted 𝒟 Δ [⟨state, role⟩] :=
  match absorber with
  | .row label name absorb applies =>
      let named : Emitted 𝒟 Δ [⟨.nominal label, role⟩] :=
        Emitted.operation (dialect := 𝒟) (.at role (.literal (.nominal label name)) .nil) .nil .nil
      let absorbed : Emitted 𝒟 named.context [⟨state, role⟩] :=
        Emitted.operation (dialect := 𝒟) (.at role (.op absorb applies) .nil)
          (.cons (current.extend named.grows)
            (.cons (named.values.get .here) (.cons (value.extend named.grows) .nil))) .nil
      named.andThen absorbed absorbed.values
  | .handler callee =>
      Emitted.operation (dialect := 𝒟) (.at role (.call callee (Bool.and_false _)) .nil)
        (.cons current (.cons value .nil)) .nil

/-- One role derives a coin and its new state. -/
@[expose] def Deriver.emit {state output : Ty} (deriver : Deriver operations functions state output)
    (role : Nat) {Δ : List Located} (current : Var Δ ⟨state, role⟩) :
    Emitted 𝒟 Δ [⟨output, role⟩, ⟨state, role⟩] :=
  match deriver with
  | .row label name derive applies =>
      let named : Emitted 𝒟 Δ [⟨.nominal label, role⟩] :=
        Emitted.operation (dialect := 𝒟) (.at role (.literal (.nominal label name)) .nil) .nil .nil
      let derived : Emitted 𝒟 named.context [⟨output, role⟩, ⟨state, role⟩] :=
        Emitted.operation (dialect := 𝒟) (.at role (.op derive applies) .nil)
          (.cons (current.extend named.grows) (.cons (named.values.get .here) .nil)) .nil
      named.andThen derived derived.values
  | .handler callee =>
      Emitted.operation (dialect := 𝒟) (.at role (.call callee (Bool.and_false _)) .nil)
        (.cons current .nil) .nil

end Emit

/-! ## The statement -/

/-- The copy of an agreed value that a role holds. -/
@[expose] def Agreement.copyOf {ports : List Located} (agreement : Agreement ports) (role : Nat) :
    Option (Var ports ⟨agreement.type, role⟩) :=
  agreement.copies.findSome? fun copy =>
    if same : copy.holder = role then some (copy.port.retype (by rw [same])) else none

/-- The statement of an entry: the agreed inputs of which the prover and the verifier
each hold a copy, in the order of the agreements. -/
@[expose] def statementOf (roles : TranscriptRoles) (header : ProtocolHeader) : List (Agreement header.inputs) :=
  header.agreements.inputs.filter fun agreement =>
    (agreement.copyOf roles.prover).isSome && (agreement.copyOf roles.verifier).isSome

/-- The first input from a position on that the role holds and that is not among the
given ports. -/
def firstUncovered (role : Nat) (covered : List Nat) : Nat → List Located → Option Nat
  | _, [] => none
  | position, port :: rest =>
      if Nat.beq port.holder role && !(occursIn covered position) then some position
      else firstUncovered role covered (position + 1) rest

section Statement

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

local notation "𝒟" => ProtocolDialect operations functions protocols deployed

/-- A role's copies of the statement, as the operands of a start function. -/
@[expose] def statementOperands (role : Nat) {ports Δ : List Located} (values : Operands Δ ports) :
    (statement : List (Agreement ports)) →
      Option (Operands Δ (Located.atRole role (statement.map (·.type))))
  | [] => some .nil
  | agreement :: rest =>
      match agreement.copyOf role, statementOperands role values rest with
      | some port, some tail => some (.cons (values.get port) tail)
      | _, _ => none

/-- A role absorbs its copies of the statement, each with the label of its position. -/
@[expose] def absorbStatement (suite : Suite operations functions) (role : Nat) {ports Δ : List Located}
    (values : Operands Δ ports) :
    Nat → List (Agreement ports) → Emitted 𝒟 Δ [⟨suite.state, role⟩] →
      Except StepRefusal (Emitted 𝒟 Δ [⟨suite.state, role⟩])
  | _, [], sofar => .ok sofar
  | position, agreement :: rest, sofar =>
      match agreement.copyOf role, suite.absorb (.statement position) agreement.type with
      | some port, some absorber =>
          let absorbed := absorber.emit (protocols := protocols) (deployed := deployed) role
            (sofar.values.get .here) ((values.get port).extend sofar.grows)
          absorbStatement suite role values (position + 1) rest
            (sofar.andThen absorbed absorbed.values)
      | _, _ => .error (.statement position)

/-- A role's state at the start of the entry. -/
@[expose] def startState (suite : Suite operations functions) (role : Nat) {ports Δ : List Located}
    (statement : List (Agreement ports)) (values : Operands Δ ports) :
    Except StepRefusal (Emitted 𝒟 Δ [⟨suite.state, role⟩]) :=
  match suite.start (statement.map (·.type)) with
  | none => .error .row
  | some (.separator label identity row applies) =>
      let named : Emitted 𝒟 Δ [⟨.nominal label, role⟩] :=
        Emitted.operation (dialect := 𝒟) (.at role (.literal (.nominal label identity)) .nil)
          .nil .nil
      let started : Emitted 𝒟 named.context [⟨suite.state, role⟩] :=
        Emitted.operation (dialect := 𝒟) (.at role (.op row applies) .nil)
          (.cons (named.values.get .here) .nil) .nil
      absorbStatement suite role values 0 statement (named.andThen started started.values)
  | some (.handler callee) =>
      match statementOperands role values statement with
      | some arguments =>
          .ok (Emitted.operation (dialect := 𝒟) (.at role (.call callee (Bool.and_false _)) .nil)
            arguments .nil)
      | none => .error (.statement 0)

end Statement

/-! ## The rule -/

/-- The Fiat–Shamir rule of a suite. -/
@[expose] def fiatShamirRule {operations : List OperationSignature} {functions : List FunctionHeader}
    (suite : Suite operations functions) :
    Rule ⟨suite.state, suite.state⟩ operations functions where
  exchange := fun {protocols deployed} place site type {_} value first second =>
    match suite.absorb (place.label site) type with
    | none => .error (.message place.definition site)
    | some absorber =>
        -- The exchange binds the verifier's copy; then each role absorbs its copy.
        let sent : Emitted (ProtocolDialect operations functions protocols deployed) _
            [⟨type, place.roles.verifier⟩] :=
          Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
            (.exchange place.roles.prover place.roles.verifier site type) (.cons value .nil) .nil
        let atProver := absorber.emit (protocols := protocols) (deployed := deployed)
          place.roles.prover (first.extend sent.grows) (value.extend sent.grows)
        let received := (sent.values.get .here).extend atProver.grows
        let atVerifier := absorber.emit (protocols := protocols) (deployed := deployed)
          place.roles.verifier ((second.extend sent.grows).extend atProver.grows) received
        .ok ((sent.andThen atProver atProver.values).andThen atVerifier
          (.cons (received.extend atVerifier.grows)
            (.cons ((atProver.values.get .here).extend atVerifier.grows)
              (.cons (atVerifier.values.get .here) .nil))))
  derives := true
  draw := fun {protocols deployed} place site {inputs output} law {_} first second =>
    if inputs.isEmpty then
      match suite.derive (place.label site) law.index output with
      | none => .error (.undecoded place.definition site)
      | some deriver =>
          let atVerifier := deriver.emit (protocols := protocols) (deployed := deployed)
            place.roles.verifier second
          let atProver := deriver.emit (protocols := protocols) (deployed := deployed)
            place.roles.prover (first.extend atVerifier.grows)
          .ok (atVerifier.andThen atProver
            (.cons (atProver.values.get .here)
              (.cons ((atVerifier.values.get .here).extend atProver.grows)
                (.cons (atProver.values.get (.there .here))
                  (.cons ((atVerifier.values.get (.there .here)).extend atProver.grows) .nil)))))
    else .error (.lawInputs place.definition site)
  entryRefusal := fun roles header =>
    -- An input that the verifier holds alone is not part of the statement.
    let covered := (statementOf roles header).filterMap fun agreement =>
      (agreement.copyOf roles.verifier).map (·.index)
    (firstUncovered roles.verifier covered 0 header.inputs).map .verifierInput
  entryPorts := fun _ header => ⟨header.inputs, header.outputs, header.agreements⟩
  entry := fun {protocols deployed} place header body =>
    let statement := statementOf place.roles header
    let ports : Operands (bindAll [] header.inputs) header.inputs := Operands.newest header.inputs
    match startState (protocols := protocols) (deployed := deployed) suite place.roles.prover
        statement ports with
    | .error refusal => .error refusal
    | .ok atProver =>
        match startState (protocols := protocols) (deployed := deployed) suite
            place.roles.verifier statement (ports.extend atProver.grows) with
        | .error refusal => .error refusal
        | .ok atVerifier =>
            match body
                ((Renaming.identity header.inputs).extend (atProver.grows.trans atVerifier.grows))
                ((atProver.values.get .here).extend atVerifier.grows)
                (atVerifier.values.get .here) with
            | .ok threaded =>
                -- The entry returns its own outputs: the two final states are dropped.
                .ok (atProver.wrap (atVerifier.wrap (.bind threaded
                  (.ret (Operands.newest header.outputs
                    (Γ := ⟨suite.state, place.roles.verifier⟩ ::
                      ⟨suite.state, place.roles.prover⟩ :: atVerifier.context))))))
            | .error refusal => .error refusal
  idleEntry := false

/-! ## A suite from the rows of a package -/

/-- The row at a position of the table, when it has the signature. -/
@[expose] def rowWith {operations : List OperationSignature} (rows : Scope operations)
    (signature : OperationSignature) (row : Nat) : Option (Var operations signature) :=
  rows.atType? signature row

/-- The first of the rows that has the signature. -/
@[expose] def firstRowWith {operations : List OperationSignature} (rows : Scope operations)
    (signature : OperationSignature) : List Nat → Option (Var operations signature)
  | [] => none
  | row :: later =>
      match rowWith rows signature row with
      | some reference => some reference
      | none => firstRowWith rows signature later

/-- A row that a local operation may apply, with the proof that it may: a pure row whose
outputs are populated, or a restricted row. -/
@[expose] def appliedRow {operations : List OperationSignature} {signature : OperationSignature}
    {α : Type} (make : Var operations signature → signature.applies = true → α) :
    Option (Var operations signature) → Option α
  | some row => if applies : signature.applies = true then some (make row applies) else none
  | none => none

/-- The first of the functions that has the header. -/
def firstCalleeWith {functions : List FunctionHeader} (callees : Scope functions)
    (header : FunctionHeader) : List Nat → Option (Var functions header)
  | [] => none
  | number :: later =>
      match callees.find? header number with
      | some reference => some reference
      | none => firstCalleeWith callees header later

/-- The site rows of every protocol, for lookup by the protocol's number. -/
def siteTable (sites : List (List Raw.SiteRow)) : Sequence (List Raw.SiteRow) :=
  sites.foldl (fun table rows => table.push rows) .empty

/-- The function of a site among the site rows of its definition: the one for the image's
transcript roles, or the one for every image. -/
def siteRowOf (site : Nat) (roles : TranscriptRoles) : List Raw.SiteRow → Option Nat
  | [] => none
  | row :: rest =>
      let same := match row.roles with
        | none => true
        | some (prover, verifier) => Nat.beq prover roles.prover && Nat.beq verifier roles.verifier
      if Nat.beq row.site site && same then some row.row else siteRowOf site roles rest

/-- The function that a source suite's declaration gives for a label. -/
def labelRow (table : Sequence (List Raw.SiteRow)) (count : Nat) : Label → Option Nat
  | .statement _ => none
  | .site definition site roles =>
      match table.get? (count - 1 - definition) with
      | some rows => siteRowOf site roles rows
      | none => none

/-- The second component of the first pair with the given first component. -/
def pairedWith (key : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | pair :: rest => if Nat.beq pair.1 key then some pair.2 else pairedWith key rest

/-- The suite that a declaration describes, over the rows and functions of a package. -/
@[expose] def Suite.ofRaw {operations : List OperationSignature} {functions : List FunctionHeader}
    (rows : Scope operations) (callees : Scope functions) : Raw.Suite → Suite operations functions
  | .catalogue state label start absorbing deriving_ identity =>
      { state := state
        start := fun _ =>
          appliedRow (.separator label identity)
            (rowWith rows ⟨[.nominal label], [state], .pure⟩ start)
        absorb := fun name type =>
          appliedRow (.row label name.data)
            (firstRowWith rows ⟨[state, .nominal label, type], [state], .pure⟩ absorbing)
        derive := fun name law output =>
          appliedRow (.row label name.data)
            ((pairedWith law deriving_).bind
              (rowWith rows ⟨[state, .nominal label], [output, state], .pure⟩)) }
  | .source state start absorbing deriving_ sites =>
      let table := siteTable sites
      let count := sites.length
      { state := state
        start := fun statement => (callees.find? ⟨statement, [state], false⟩ start).map .handler
        absorb := fun name type =>
          match (labelRow table count name).bind
              (callees.find? ⟨[state, type], [state], false⟩) with
          | some callee => some (.handler callee)
          | none => (firstCalleeWith callees ⟨[state, type], [state], false⟩ absorbing).map .handler
        derive := fun name law output =>
          match (labelRow table count name).bind
              (callees.find? ⟨[state], [output, state], false⟩) with
          | some callee => some (.handler callee)
          | none =>
              ((pairedWith law deriving_).bind
                (callees.find? ⟨[state], [output, state], false⟩)).map .handler }

/-! ## Online roles beside the transcript roles -/

/-- How a definition is reached, for the check on online roles: the transcript roles, of
which either may be absent, and the roles that run as online roles of the entry. -/
structure Reach where
  prover : Option Nat
  verifier : Option Nat
  online : List Nat
  deriving DecidableEq

/-- A role is one of the two transcript roles. -/
def Reach.transcript (reach : Reach) (role : Nat) : Bool :=
  isRole reach.prover role || isRole reach.verifier role

/-- A role is online and not a transcript role. -/
def Reach.third (reach : Reach) (role : Nat) : Bool :=
  occursIn reach.online role && !reach.transcript role

/-- The callee's reach under a role map. -/
def Reach.under (reach : Reach) (roleMap : RoleMap) : Reach :=
  ⟨preimageOf roleMap reach.prover, preimageOf roleMap reach.verifier,
    (List.range roleMap.length).filter fun formal => occursIn reach.online (roleMap.apply formal)⟩

/-- One more reach of the protocol at a position, the most recent first. -/
def addReach (reach : Reach) : Nat → List (List Reach) → List (List Reach)
  | 0, [] => [[reach]]
  | 0, own :: older =>
      (if own.any fun other => decide (other = reach) then own else reach :: own) :: older
  | index + 1, [] => [] :: addReach reach index []
  | index + 1, own :: older => own :: addReach reach index older

section ThirdRole

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The site of an exchange or draw between exactly one transcript role and another
online role. -/
def thirdRoleAt (reach : Reach) : ProtocolOp operations functions protocols deployed → Option Nat
  | .exchange sender receiver site _ =>
      if (reach.transcript sender && reach.third receiver) ||
          (reach.third sender && reach.transcript receiver) then some site else none
  | .draw owner receivers site _ _ =>
      if (reach.transcript owner && receivers.any reach.third) ||
          (reach.third owner && receivers.any reach.transcript) then some site else none
  | .at .. | .sample .. | .repeat .. | .choose .. | .apply .. => none

mutual
  /-- The first such site of a region, nested regions included. -/
  def thirdRoleIn (reach : Reach) {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out → Option Nat
    | .ret _ => none
    | .stop _ => none
    | .bind body rest => (thirdRoleIn reach body).or (thirdRoleIn reach rest)
    | .letOp op _ bodies rest =>
        ((thirdRoleAt reach op).or (thirdRoleInRegions reach bodies)).or (thirdRoleIn reach rest)

  def thirdRoleInRegions (reach : Reach) {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures → Option Nat
    | .nil => none
    | .cons body tail => (thirdRoleIn reach body).or (thirdRoleInRegions reach tail)
end

end ThirdRole

/-- The first exchange or draw of a program, reached from the entry, between exactly one
transcript role and another online role. `reaches` lists, for each protocol from the
newest, the ways it is reached from the protocols after it. -/
@[expose] def thirdRoleRefusal {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      List (List Reach) → Option StepRefusal
  | _, .nil, _ => none
  | _, .snoc (protocols := earlier) protocols definition _, reaches =>
      let own := reaches.headD []
      match own.findSome? fun reach => thirdRoleIn reach definition.body with
      | some site => some (.thirdRole earlier.length site)
      | none =>
          thirdRoleRefusal protocols
            (own.foldl (fun older reach =>
              (applications definition.body []).foldl (fun older application =>
                addReach (reach.under application.2) application.1 older) older) reaches.tail)

/-- The Fiat–Shamir step on a typed package: the program of the declared entry in which
the transcript roles derive their coins. The tables and the functions are those of the
package. -/
@[expose] def fiatShamir (typed : Typed) (declaration : Raw.Declaration) :
    Except StepRefusal (Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions) :=
  match declaration.suite with
  | none => .error .row
  | some suite =>
      let suite := Suite.ofRaw (tableScope (typed.table.map (·.signature)))
        (tableScope typed.functions) suite
      let reaches := List.replicate (typed.protocols.length - 1 - declaration.entry) [] ++
        [[(⟨some declaration.prover, some declaration.verifier, declaration.online⟩ : Reach)]]
      if let some refusal := thirdRoleRefusal typed.program.protocols reaches then .error refusal
      else stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) Identities.written
        declaration.entry
        ⟨declaration.prover, declaration.verifier⟩ typed.program.protocols

end Zkc.Core
