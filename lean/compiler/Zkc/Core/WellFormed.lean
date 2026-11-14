module

public import Zkc.Core.Dialects

public section

/-! Residual well-formedness and programs.

Typing fixes operand types and holders, closed regions, references to earlier
definitions and to operation rows, the agreement of an operation with its row's
signature and kind, the authored reason of a `guard`, the outputs of a `choose` held
by its participants, the one type and the first copy of an agreement, and the
prohibition on a deployed definition using a specification-only one. The remaining
conditions are decidable facts about the numbers of a definition or of the package's
tables. Each has a name, a constructor of `Violation`:

- a protocol has a role; holders, owners, participants and role-map entries are below
  the role count;
- a `choose` on a condition or an arm number has an arm;
- a `repeat` or `choose` has a participant and lists each participant once; every
  role that an operation inside it names is a participant, and every value that
  enters or leaves it is held by one;
- the sender and the receiver of an `exchange` differ; the receivers of a `draw`
  are listed once each and exclude its owner;
- a role map has one entry per formal role of the callee, and its entries are
  distinct;
- a site is below the site limit and no two operations of a definition share a site;
- a protocol region contains no `stop`, and a `stop` in a local region names an
  authored reason;
- the copies of an agreement have different holders, and the agreements of a
  signature name each port at most once;
- every type of a signature, of a result and of a table row is a type of the package:
  its nominal rows are rows of the type table, and the records and variants it names are
  declared with the use and the shape it carries; the fields and alternatives of the
  declarations are types of the package;
- a catalogue name is not empty and uses letters, digits and `. _ - /`; no two
  operation rows have one catalogue identity; a sampling row has one output; every
  output type of a pure row and of a sampling row is populated; the domain row that a
  restricted row names is an earlier pure row of the table with the same inputs and the
  one output `bool`.

`FunctionDefinition.violation` and `ProtocolDefinition.violation` find the first
violated condition in one pass over the definition, which also collects its sites. A
program can only be extended by a definition without a violation, so the kernel
decides the conditions once for every definition it accepts.

Sites are unique within a definition. In a program as written they are also numbered
without gaps; that is the separate condition `Program.dense`, which a step that removes
a site does not preserve.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The residual conditions, each named by its violation. -/
inductive Violation where
  /-- A protocol has no role. -/
  | noRole
  /-- A holder, an owner, a participant or a role-map entry is not below the role count. -/
  | roleOutOfRange
  /-- A `repeat` or `choose` has no participant. -/
  | noParticipant
  /-- A `choose` on an arm number has no arm. -/
  | noArm
  /-- A `repeat` or `choose` lists a participant twice. -/
  | repeatedParticipant
  /-- An operation inside a `repeat` or `choose` names a role that is not a participant. -/
  | roleOutsideParticipants
  /-- A value that enters or leaves a `repeat` or `choose` is held by a role that is
  not a participant. -/
  | valueOutsideParticipants
  /-- The sender of an `exchange` is its receiver. -/
  | exchangeToSelf
  /-- A `draw` lists a receiver twice. -/
  | repeatedReceiver
  /-- The owner of a `draw` is one of its receivers. -/
  | ownerReceives
  /-- A role map does not have one entry per formal role of the callee. -/
  | roleMapLength
  /-- A role map sends two formal roles to one role. -/
  | roleMapNotInjective
  /-- A site is not below the site limit. -/
  | siteLimit
  /-- Two operations of a definition share a site. -/
  | repeatedSite
  /-- The sites of a definition as written are not numbered without gaps. -/
  | siteGap
  /-- A protocol region contains a `stop`. -/
  | protocolStop
  /-- A `stop` names a reserved reason, `incomplete` or `undefined`. -/
  | reservedReason
  /-- Two copies of an agreement have one holder. -/
  | agreementHolders
  /-- The agreements of a signature name a port twice. -/
  | agreementPorts
  /-- A type names a nominal row beyond the type table, or a record or a variant that the
  package does not declare with the use and the shape that the type carries. -/
  | nominalRow
  /-- A catalogue name is empty or uses a character other than letters, digits and
  `. _ - /`. -/
  | catalogueName
  /-- Two operation rows have one catalogue identity. -/
  | repeatedOperation
  /-- A sampling row does not have exactly one output. -/
  | samplingOutputs
  /-- A pure row or a sampling row has an output type that is not populated: no total
  function returns it, and no coin has it. -/
  | unpopulatedOutput
  /-- A restricted row names a domain row that is not an earlier pure row of the table with
  the same inputs and the one output `bool`. -/
  | domainRow
  /-- A table of names does not have one entry per definition, role or site. -/
  | nameTable
  /-- A declaration of a record or a variant has a field or an alternative whose type is not
  a type of the package. -/
  | declaration
  deriving Repr, Inhabited, DecidableEq

/-- The name of the first condition of a list that fails; none when all hold. -/
@[expose] def firstViolation : List (Bool × Violation) → Option Violation
  | [] => none
  | (holds, violation) :: rest => cond holds (firstViolation rest) (some violation)

/-- The earlier of two findings. -/
@[expose] def earlierViolation : Option Violation → Option Violation → Option Violation
  | some violation, _ => some violation
  | none, later => later

/-- Every condition of a list without a violation holds. -/
theorem firstViolation_holds :
    ∀ (conditions : List (Bool × Violation)), firstViolation conditions = none →
      ∀ entry ∈ conditions, entry.1 = true
  | [], _, _, member => nomatch member
  | (holds, violation) :: rest, clean, entry, member => by
      cases holds with
      | false => cases clean
      | true =>
          rcases List.mem_cons.mp member with rfl | later
          · rfl
          · exact firstViolation_holds rest clean entry later

theorem earlierViolation_both {first second : Option Violation}
    (clean : earlierViolation first second = none) : first = none ∧ second = none := by
  cases first with
  | some violation => cases clean
  | none => exact ⟨rfl, clean⟩

/-! ## Types of the type table -/

mutual
  /-- A type of a package: every nominal row it names is a row of the type table, and
  every record and variant it names is declared with the use and the shape that the type
  carries. -/
  @[expose] def Ty.named (types : TypeTable) : Ty → Bool
    | .bool | .nat | .fin _ => true
    | .nominal row => Nat.blt row types.nominals
    | .seq element _ => Ty.named types element
    | .tuple components => Ty.allNamed types components
    | .record declaration use fields =>
        decide (types.records[declaration]? = some ⟨use, fields⟩) && Ty.allNamed types fields
    | .variant declaration alternatives =>
        decide (types.variants[declaration]? = some ⟨alternatives⟩) &&
          Ty.allNamed types alternatives

  @[expose] def Ty.allNamed (types : TypeTable) : List Ty → Bool
    | [] => true
    | type :: rest => Ty.named types type && Ty.allNamed types rest
end

/-- Every located type is a type of the package. -/
@[expose] def Located.allNamed (types : TypeTable) : List Located → Bool
  | [] => true
  | located :: rest => Ty.named types located.type && Located.allNamed types rest

/-- The declarations of a type table name types of the table. -/
def TypeTable.declared (types : TypeTable) : Bool :=
  types.records.all (fun record => Ty.allNamed types record.fields) &&
    types.variants.all fun variant => Ty.allNamed types variant.alternatives

/-! ## Local regions -/

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

mutual
  /-- A `stop` of a local region names an authored reason, and the types of every
  result are types of the package. -/
  @[expose] def localRegionViolation (typeTable : TypeTable) {Γ out : List Ty} :
      Region (LocalDialect operations functions deployed) Γ out → Option Violation
    | .ret _ => none
    | .stop reason => cond (authoredStop reason) none (some .reservedReason)
    | .letOp op _ bodies next =>
        cond (Ty.allNamed typeTable (LocalOp.results op))
          (earlierViolation (localRegionsViolation typeTable bodies)
            (localRegionViolation typeTable next))
          (some .nominalRow)
    | .bind (mid := mid) body next =>
        cond (Ty.allNamed typeTable mid)
          (earlierViolation (localRegionViolation typeTable body)
            (localRegionViolation typeTable next))
          (some .nominalRow)

  @[expose] def localRegionsViolation (typeTable : TypeTable) {signatures : List (List Ty × List Ty)} :
      Regions (LocalDialect operations functions deployed) signatures → Option Violation
    | .nil => none
    | .cons body tail =>
        earlierViolation (localRegionViolation typeTable body)
          (localRegionsViolation typeTable tail)
end

end Local

/-! ## Protocol regions -/

/-- A role may act where the participants of the enclosing `repeat` or `choose`, if
there is one, include it. -/
@[expose] def participates : Option (List Nat) → Nat → Bool
  | none, _ => true
  | some participants, role => occursIn participants role

/-- The roles that act at one place are below the role count and, inside a `repeat`
or `choose`, participants. -/
@[expose] def actingRoles (roles : Nat) (enclosing : Option (List Nat)) (acting : List Nat) :
    List (Bool × Violation) :=
  [(acting.all fun role => Nat.blt role roles, .roleOutOfRange),
   (acting.all (participates enclosing), .roleOutsideParticipants)]

/-- The sender and the receiver of an `exchange` differ. -/
def exchangeConditions (sender receiver : Nat) : List (Bool × Violation) :=
  [(!(Nat.beq sender receiver), .exchangeToSelf)]

/-- The receivers of a `draw` are listed once each and exclude its owner. Their order is the
order in which the results of the draw are bound, and a role map changes it: an injective map
keeps receivers distinct and does not keep them increasing. -/
@[expose] def drawConditions (owner : Nat) (receivers : List Nat) : List (Bool × Violation) :=
  [(distinctNumbers receivers, .repeatedReceiver),
   (!(occursIn receivers owner), .ownerReceives)]

/-- The participants of a `repeat` or `choose`: at least one, each once, holding
every value that enters or leaves. -/
@[expose] def participantConditions (participants : List Nat) (values : List Located) :
    List (Bool × Violation) :=
  [(!participants.isEmpty, .noParticipant),
   (distinctNumbers participants, .repeatedParticipant),
   (Located.heldBy participants values, .valueOutsideParticipants)]

/-- A choice on a condition or on an arm number has an arm. A choice on a variant has one
region per alternative, and none when the variant has no alternative. -/
@[expose] def ChoiceTag.inhabited : ChoiceTag → Bool
  | .condition => true
  | .arm count => !(Nat.beq count 0)
  | .alternative _ _ => true

/-- A role map has one entry per formal role of the callee, and distinct entries. -/
@[expose] def roleMapConditions (formal : Nat) (roleMap : RoleMap) : List (Bool × Violation) :=
  [(Nat.beq roleMap.length formal, .roleMapLength),
   (distinctNumbers roleMap, .roleMapNotInjective)]

/-- A protocol has a role, the holders of its ports are below its role count, and the
types of its ports are types of the package. -/
@[expose] def portConditions (typeTable : TypeTable) (roles : Nat) (ports : List Located) : List (Bool × Violation) :=
  [(!(Nat.beq roles 0), .noRole),
   (ports.all fun port => Nat.blt port.holder roles, .roleOutOfRange),
   (Located.allNamed typeTable ports, .nominalRow)]

/-- The copies of each agreement have different holders, and no port is named twice:
`holders` lists the holders of each agreement's copies, `ports` the positions of
the ports that the agreements name. -/
@[expose] def copyConditions (holders : List (List Nat)) (ports : List Nat) : List (Bool × Violation) :=
  [(holders.all distinctNumbers, .agreementHolders),
   (distinctNumbers ports, .agreementPorts)]

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- Every role that a protocol operation names: an owner, a sender, a receiver, the
receivers of a draw, the participants of a `repeat` or `choose`, the entries of a
role map. -/
@[expose] def ProtocolOp.roles : ProtocolOp operations functions protocols deployed → List Nat
  | .at role .. => [role]
  | .exchange sender receiver .. => [sender, receiver]
  | .draw owner receivers .. => owner :: receivers
  | .sample owner .. => [owner]
  | .repeat participants .. | .choose participants .. => participants
  | .apply _ roleMap .. => roleMap

/-- The site of a protocol operation, when it has one. -/
@[expose] def ProtocolOp.sites : ProtocolOp operations functions protocols deployed → List Nat
  | .exchange _ _ site _ | .draw _ _ site _ _ | .sample _ site _ _ | .apply _ _ site _ => [site]
  | .at .. | .repeat .. | .choose .. => []

/-- The first violated condition of one protocol operation of a protocol with `roles`
roles, inside the `repeat` or `choose` whose participants are `enclosing`. -/
@[expose] def ProtocolOp.violation (typeTable : TypeTable) (roles : Nat) (enclosing : Option (List Nat)) :
    (op : ProtocolOp operations functions protocols deployed) → Option Violation
  | op@(.at _ _ bodies) =>
      earlierViolation (firstViolation (actingRoles roles enclosing op.roles))
        (localRegionsViolation typeTable bodies)
  | op@(.exchange sender receiver _ _) =>
      firstViolation (actingRoles roles enclosing op.roles ++ exchangeConditions sender receiver)
  | op@(.draw owner receivers _ _ _) =>
      firstViolation (actingRoles roles enclosing op.roles ++ drawConditions owner receivers)
  | op@(.sample ..) => firstViolation (actingRoles roles enclosing op.roles)
  | op@(.repeat participants _ carried _ captures _) =>
      firstViolation (actingRoles roles enclosing op.roles ++
        participantConditions participants (carried ++ captures))
  | op@(.choose participants tag captures outputs _) =>
      firstViolation (actingRoles roles enclosing op.roles ++
        (participantConditions participants (captures ++ outputs) ++
          [(tag.inhabited, .noArm)]))
  | op@(.apply (header := header) _ roleMap _ _) =>
      firstViolation (actingRoles roles enclosing op.roles ++
        roleMapConditions header.roles roleMap)

/-- The participants that enclose an operation's regions: its own, for a `repeat` or
`choose`. -/
@[expose] def ProtocolOp.enclosing (enclosing : Option (List Nat)) :
    ProtocolOp operations functions protocols deployed → Option (List Nat)
  | .repeat participants .. | .choose participants .. => some participants
  | .at .. | .exchange .. | .draw .. | .sample .. | .apply .. => enclosing

mutual
  /-- One pass over a protocol region: the first violated condition of its
  operations, or the sites it uses, nested regions and every arm of a `choose`
  included, before the sites met so far. -/
  @[expose] def protocolRegionSites {Γ out : List Located} (typeTable : TypeTable) (roles : Nat)
      (enclosing : Option (List Nat)) :
      Region (ProtocolDialect operations functions protocols deployed) Γ out → List Nat →
        Except Violation (List Nat)
    | .ret _, sites => .ok sites
    | .stop _, _ => .error .protocolStop
    | .letOp op _ bodies next, sites =>
        match ProtocolOp.violation typeTable roles enclosing op with
        | some violation => .error violation
        | none =>
            cond (Located.allNamed typeTable (ProtocolOp.results op))
              (match protocolRegionsSites typeTable roles (ProtocolOp.enclosing enclosing op) bodies
                  (ProtocolOp.sites op ++ sites) with
                | .error violation => .error violation
                | .ok sites => protocolRegionSites typeTable roles enclosing next sites)
              (.error .nominalRow)
    | .bind (mid := mid) body next, sites =>
        cond (Located.allNamed typeTable mid)
          (match protocolRegionSites typeTable roles enclosing body sites with
            | .error violation => .error violation
            | .ok sites => protocolRegionSites typeTable roles enclosing next sites)
          (.error .nominalRow)

  @[expose] def protocolRegionsSites {signatures : List (List Located × List Located)}
      (typeTable : TypeTable) (roles : Nat) (enclosing : Option (List Nat)) :
      Regions (ProtocolDialect operations functions protocols deployed) signatures → List Nat →
        Except Violation (List Nat)
    | .nil, sites => .ok sites
    | .cons body tail, sites =>
        match protocolRegionSites typeTable roles enclosing body sites with
        | .error violation => .error violation
        | .ok sites => protocolRegionsSites typeTable roles enclosing tail sites
end

end Protocol

/-! ## Sites -/

/-- No site number reaches this limit. It bounds the numerals of the uniqueness test. -/
def siteLimit : Nat := 1048576

/-- The remaining sites are below the limit and unused. The used sites are the set
bits of `seen`. A site is compared with the limit before its bit is formed, so no
numeral has more bits than the limit. -/
@[expose] def unusedSites : Nat → List Nat → Option Violation
  | _, [] => none
  | seen, site :: rest =>
      cond (Nat.blt site siteLimit)
        (cond (seen.testBit site) (some .repeatedSite)
          (unusedSites (seen ||| (1 <<< site)) rest))
        (some .siteLimit)

/-- No two of the sites of a definition are equal. -/
@[expose] def sitesViolation (sites : List Nat) : Option Violation := unusedSites 0 sites

/-- Every site is below a count. -/
def sitesBelow (count : Nat) : List Nat → Bool
  | [] => true
  | site :: rest => Nat.blt site count && sitesBelow count rest

/-- The sites of a definition are `0 … k−1`: there are `k` of them and each is below
`k`. With uniqueness this numbers them without gaps. The count is computed once. -/
def sitesDense (sites : List Nat) : Bool :=
  match sites.length with
  | 0 => true
  | count + 1 => sitesBelow (count + 1) sites

/-! ## Agreements -/

/-- The conditions of the agreements over one list of ports. -/
@[expose] def agreementConditions {ports : List Located} (agreements : List (Agreement ports)) :
    List (Bool × Violation) :=
  copyConditions (agreements.map fun agreement => agreement.copies.map (·.holder))
    (agreements.flatMap fun agreement => agreement.copies.map (·.port.index))

/-! ## Definitions and programs -/

section Definitions

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- The first violated residual condition of a function; none when it is well formed. -/
@[expose] def FunctionDefinition.violation (typeTable : TypeTable) {header : FunctionHeader}
    (definition : FunctionDefinition operations functions header) : Option Violation :=
  cond (Ty.allNamed typeTable header.inputs && Ty.allNamed typeTable header.outputs)
    (localRegionViolation typeTable definition.body) (some .nominalRow)

/-- The sites of a protocol's body, or the first violated condition of its operations. -/
@[expose] def ProtocolDefinition.sites (typeTable : TypeTable) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) :
    Except Violation (List Nat) :=
  protocolRegionSites typeTable header.roles none definition.body []

/-- The first violated residual condition of a protocol; none when it is well formed.
The signature is decided first, then the body in one pass, then the sites that the
pass collected. -/
@[expose] def ProtocolDefinition.violation (typeTable : TypeTable) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) : Option Violation :=
  earlierViolation
    (firstViolation
      (portConditions typeTable header.roles (header.inputs ++ header.outputs) ++
        (agreementConditions header.agreements.inputs ++
          agreementConditions header.agreements.outputs)))
    (match definition.sites typeTable with
      | .error violation => some violation
      | .ok sites => sitesViolation sites)

/-- The sites of a protocol are numbered without gaps. -/
@[expose] def ProtocolDefinition.dense (typeTable : TypeTable) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) : Bool :=
  match definition.sites typeTable with
  | .error _ => true
  | .ok sites => sitesDense sites

end Definitions

/-- The functions of a program in order, each typed over the operation table and the
headers of the earlier ones, and each without a residual violation. The index lists
the headers, most recent first. -/
inductive Functions (typeTable : TypeTable) (operations : List OperationSignature) :
    List FunctionHeader → Type where
  | nil : Functions typeTable operations []
  | snoc {functions : List FunctionHeader} {header : FunctionHeader}
      (earlier : Functions typeTable operations functions)
      (definition : FunctionDefinition operations functions header)
      (wellFormed : definition.violation typeTable = none) :
      Functions typeTable operations (header :: functions)
  /-- A function known by its header only: its body is not written in the core language.
  Its meaning is the model's. -/
  | «opaque» {functions : List FunctionHeader} (earlier : Functions typeTable operations functions)
      (header : FunctionHeader)
      (named : (Ty.allNamed typeTable header.inputs && Ty.allNamed typeTable header.outputs) = true) :
      Functions typeTable operations (header :: functions)

/-- The protocols of a program in order, each typed over the operation table, the
headers of every function and the headers of the earlier protocols. -/
inductive Protocols (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) : List ProtocolHeader → Type where
  | nil : Protocols typeTable operations functions []
  | snoc {protocols : List ProtocolHeader} {header : ProtocolHeader}
      (earlier : Protocols typeTable operations functions protocols)
      (definition : ProtocolDefinition operations functions protocols header)
      (wellFormed : definition.violation typeTable = none) :
      Protocols typeTable operations functions (header :: protocols)

/-- The functions before the last one. -/
@[expose] def Functions.earlier {typeTable : TypeTable} {operations : List OperationSignature}
    {header : FunctionHeader} {functions : List FunctionHeader} :
    Functions typeTable operations (header :: functions) → Functions typeTable operations functions
  | .snoc earlier _ _ => earlier
  | .opaque earlier _ _ => earlier

/-- The protocols before the last one. -/
@[expose] def Protocols.earlier {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {header : ProtocolHeader} {protocols : List ProtocolHeader} :
    Protocols typeTable operations functions (header :: protocols) →
      Protocols typeTable operations functions protocols
  | .snoc earlier _ _ => earlier

/-- A program: its functions, then its protocols. `typeTable` is the package's
type table. -/
structure Program (typeTable : TypeTable) (operations : List OperationSignature)
    (functionHeaders : List FunctionHeader) (protocolHeaders : List ProtocolHeader) where
  functions : Functions typeTable operations functionHeaders
  protocols : Protocols typeTable operations functionHeaders protocolHeaders

/-- The sites of every protocol are numbered without gaps: the condition of a program
as written. -/
@[expose] def Protocols.dense {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols → Bool
  | _, .nil => true
  | _, .snoc earlier definition _ => earlier.dense && definition.dense typeTable

@[expose] def Program.dense {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    (program : Program typeTable operations functions protocols) : Bool :=
  program.protocols.dense

/-! ## Tables -/

/-- A row of the operation table: its catalogue identity and its signature. -/
structure Operation where
  identity : CatalogueRow
  signature : OperationSignature
  deriving Repr, DecidableEq

/-- A character of a catalogue name, by its code point: a digit, a letter, or one of
`- . / _`. -/
def nameCharacter (code : Nat) : Bool :=
  (Nat.ble 48 code && Nat.ble code 57) || (Nat.ble 65 code && Nat.ble code 90) ||
    (Nat.ble 97 code && Nat.ble code 122) ||
    (Nat.ble 45 code && Nat.ble code 47) || Nat.beq code 95

/-- A catalogue name is not empty and uses letters, digits and `. _ - /`. -/
def catalogueName (name : Name) : Bool :=
  !name.isEmpty && name.all nameCharacter

/-- The `type` arguments of a row are types of the package. -/
@[expose] def staticsNamed (typeTable : TypeTable) : List Static → Bool
  | [] => true
  | .type type :: rest => Ty.named typeTable type && staticsNamed typeTable rest
  | _ :: rest => staticsNamed typeTable rest

/-- Two names are equal. -/
def sameName : Name → Name → Bool
  | [], [] => true
  | first :: rest, other :: others => Nat.beq first other && sameName rest others
  | _, _ => false

/-- Two static arguments are equal. -/
def Static.same : Static → Static → Bool
  | .domain first, .domain second => sameName first second
  | .nat first, .nat second => Nat.beq first second
  | .type first, .type second => decide (first = second)
  | _, _ => false

def sameStatics : List Static → List Static → Bool
  | [], [] => true
  | first :: rest, other :: others => first.same other && sameStatics rest others
  | _, _ => false

/-- Two catalogue identities are equal. The test is a Boolean function written for the
kernel: it compares the names first and builds no proof for rows that differ early. -/
def CatalogueRow.same (first second : CatalogueRow) : Bool :=
  sameName first.name second.name && sameStatics first.statics second.statics

/-- No catalogue identity occurs twice. -/
def distinctIdentities : List CatalogueRow → Bool
  | [] => true
  | row :: rest => !(rest.any row.same) && distinctIdentities rest

/-- A sampling row has exactly one output. -/
def samplingRow (signature : OperationSignature) : Bool :=
  match signature.kind, signature.outputs with
  | .sampling, [_] => true
  | .sampling, _ => false
  | _, _ => true

/-- Every output type of a pure row and of a sampling row is populated: a total function
returns a value of each of its output types, and a law is a type that has a value. -/
def populatedRow (signature : OperationSignature) : Bool :=
  match signature.kind with
  | .pure | .sampling => Ty.allPopulated signature.outputs
  | .restricted _ => true

/-- The domain row that the row with the number `row` names, if it names one, is an
earlier row of the table, pure, with the inputs of the row and the one output `bool`. -/
@[expose] def domainRow (signatures : List OperationSignature) (row : Nat)
    (signature : OperationSignature) : Bool :=
  match signature.kind with
  | .restricted (some domain) =>
      Nat.blt domain row &&
        decide (signatures[domain]? = some ⟨signature.inputs, [.bool], .pure⟩)
  | _ => true

/-- Every row from the number `row` on names a domain row of the table, or none. -/
@[expose] def domainRowsFrom (signatures : List OperationSignature) :
    (row : Nat) → List OperationSignature → Bool
  | _, [] => true
  | row, signature :: rest =>
      domainRow signatures row signature && domainRowsFrom signatures (row + 1) rest

/-- Every restricted row of a table that names a domain row names an earlier pure row
with its inputs and the one output `bool`. -/
@[expose] def domainRows (signatures : List OperationSignature) : Bool :=
  domainRowsFrom signatures 0 signatures

/-- The type table of a package: its nominal rows and its declarations. -/
@[expose, reducible] def typeTableOf (types : List CatalogueRow) (records : List RecordDeclaration)
    (variants : List VariantDeclaration) : TypeTable :=
  ⟨types.length, records, variants⟩

/-- The first violated condition of the type table, the declarations and the operation
table. -/
@[expose] def tablesViolation (types : List CatalogueRow) (records : List RecordDeclaration)
    (variants : List VariantDeclaration) (operations : List Operation) : Option Violation :=
  let typeTable := typeTableOf types records variants
  firstViolation
    [(types.all fun row => catalogueName row.name, .catalogueName),
     (operations.all fun row => catalogueName row.identity.name, .catalogueName),
     (types.all fun row => staticsNamed typeTable row.statics, .nominalRow),
     (operations.all fun row =>
        staticsNamed typeTable row.identity.statics &&
          (Ty.allNamed typeTable row.signature.inputs &&
            Ty.allNamed typeTable row.signature.outputs), .nominalRow),
     (operations.all fun row => samplingRow row.signature, .samplingOutputs),
     (distinctIdentities (operations.map (·.identity)), .repeatedOperation),
     (operations.all fun row => populatedRow row.signature, .unpopulatedOutput),
     (domainRows (operations.map (·.signature)), .domainRow),
     (typeTable.declared, .declaration)]

end Zkc.Core
