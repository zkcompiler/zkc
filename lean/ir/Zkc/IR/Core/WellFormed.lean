module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.IR.Core.Dialects

@[expose] public section

/-! Residual well-formedness and programs.

Typing fixes operand types and holders, closed regions, references to earlier
definitions and to operation rows, the agreement of an operation with its row's
signature and kind, the authored reason of a `guard`, the outputs of a `branch` held
by its participants, the one type of an agreement's copies, and the prohibition on a
deployed definition using a specification-only one. The remaining conditions are
decidable facts about the numbers of a definition. Each has a name, a constructor of
`Violation`:

- a protocol has a role; holders, owners, participants and role-map entries are below
  the role count;
- a `repeat` or `branch` has a participant and lists each participant once; every
  role that an operation inside it names is a participant, and every value that
  enters or leaves it is held by one;
- the sender and the receiver of an `exchange` differ; the receivers of a `draw`
  increase strictly and exclude its owner;
- a role map has one entry per formal role of the callee, and its entries are
  distinct;
- the sites of a definition are `0 … k−1`, each used once;
- a protocol region contains no `stop`, and a `stop` in a local region names an
  authored reason;
- the copies of an agreement have different holders, and the agreements of a
  signature name each port at most once.

`Definition.violation` finds the first violated condition in one pass over the
definition, which also collects its sites. A `Program` can only be extended by a
definition with `definition.violation = none`, so the kernel decides the conditions
once for every definition it accepts.
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
  /-- A `repeat` or `branch` has no participant. -/
  | noParticipant
  /-- A `repeat` or `branch` lists a participant twice. -/
  | repeatedParticipant
  /-- An operation inside a `repeat` or `branch` names a role that is not a participant. -/
  | roleOutsideParticipants
  /-- A value that enters or leaves a `repeat` or `branch` is held by a role that is
  not a participant. -/
  | valueOutsideParticipants
  /-- The sender of an `exchange` is its receiver. -/
  | exchangeToSelf
  /-- The receivers of a `draw` do not increase strictly. -/
  | receiversNotIncreasing
  /-- The owner of a `draw` is one of its receivers. -/
  | ownerReceives
  /-- A role map does not have one entry per formal role of the callee. -/
  | roleMapLength
  /-- A role map sends two formal roles to one role. -/
  | roleMapNotInjective
  /-- A site is not below the number of sites of its definition: the numbering has a gap. -/
  | siteGap
  /-- Two operations of a definition share a site. -/
  | repeatedSite
  /-- A protocol region contains a `stop`. -/
  | protocolStop
  /-- A `stop` names the reserved reason `incomplete`. -/
  | reservedReason
  /-- Two copies of an agreement have one holder. -/
  | agreementHolders
  /-- The agreements of a signature name a port twice. -/
  | agreementPorts
  deriving Repr, Inhabited, DecidableEq

/-- The name of the first condition of a list that fails; none when all hold. -/
def firstViolation : List (Bool × Violation) → Option Violation
  | [] => none
  | (holds, violation) :: rest => cond holds (firstViolation rest) (some violation)

/-- The earlier of two findings. -/
def earlierViolation : Option Violation → Option Violation → Option Violation
  | some violation, _ => some violation
  | none, later => later

/-! ## Local regions -/

section Local

variable {operations : List OperationSignature} {headers : List Header} {deployed : Bool}

mutual
  /-- A `stop` of a local region names an authored reason. -/
  def localRegionViolation {Γ out : List Ty} :
      Region (LocalDialect operations headers deployed) Γ out → Option Violation
    | .ret _ => none
    | .stop reason => cond (authoredStop reason) none (some .reservedReason)
    | .letOp _ _ bodies next =>
        earlierViolation (localRegionsViolation bodies) (localRegionViolation next)
    | .bind body next => earlierViolation (localRegionViolation body) (localRegionViolation next)

  def localRegionsViolation {signatures : List (List Ty × List Ty)} :
      Regions (LocalDialect operations headers deployed) signatures → Option Violation
    | .nil => none
    | .cons body tail => earlierViolation (localRegionViolation body) (localRegionsViolation tail)
end

end Local

/-! ## Protocol regions -/

/-- A role may act where the participants of the enclosing `repeat` or `branch`, if
there is one, include it. -/
def participates : Option (List Nat) → Nat → Bool
  | none, _ => true
  | some participants, role => occursIn participants role

/-- The roles that act at one place are below the role count and, inside a `repeat`
or `branch`, participants. -/
def actingRoles (roles : Nat) (enclosing : Option (List Nat)) (acting : List Nat) :
    List (Bool × Violation) :=
  [(acting.all fun role => Nat.blt role roles, .roleOutOfRange),
   (acting.all (participates enclosing), .roleOutsideParticipants)]

/-- The sender and the receiver of an `exchange` differ. -/
def exchangeConditions (sender receiver : Nat) : List (Bool × Violation) :=
  [(!(Nat.beq sender receiver), .exchangeToSelf)]

/-- The receivers of a `draw` increase strictly and exclude its owner. -/
def drawConditions (owner : Nat) (receivers : List Nat) : List (Bool × Violation) :=
  [(increasingNumbers receivers, .receiversNotIncreasing),
   (!(occursIn receivers owner), .ownerReceives)]

/-- The participants of a `repeat` or `branch`: at least one, each once, holding
every value that enters or leaves. -/
def participantConditions (participants : List Nat) (values : List Located) :
    List (Bool × Violation) :=
  [(!participants.isEmpty, .noParticipant),
   (distinctNumbers participants, .repeatedParticipant),
   (Located.heldBy participants values, .valueOutsideParticipants)]

/-- A role map has one entry per formal role of the callee, and distinct entries. -/
def roleMapConditions (formal : Nat) (roleMap : RoleMap) : List (Bool × Violation) :=
  [(Nat.beq roleMap.length formal, .roleMapLength),
   (distinctNumbers roleMap, .roleMapNotInjective)]

/-- A protocol has a role, and the holders of its ports are below its role count. -/
def portConditions (roles : Nat) (ports : List Located) : List (Bool × Violation) :=
  [(!(Nat.beq roles 0), .noRole),
   (ports.all fun port => Nat.blt port.holder roles, .roleOutOfRange)]

/-- The copies of each agreement have different holders, and no port is named twice:
`holders` lists the holders of each agreement's copies, `ports` the positions of
the ports that the agreements name. -/
def copyConditions (holders : List (List Nat)) (ports : List Nat) : List (Bool × Violation) :=
  [(holders.all distinctNumbers, .agreementHolders),
   (distinctNumbers ports, .agreementPorts)]

section Protocol

variable {operations : List OperationSignature} {headers : List Header} {deployed : Bool}

/-- Every role that a protocol operation names: an owner, a sender, a receiver, the
receivers of a draw, the participants of a `repeat` or `branch`, the entries of a
role map. -/
def ProtocolOp.roles : ProtocolOp operations headers deployed → List Nat
  | .at role .. => [role]
  | .exchange sender receiver .. => [sender, receiver]
  | .draw owner receivers .. => owner :: receivers
  | .sample owner .. => [owner]
  | .repeat participants .. | .branch participants .. => participants
  | .apply _ roleMap .. => roleMap

/-- The site of a protocol operation, when it has one. -/
def ProtocolOp.sites : ProtocolOp operations headers deployed → List Nat
  | .exchange _ _ site _ | .draw _ _ site _ | .sample _ site _ | .apply _ _ site _ => [site]
  | .at .. | .repeat .. | .branch .. => []

/-- The first violated condition of one protocol operation of a protocol with `roles`
roles, inside the `repeat` or `branch` whose participants are `enclosing`. -/
def ProtocolOp.violation (roles : Nat) (enclosing : Option (List Nat)) :
    (op : ProtocolOp operations headers deployed) → Option Violation
  | op@(.at _ _ bodies) =>
      earlierViolation (firstViolation (actingRoles roles enclosing op.roles))
        (localRegionsViolation bodies)
  | op@(.exchange sender receiver _ _) =>
      firstViolation (actingRoles roles enclosing op.roles ++ exchangeConditions sender receiver)
  | op@(.draw owner receivers _ _) =>
      firstViolation (actingRoles roles enclosing op.roles ++ drawConditions owner receivers)
  | op@(.sample ..) => firstViolation (actingRoles roles enclosing op.roles)
  | op@(.repeat participants _ carried captures) =>
      firstViolation (actingRoles roles enclosing op.roles ++
        participantConditions participants (carried ++ captures))
  | op@(.branch participants captures outputs _) =>
      firstViolation (actingRoles roles enclosing op.roles ++
        participantConditions participants (captures ++ outputs))
  | op@(.apply (roles := formal) _ roleMap _ _) =>
      firstViolation (actingRoles roles enclosing op.roles ++ roleMapConditions formal roleMap)

/-- The participants that enclose an operation's regions: its own, for a `repeat` or
`branch`. -/
def ProtocolOp.enclosing (enclosing : Option (List Nat)) :
    ProtocolOp operations headers deployed → Option (List Nat)
  | .repeat participants .. | .branch participants .. => some participants
  | .at .. | .exchange .. | .draw .. | .sample .. | .apply .. => enclosing

mutual
  /-- One pass over a protocol region: the first violated condition of its
  operations, or the sites it uses, nested regions and both arms of a `branch`
  included, before the sites met so far. -/
  def protocolRegionSites {Γ out : List Located} (roles : Nat) (enclosing : Option (List Nat)) :
      Region (ProtocolDialect operations headers deployed) Γ out → List Nat →
        Except Violation (List Nat)
    | .ret _, sites => .ok sites
    | .stop _, _ => .error .protocolStop
    | .letOp op _ bodies next, sites =>
        match ProtocolOp.violation roles enclosing op with
        | some violation => .error violation
        | none =>
            match protocolRegionsSites roles (ProtocolOp.enclosing enclosing op) bodies
              (ProtocolOp.sites op ++ sites) with
            | .error violation => .error violation
            | .ok sites => protocolRegionSites roles enclosing next sites
    | .bind body next, sites =>
        match protocolRegionSites roles enclosing body sites with
        | .error violation => .error violation
        | .ok sites => protocolRegionSites roles enclosing next sites

  def protocolRegionsSites {signatures : List (List Located × List Located)} (roles : Nat)
      (enclosing : Option (List Nat)) :
      Regions (ProtocolDialect operations headers deployed) signatures → List Nat →
        Except Violation (List Nat)
    | .nil, sites => .ok sites
    | .cons body tail, sites =>
        match protocolRegionSites roles enclosing body sites with
        | .error violation => .error violation
        | .ok sites => protocolRegionsSites roles enclosing tail sites
end

end Protocol

/-! ## Sites -/

/-- The remaining sites are below `count` and unused. The used sites are the set bits
of `seen`. A site is compared with `count` before its bit is formed, so no numeral
has more bits than the definition has sites. -/
def unusedSites (count : Nat) : Nat → List Nat → Option Violation
  | _, [] => none
  | seen, site :: rest =>
      cond (Nat.blt site count)
        (cond (seen.testBit site) (some .repeatedSite)
          (unusedSites count (seen ||| (1 <<< site)) rest))
        (some .siteGap)

/-- The sites of a definition, in any order, are `0 … k−1`, each used once: there
are `k` of them, each is below `k`, and none repeats. -/
def sitesViolation (sites : List Nat) : Option Violation := unusedSites sites.length 0 sites

/-! ## Agreements -/

/-- The conditions of the agreements over one list of ports. -/
def agreementConditions {ports : List Located} (agreements : List (Agreement ports)) :
    List (Bool × Violation) :=
  copyConditions (agreements.map fun agreement => agreement.copies.map (·.holder))
    (agreements.flatMap fun agreement => agreement.copies.map (·.port.index))

/-! ## Definitions and programs -/

section Definitions

variable {operations : List OperationSignature} {headers : List Header}

/-- The first violated residual condition of a definition; none when it is well
formed. A protocol's signature is decided first, then its body in one pass, then the
sites that the pass collected. -/
def Definition.violation :
    {header : Header} → Definition operations headers header → Option Violation
  | _, .function _ body => localRegionViolation body
  | _, .protocol (inputs := inputs) (outputs := outputs) roles agreements _ body =>
      earlierViolation
        (firstViolation
          (portConditions roles (inputs ++ outputs) ++
            (agreementConditions agreements.inputs ++ agreementConditions agreements.outputs)))
        (match protocolRegionSites roles none body [] with
          | .error violation => some violation
          | .ok sites => sitesViolation sites)

end Definitions

/-- A program: definitions in order, each typed over the operation table and the
headers of the earlier ones, and each without a residual violation. The index lists
the headers, most recent first. -/
inductive Program (operations : List OperationSignature) : List Header → Type where
  | nil : Program operations []
  | snoc {headers : List Header} {header : Header} (earlier : Program operations headers)
      (definition : Definition operations headers header)
      (wellFormed : definition.violation = none) : Program operations (header :: headers)

/-- The agreements of the signature of a program's last definition, a protocol. -/
def Program.agreements {operations : List OperationSignature} {headers : List Header} {roles : Nat}
    {inputs outputs : List Located} {agreements : Agreements inputs outputs}
    {specificationOnly : Bool}
    (_ : Program operations (.protocol roles inputs outputs agreements specificationOnly :: headers)) :
    Agreements inputs outputs :=
  agreements

end Zkc.Core

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.firstViolation
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.earlierViolation
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.localRegionViolation
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.localRegionsViolation
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.participates
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.ProtocolOp.roles
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.ProtocolOp.sites
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.ProtocolOp.violation
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.ProtocolOp.enclosing
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.protocolRegionSites
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.protocolRegionsSites
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.unusedSites
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Definition.violation
