module

public import Zkc.Core.ThreadMarks

public section

/-! A threading step over the protocols of a program.

Two passes over the protocols, in one structural recursion:

1. On the way down, from the newest protocol: the ways each definition is reached
   (`Demand`). The entry is reached with the declaration's two roles; an application
   reaches its callee with their preimages under the role map. A definition that is not
   reached from the entry has no image: the result is the program of the entry.
2. On the way up, from the oldest: the images of each definition, typed over the images
   before them. For every demand `touches` decides whether the definition changes. It
   has one image per pair of roles for which it changes, and one image with its own
   header for all the other demands together. Each image is checked for residual
   violations when it is added, so the result is a `Protocols` value.

The functions of the program are not an argument: no step looks at them.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- How a definition is reached: as the entry, or by an application under which the
caller's prover and verifier run as these roles of the definition, if as any. -/
inductive Demand where
  | entry (roles : TranscriptRoles)
  | applied (prover verifier : Option Nat)
  deriving Repr, DecidableEq

@[expose] def Demand.prover : Demand → Option Nat
  | .entry roles => some roles.prover
  | .applied prover _ => prover

@[expose] def Demand.verifier : Demand → Option Nat
  | .entry roles => some roles.verifier
  | .applied _ verifier => verifier

@[expose] def Demand.isApplied : Demand → Bool
  | .entry _ => false
  | .applied .. => true

/-- One more demand of the protocol at a position, the most recent first. -/
@[expose] def addDemand (demand : Demand) : Nat → List (List Demand) → List (List Demand)
  | 0, [] => [[demand]]
  | 0, own :: older =>
      (if own.any fun other => decide (other = demand) then own else demand :: own) :: older
  | index + 1, [] => [] :: addDemand demand index []
  | index + 1, own :: older => own :: addDemand demand index older

section Applications

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The callee's position and the role map of an application. -/
@[expose] def applicationOf : ProtocolOp operations functions protocols deployed → List (Nat × RoleMap)
  | .apply callee roleMap _ _ => [(callee.index, roleMap)]
  | .at .. | .exchange .. | .draw .. | .sample .. | .repeat .. | .choose .. => []

mutual
  /-- The applications of a region, nested regions included, before those found so far. -/
  @[expose] def applications {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out →
        List (Nat × RoleMap) → List (Nat × RoleMap)
    | .ret _, found => found
    | .stop _, found => found
    | .bind body rest, found => applications rest (applications body found)
    | .letOp op _ bodies rest, found =>
        applications rest (applicationsOf bodies (applicationOf op ++ found))

  @[expose] def applicationsOf {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures →
        List (Nat × RoleMap) → List (Nat × RoleMap)
    | .nil, found => found
    | .cons body tail, found => applicationsOf tail (applications body found)
end

end Applications

/-- The demands of the earlier protocols after one definition that is reached in the
given ways and has the given applications. -/
@[expose] def propagate (own : List Demand) (applied : List (Nat × RoleMap))
    (older : List (List Demand)) : List (List Demand) :=
  own.foldl (fun older demand =>
    applied.foldl (fun older application =>
      addDemand (.applied (preimageOf application.2 demand.prover)
        (preimageOf application.2 demand.verifier)) application.1 older) older) older

/-- Where a protocol of the result comes from: the identity of its definition, which the
image keeps, the roles it threads for, and whether it is the entry. -/
structure Origin where
  definition : Nat
  roles : Option TranscriptRoles
  entry : Bool
  deriving Repr

/-- The identities of the protocols of a step's result, from where each comes from: the
origins list the protocols from the newest, and the protocol with a number has the
identity of its definition. -/
@[expose] def originIdentities : List Origin → Identities
  | [] => Identities.written
  | origin :: earlier => fun number =>
      if number = earlier.length then origin.definition else originIdentities earlier number

section Driver

variable {typeTable : TypeTable} {operations : List OperationSignature} {functions : List FunctionHeader}
variable (t : Threads)

/-- The images made so far, among them those of one definition with the positions the
callee table will record. -/
structure Images (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (old : List ProtocolHeader) (header : ProtocolHeader) where
  new : List ProtocolHeader
  protocols : Protocols typeTable operations functions new
  table : CalleeTable t.header old new
  list : List (Option TranscriptRoles × Nat)
  valid : ∀ pair ∈ list, atLevel? new table.depth pair.2 = some (t.header pair.1 header)
  origins : List Origin
  counted : origins.length = new.length

variable {t}

/-- One more image of the definition, for a key. -/
@[expose] def Images.add {old : List ProtocolHeader} {header : ProtocolHeader}
    (images : Images t typeTable operations functions old header) (key : Option TranscriptRoles)
    (body : Region
      (ProtocolDialect operations functions images.new (!(t.header key header).specificationOnly))
      (bindAll [] (t.header key header).inputs) (t.header key header).outputs)
    (origin : Origin) : Except StepRefusal (Images t typeTable operations functions old header) :=
  match wellFormed : (ProtocolDefinition.mk (protocols := images.new)
      (header := t.header key header) body).violation typeTable with
  | none =>
      .ok ⟨t.header key header :: images.new, .snoc images.protocols ⟨body⟩ wellFormed,
        images.table.weaken _, (key, images.table.depth) :: images.list,
        fun pair member => by
          rcases List.mem_cons.mp member with rfl | earlier
          · show atLevel? (t.header key header :: images.new) (images.table.depth + 1)
              images.table.depth = some _
            rw [images.table.counted]
            exact atLevel?_newest images.new _
          · exact atLevel?_cons images.new _ (images.valid pair earlier),
        origin :: images.origins, congrArg (· + 1) images.counted⟩
  | some violation => .error (.residual violation)

/-- The header of the entry after a step: its ports change, nothing else. -/
@[expose, reducible] def EntryPorts.header (ports : EntryPorts) (header : ProtocolHeader) : ProtocolHeader :=
  ⟨header.roles, ports.inputs, ports.outputs, ports.agreements, header.specificationOnly⟩

/-- The image of the entry. No application names it, so the callee table does not
record it. -/
@[expose] def Images.addEntry {old : List ProtocolHeader} {header : ProtocolHeader}
    (images : Images t typeTable operations functions old header) (ports : EntryPorts)
    (body : Region (ProtocolDialect operations functions images.new (!header.specificationOnly))
      (bindAll [] ports.inputs) ports.outputs)
    (origin : Origin) : Except StepRefusal (Images t typeTable operations functions old header) :=
  match wellFormed : (ProtocolDefinition.mk (protocols := images.new)
      (header := ports.header header) body).violation typeTable with
  | none =>
      .ok ⟨ports.header header :: images.new,
        .snoc (header := ports.header header) images.protocols ⟨body⟩ wellFormed,
        images.table.weaken _,
        images.list, fun pair member => atLevel?_cons images.new _ (images.valid pair member),
        origin :: images.origins, congrArg (· + 1) images.counted⟩
  | some violation => .error (.residual violation)

variable (t) (rule : Rule t operations functions)

/-- For each demand of a definition, whether the definition changes for it. -/
@[expose] def classify {old new : List ProtocolHeader} {header : ProtocolHeader}
    (table : CalleeTable t.header old new) (number : Nat)
    (definition : ProtocolDefinition operations functions old header) :
    List Demand → Except StepRefusal (List (Demand × Bool))
  | [] => .ok []
  | demand :: rest =>
      match touches t rule.derives table number demand.prover demand.verifier definition.body,
          classify table number definition rest with
      | .ok active, .ok rest => .ok ((demand, active) :: rest)
      | .error refusal, _ => .error refusal
      | _, .error refusal => .error refusal

/-- The image with the definition's own header, once. -/
@[expose] def plainImage {old : List ProtocolHeader} {header : ProtocolHeader} (number : Nat)
    (definition : ProtocolDefinition operations functions old header) (made : Bool)
    (images : Images t typeTable operations functions old header) :
    Except StepRefusal (Images t typeTable operations functions old header) :=
  if made then .ok images
  else
    match plainRegion t images.table definition.body (Renaming.identity header.inputs) with
    | .ok body => images.add none body ⟨number, none, false⟩
    | .error refusal => .error refusal

/-- The images of one definition, one demand after the other. `made` says whether the
image with the definition's own header exists. -/
@[expose] def rewriteDefinition {old : List ProtocolHeader} {header : ProtocolHeader} (number : Nat)
    (definition : ProtocolDefinition operations functions old header) (specialized : Bool) :
    List (Demand × Bool) → Bool → Images t typeTable operations functions old header →
      Except StepRefusal (Images t typeTable operations functions old header)
  | [], _, images => .ok images
  | (.applied (some prover) (some verifier), true) :: rest, made, images =>
      let place : Place := ⟨number, ⟨prover, verifier⟩, specialized⟩
      let start := afterTwo (t.first place.roles) (t.second place.roles)
        (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs
      match threadRegion t rule images.table place definition.body start.1 start.2.1 start.2.2 with
      | .ok body =>
          match images.add (some place.roles) body ⟨number, some place.roles, false⟩ with
          | .ok images => rewriteDefinition number definition specialized rest made images
          | .error refusal => .error refusal
      | .error refusal => .error refusal
  | (.entry roles, active) :: rest, made, images =>
      if let some refusal := rule.entryRefusal roles header then .error refusal
      else if active || rule.idleEntry then
        let place : Place := ⟨number, roles, false⟩
        match rule.entry place header (fun rename first second =>
            threadRegion t rule images.table place definition.body rename first second) with
        | .ok body =>
            match images.addEntry (rule.entryPorts roles header) body ⟨number, some roles, true⟩ with
            | .ok images => rewriteDefinition number definition specialized rest made images
            | .error refusal => .error refusal
        | .error refusal => .error refusal
      else
        match plainImage t number definition made images with
        | .ok images => rewriteDefinition number definition specialized rest true images
        | .error refusal => .error refusal
  | (.applied .., _) :: rest, made, images =>
      match plainImage t number definition made images with
      | .ok images => rewriteDefinition number definition specialized rest true images
      | .error refusal => .error refusal

/-- The images of the protocols of a program, with the table from the old protocols. -/
structure Rewritten (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) (old : List ProtocolHeader) where
  new : List ProtocolHeader
  protocols : Protocols typeTable operations functions new
  table : CalleeTable t.header old new
  origins : List Origin
  counted : origins.length = new.length
  /-- What the step rewrote: the marks of every old protocol, for every pair of roles. -/
  marks : MarkTable operations old

/-- The images of every protocol. `identities` are the identities of the protocols
before the step; an image has the identity of its definition. `demands` lists, for each
protocol from the newest, the ways it is reached from the protocols after it. -/
@[expose] def rewriteProtocols (identities : Identities) :
    {old : List ProtocolHeader} → Protocols typeTable operations functions old →
      List (List Demand) → Except StepRefusal (Rewritten t typeTable operations functions old)
  | _, .nil, _ => .ok ⟨[], .nil, .empty, [], rfl, .nil⟩
  | _, .snoc (protocols := earlier) (header := header) protocols definition _, demands =>
      let own := demands.headD []
      match rewriteProtocols identities protocols
          (propagate own (applications definition.body []) demands.tail) with
      | .ok ⟨new, typed, table, origins, counted, marks⟩ =>
          match classify t rule table (identities earlier.length) definition own with
          | .ok classified =>
              let threading := classified.filter fun entry => entry.2 && entry.1.isApplied
              match rewriteDefinition t rule (identities earlier.length) definition
                  (Nat.ble 2 threading.length) classified false
                  ⟨new, typed, table, [], (fun _ member => nomatch member), origins, counted⟩ with
              | .ok images =>
                  .ok ⟨images.new, images.protocols,
                    images.table.extend header images.list images.valid, images.origins,
                    images.counted,
                    .cons (fun roles => regionMarks table.threads marks
                      ⟨identities earlier.length, roles, Nat.ble 2 threading.length⟩
                      definition.body) marks⟩
              | .error refusal => .error refusal
          | .error refusal => .error refusal
      | .error refusal => .error refusal

/-- The protocols of a program after a step, with where each comes from. -/
structure Stepped (typeTable : TypeTable) (operations : List OperationSignature)
    (functions : List FunctionHeader) where
  headers : List ProtocolHeader
  protocols : Protocols typeTable operations functions headers
  origins : List Origin
  counted : origins.length = headers.length

/-- The identities of the protocols after a step: each image has the identity of the
definition it comes from. -/
@[expose] def Stepped.identities {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} (stepped : Stepped typeTable operations functions) :
    Identities :=
  originIdentities stepped.origins

/-- The declared prover and verifier are roles of the entry. -/
@[expose] def declaredRolesBelow (roles : TranscriptRoles) : Option ProtocolHeader → Bool
  | some header => Nat.blt roles.prover header.roles && Nat.blt roles.verifier header.roles
  | none => false

/-- The ways the protocols of a program are reached before any application is followed:
the declared protocol as the entry, no other protocol. -/
@[expose] def entryDemands (count entry : Nat) (roles : TranscriptRoles) : List (List Demand) :=
  List.replicate (count - 1 - entry) [] ++ [[.entry roles]]

/-- The step on the program of an entry: `entry` is the number of the declared protocol
among the protocols, `roles` its prover and verifier, `identities` the identities of the
protocols. A declaration that names no protocol, one role twice, or a role that the entry
does not have is refused. -/
@[expose] def stepProtocols (identities : Identities) (entry : Nat) (roles : TranscriptRoles)
    {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old) :
    Except StepRefusal (Stepped typeTable operations functions) :=
  if Nat.blt entry old.length && !(Nat.beq roles.prover roles.verifier) &&
      declaredRolesBelow roles (old[old.length - 1 - entry]?) then
    match rewriteProtocols t rule identities protocols (entryDemands old.length entry roles) with
    | .ok rewritten =>
        .ok ⟨rewritten.new, rewritten.protocols, rewritten.origins, rewritten.counted⟩
    | .error refusal => .error refusal
  else .error .entry

/-- What a step rewrote, for a handler of the effects of the declared entry: the mark of
every site relative to the entry. No site is marked when the step has no result. -/
@[expose] def stepMarks (identities : Identities) (entry : Nat) (roles : TranscriptRoles)
    {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old) :
    Site → Option (Mark operations) :=
  match rewriteProtocols t rule identities protocols (entryDemands old.length entry roles) with
  | .ok rewritten => rewritten.marks.at (old.length - 1 - entry) roles
  | .error _ => fun _ => none

end Driver

/-- A definition that is not reached adds no demand of the earlier protocols. -/
theorem propagate_nil (applied : List (Nat × RoleMap)) (older : List (List Demand)) :
    propagate [] applied older = older := by
  unfold propagate
  rfl

end Zkc.Core
