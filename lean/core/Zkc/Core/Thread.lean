module

public import Zkc.Core.Retarget
public import Zkc.Core.Emit

public section

/-! Threading two values through a whole program.

The Fiat–Shamir step threads one transcript state per transcript role; the serialize
step threads a writer at the prover and a reader at the verifier. Both are instances of
the function of this module. A step supplies a `Rule`: what an exchange from the prover
to the verifier and a draw between the two become, and how the entry starts and ends.
Everything else is here, once:

- **Transcript roles of a definition.** The entry names the prover and the verifier.
  An application gives the callee the preimages of the caller's two roles under its role
  map; either may have none. A first pass, from the entry down, records for every
  definition the pairs under which it is reached (`Demand`).
- **Which definitions change.** For a pair, `touches` decides whether a definition
  contains a rewritten operation, directly or through applications, and finds the
  refusals that concern the shape of the program. A definition that changes for a pair is
  rewritten once for that pair: its image takes and returns the two threaded values. For
  all other pairs it has one image with its own header.
- **Threading.** `threadRegion` carries the two values as references of the new
  context. A `repeat` carries them and a `choose` captures and returns them when their
  regions contain a rewritten operation; an `apply` passes and receives them when the
  callee has an image for the pair.
- **A loop that collects.** A `repeat` returns the sequences of what its region collects
  before what it carries, and its region returns the collected values before the carried
  ones. A loop that threads carries the two values before its own carried values, so they
  stand between the collected sequences and the carried results: its region is the
  threaded region followed by a return that puts the two values after the collected ones
  (`Region.returnAfter`), and after the loop the old results are renamed around the two
  (`afterLeading`). A loop that collects nothing has nothing before the two, and its
  region is the threaded region itself.
- **Callees.** A `CalleeTable` keyed by `Option TranscriptRoles` maps an old callee to
  its image: `some roles` for the image that threads, `none` for the other one.

A local operation with its nested regions passes into the result as the same term, and
the functions of the program are not visited. Every protocol term is rebuilt, also in a
definition that does not change, because it is typed over the list of protocol headers.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The prover's and the verifier's role in one definition. -/
structure TranscriptRoles where
  prover : Nat
  verifier : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The types of the two threaded values: one held by the prover, one by the verifier. -/
structure Threads where
  prover : Ty
  verifier : Ty

namespace Threads

variable (t : Threads)

/-- The prover's threaded value in a definition. -/
@[expose, reducible] def first (roles : TranscriptRoles) : Located := ⟨t.prover, roles.prover⟩

/-- The verifier's. -/
@[expose, reducible] def second (roles : TranscriptRoles) : Located := ⟨t.verifier, roles.verifier⟩

/-- The two threaded values, the prover's first. -/
@[expose, reducible] def states (roles : TranscriptRoles) : List Located := [t.first roles, t.second roles]

end Threads

/-- An agreement over ports that follow one more port. -/
@[expose] def Agreement.under {ports : List Located} (head : Located) (agreement : Agreement ports) :
    Agreement (head :: ports) :=
  ⟨agreement.type, ⟨agreement.first.holder, agreement.first.port.there⟩,
    agreement.others.map fun copy => ⟨copy.holder, copy.port.there⟩⟩

/-- The header of an image: the old header, or the old header with the two threaded
values before its inputs and before its outputs. -/
@[expose, reducible] def Threads.header (t : Threads) : Option TranscriptRoles → ProtocolHeader → ProtocolHeader
  | none, header => header
  | some roles, header =>
      ⟨header.roles, t.states roles ++ header.inputs, t.states roles ++ header.outputs,
        ⟨header.agreements.inputs.map fun agreement =>
            (agreement.under (t.second roles)).under (t.first roles),
          header.agreements.outputs.map fun agreement =>
            (agreement.under (t.second roles)).under (t.first roles)⟩,
        header.specificationOnly⟩

/-- For each region of a list, its inputs as the values before the two threaded values and
the values after them. It fixes the signature of the region that threads: it takes the two
values between them and returns the two before its outputs. -/
inductive ThreadedRegions (t : Threads) (roles : TranscriptRoles) :
    List (List Located × List Located) → List (List Located × List Located) → Type where
  | nil : ThreadedRegions t roles [] []
  | cons (leading added : List Located) {outputs : List Located}
      {rest targets : List (List Located × List Located)}
      (tail : ThreadedRegions t roles rest targets) :
      ThreadedRegions t roles ((leading ++ added, outputs) :: rest)
        ((leading ++ (t.states roles ++ added), t.states roles ++ outputs) :: targets)

/-- The regions of a choice on a condition or an arm number that threads: each takes the
two values before the captures. -/
@[expose] def Threads.arms (t : Threads) (roles : TranscriptRoles) (captures outputs : List Located) :
    (count : Nat) →
      ThreadedRegions t roles (List.replicate count (captures, outputs))
        (List.replicate count (t.states roles ++ captures, t.states roles ++ outputs))
  | 0 => .nil
  | count + 1 => .cons [] captures (Threads.arms t roles captures outputs count)

/-- The regions of a choice on a variant that threads: the region of an alternative takes
the two values after the payloads of the participants and before the captures. -/
@[expose] def Threads.alternatives (t : Threads) (roles : TranscriptRoles)
    (participants : List Nat) (captures outputs : List Located) :
    (alternatives : List Ty) →
      ThreadedRegions t roles
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ (t.states roles ++ captures),
            t.states roles ++ outputs))
  | [] => .nil
  | payload :: rest =>
      .cons (Located.ofRoles payload participants) captures
        (Threads.alternatives t roles participants captures outputs rest)

/-- The regions of a choice that threads, as the regions of the choice that captures and
returns the two values. -/
@[expose] def Threads.choice (t : Threads) (roles : TranscriptRoles) (participants : List Nat)
    (captures outputs : List Located) :
    (tag : ChoiceTag) →
      ThreadedRegions t roles (tag.regions participants captures outputs)
        (tag.regions participants (t.states roles ++ captures) (t.states roles ++ outputs))
  | .condition => Threads.arms t roles captures outputs 2
  | .arm count => Threads.arms t roles captures outputs count
  | .alternative _ alternatives => Threads.alternatives t roles participants captures outputs alternatives

/-- Values that stand before `leading ++ trailing`, put between the two. -/
@[expose] def Values.between {Ty : Type} {Value : Ty → Type} {states : List Ty} (leading : List Ty)
    {trailing : List Ty} (values : Values Value (states ++ (leading ++ trailing))) :
    Values Value (leading ++ (states ++ trailing)) :=
  ((Values.split states values).2.split leading).1.append
    ((Values.split states values).1.append ((Values.split states values).2.split leading).2)

/-- A region that returns `states` before its other outputs, as a region that returns them
after the first of those, `leading`: the region, then a return of its values in the other
order. With nothing before them it is the region itself. -/
@[expose] def Region.returnAfter {dialect : Dialect} {Δ : List dialect.Ty} (states : List dialect.Ty) :
    (leading : List dialect.Ty) → {trailing : List dialect.Ty} →
      Region dialect Δ (states ++ (leading ++ trailing)) →
        Region dialect Δ (leading ++ (states ++ trailing))
  | [], _, region => region
  | head :: rest, _, region =>
      .bind region (.ret (Values.between (head :: rest) (Operands.newest _)))

/-- Why a step has no result. The first group are conditions on the program, which the
checker decides for a declaration before the step runs; the second are conditions on the
rows of the suite or layout; the third are no condition of either kind, and neither
occurs for a program of well-formed definitions and a rule that emits what the check of
a definition accepts (`stepProtocols_external`, `stepProtocols_returns` in
`Core/LegalStep.lean`). -/
inductive StepRefusal where
  /-- The declaration names no protocol of the program, or one role twice. -/
  | entry
  /-- An input of the entry held by the verifier has no copy held by the prover. -/
  | verifierInput (position : Nat)
  /-- A draw by a transcript role that does not have the other as its only receiver. -/
  | drawShape (definition site : Nat)
  /-- An exchange from the verifier to the prover. -/
  | towardProver (definition site : Nat)
  /-- An exchange or a draw between exactly one transcript role and another online role. -/
  | thirdRole (definition site : Nat)
  /-- A derived draw whose law has inputs. -/
  | lawInputs (definition site : Nat)
  /-- A draw between the transcript roles in a program that is serialized. -/
  | interactive (definition site : Nat)
  /-- The suite does not decode the law of a derived draw. -/
  | undecoded (definition site : Nat)
  /-- The suite or layout has no row for the type of a message, or no label. -/
  | message (definition site : Nat)
  /-- The type of a message has no value: no reader gives one. -/
  | unpopulated (definition site : Nat)
  /-- The suite has no start, or no row for a part of the statement. -/
  | statement (position : Nat)
  /-- A fixed row of the suite or layout is missing or has another signature. -/
  | row
  /-- An applied protocol has no image, or a threaded value is not held by a
  participant. -/
  | image
  /-- A rewritten definition violates a residual condition. -/
  | residual (violation : Violation)
  deriving Repr

/-- Both findings, the first refusal first. -/
@[expose] def bothTouch : Except StepRefusal Bool → Except StepRefusal Bool → Except StepRefusal Bool
  | .ok first, .ok second => .ok (first || second)
  | .error refusal, _ => .error refusal
  | _, .error refusal => .error refusal

/-! ## Roles under a role map -/

/-- The callee role below `bound` that runs as the given role of the caller. -/
@[expose] def preimageBelow (roleMap : RoleMap) (role : Nat) :
    Nat → Option { index : Nat // roleMap.apply index = role }
  | 0 => none
  | bound + 1 =>
      if same : roleMap.apply bound = role then some ⟨bound, same⟩
      else preimageBelow roleMap role bound

/-- The callee role that runs as the given role of the caller. A role map is injective,
so there is at most one. -/
@[expose] def preimage (roleMap : RoleMap) (role : Nat) : Option { index : Nat // roleMap.apply index = role } :=
  preimageBelow roleMap role roleMap.length

/-- The callee role that runs as a role of the caller that may be absent. -/
@[expose] def preimageOf (roleMap : RoleMap) : Option Nat → Option Nat
  | none => none
  | some role => (preimage roleMap role).map (·.val)

/-- A role is the given one. -/
@[expose] def isRole : Option Nat → Nat → Bool
  | none, _ => false
  | some role, other => Nat.beq role other

/-! ## The step's rows -/

/-- Where a rewritten operation stands: the identity of its definition, the definition's
transcript roles, and whether the definition has several images that thread. -/
structure Place where
  definition : Nat
  roles : TranscriptRoles
  specialized : Bool

/-- The ports of the entry after the step. -/
structure EntryPorts where
  inputs : List Located
  outputs : List Located
  agreements : Agreements inputs outputs

/-- What a step does at the operations it rewrites. Each field is typed over any list of
protocol headers: what it emits names no protocol. -/
structure Rule (t : Threads) (operations : List OperationSignature)
    (functions : List FunctionHeader) where
  /-- An exchange from the prover to the verifier: the receiver's value and the two new
  threaded values. -/
  exchange : {protocols : List ProtocolHeader} → {deployed : Bool} → (place : Place) →
    (site : Nat) → (type : Ty) → {Δ : List Located} → Var Δ ⟨type, place.roles.prover⟩ →
      Var Δ (t.first place.roles) → Var Δ (t.second place.roles) →
        Except StepRefusal (Emitted (ProtocolDialect operations functions protocols deployed) Δ
          [⟨type, place.roles.verifier⟩, t.first place.roles, t.second place.roles])
  /-- Whether a draw by one transcript role with the other as its only receiver is
  rewritten. When it is not, such a draw is refused. -/
  derives : Bool
  /-- A draw between the two: the prover's coin, the verifier's coin and the two new
  threaded values. -/
  draw : {protocols : List ProtocolHeader} → {deployed : Bool} → (place : Place) →
    (site : Nat) → {inputs : List Ty} → {output : Ty} →
      Var operations ⟨inputs, [output], .sampling⟩ → {Δ : List Located} →
        Var Δ (t.first place.roles) → Var Δ (t.second place.roles) →
          Except StepRefusal (Emitted (ProtocolDialect operations functions protocols deployed) Δ
            [⟨output, place.roles.prover⟩, ⟨output, place.roles.verifier⟩, t.first place.roles,
              t.second place.roles])
  /-- A condition on the header of the entry, decided whether or not the entry contains a
  rewritten operation. -/
  entryRefusal : TranscriptRoles → ProtocolHeader → Option StepRefusal
  /-- The ports of the entry after the step. -/
  entryPorts : TranscriptRoles → ProtocolHeader → EntryPorts
  /-- The body of the entry, from its threaded body: the two values are made before it
  and consumed after it. -/
  entry : {protocols : List ProtocolHeader} → {deployed : Bool} → (place : Place) →
    (header : ProtocolHeader) →
      (body : {Δ : List Located} → Renaming (bindAll [] header.inputs) Δ →
        Var Δ (t.first place.roles) → Var Δ (t.second place.roles) →
          Except StepRefusal (Region (ProtocolDialect operations functions protocols deployed) Δ
            (t.states place.roles ++ header.outputs))) →
        Except StepRefusal (Region (ProtocolDialect operations functions protocols deployed)
          (bindAll [] (entryPorts place.roles header).inputs) (entryPorts place.roles header).outputs)
  /-- Whether the entry is rewritten when it contains no rewritten operation. -/
  idleEntry : Bool

section Step

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool}
variable (t : Threads)

/-! ## Which regions contain a rewritten operation -/

/-- Whether one operation is rewritten for the transcript roles, either of which may be
absent; a refusal when its shape excludes the step. An application is rewritten when the
callee has an image that threads for the preimages of the two roles. -/
@[expose] def touchesOp (derives : Bool) (table : CalleeTable t.header old new) (definition : Nat)
    (prover verifier : Option Nat) :
    ProtocolOp operations functions old deployed → Except StepRefusal Bool
  | .exchange sender receiver site _ =>
      if isRole prover sender && isRole verifier receiver then .ok true
      else if isRole verifier sender && isRole prover receiver then
        .error (.towardProver definition site)
      else .ok false
  | .draw owner receivers site (inputs := inputs) _ _ =>
      if isRole prover owner || isRole verifier owner then
        let other := if isRole prover owner then verifier else prover
        if derives then
          match other, receivers with
          | some other, [receiver] =>
              if Nat.beq receiver other then
                if inputs.isEmpty then .ok true else .error (.lawInputs definition site)
              else .error (.drawShape definition site)
          | _, _ => .error (.drawShape definition site)
        else
          match other with
          | some other =>
              if occursIn receivers other then .error (.interactive definition site) else .ok false
          | none => .ok false
      else .ok false
  | .apply callee roleMap _ _ =>
      match preimageOf roleMap prover, preimageOf roleMap verifier with
      | some inner, some outer => .ok (table.find callee (some ⟨inner, outer⟩)).isSome
      | _, _ => .ok false
  | .at .. | .sample .. | .repeat .. | .choose .. => .ok false

mutual
  /-- Whether a region contains a rewritten operation. -/
  @[expose] def touches (derives : Bool) (table : CalleeTable t.header old new) (definition : Nat)
      (prover verifier : Option Nat) {Γ out : List Located} :
      Region (ProtocolDialect operations functions old deployed) Γ out → Except StepRefusal Bool
    | .ret _ => .ok false
    | .stop _ => .ok false
    | .bind body rest =>
        bothTouch (touches derives table definition prover verifier body)
          (touches derives table definition prover verifier rest)
    | .letOp op _ bodies rest =>
        bothTouch (touchesOp t derives table definition prover verifier op)
          (bothTouch (touchesRegions derives table definition prover verifier bodies)
            (touches derives table definition prover verifier rest))

  @[expose] def touchesRegions (derives : Bool) (table : CalleeTable t.header old new) (definition : Nat)
      (prover verifier : Option Nat) {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions old deployed) signatures →
        Except StepRefusal Bool
    | .nil => .ok false
    | .cons body tail =>
        bothTouch (touches derives table definition prover verifier body)
          (touchesRegions derives table definition prover verifier tail)
end

/-! ## A region that does not change -/

mutual
  /-- A region without a rewritten operation, over the new protocol headers and in a
  context that renames the old one. An `apply` names the callee's image that does not
  thread. -/
  @[expose] def plainRegion (table : CalleeTable t.header old new) {Γ out : List Located} :
      Region (ProtocolDialect operations functions old deployed) Γ out →
        {Δ : List Located} → Renaming Γ Δ →
          Except StepRefusal (Region (ProtocolDialect operations functions new deployed) Δ out)
    | .ret values, _, rename => .ok (.ret (rename.operands values))
    | .stop reason, _, _ => .ok (.stop reason)
    | .bind (mid := mid) body rest, _, rename =>
        match plainRegion table body rename, plainRegion table rest (rename.keepAll mid) with
        | .ok body, .ok rest => .ok (.bind body rest)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
    | .letOp (.at role op bodies) arguments _ rest, _, rename =>
        match plainRegion table rest (rename.keepAll (Located.atRole role op.results)) with
        | .ok rest => .ok (.letOp (.at role op bodies) (rename.operands arguments) .nil rest)
        | .error refusal => .error refusal
    | .letOp (.exchange sender receiver site type) arguments _ rest, _, rename =>
        match plainRegion table rest (rename.keepAll [⟨type, receiver⟩]) with
        | .ok rest =>
            .ok (.letOp (.exchange sender receiver site type) (rename.operands arguments) .nil rest)
        | .error refusal => .error refusal
    | .letOp (.draw owner receivers site (output := output) law populated) arguments _ rest, _, rename =>
        match plainRegion table rest
            (rename.keepAll (⟨output, owner⟩ :: Located.ofRoles output receivers)) with
        | .ok rest =>
            .ok (.letOp (.draw owner receivers site law populated) (rename.operands arguments) .nil rest)
        | .error refusal => .error refusal
    | .letOp (.sample owner site (output := output) law populated) arguments _ rest, _, rename =>
        match plainRegion table rest (rename.keepAll [⟨output, owner⟩]) with
        | .ok rest => .ok (.letOp (.sample owner site law populated) (rename.operands arguments) .nil rest)
        | .error refusal => .error refusal
    | .letOp (.repeat participants count carried collected captures covered) arguments bodies rest,
        _, rename =>
        match plainRegions table bodies,
            plainRegion table rest
              (rename.keepAll (collectedSequencesAt count.size collected ++ carried)) with
        | .ok bodies, .ok rest =>
            .ok (.letOp (.repeat participants count carried collected captures covered)
              (rename.operands arguments) bodies rest)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, _, rename =>
        match plainRegions table bodies, plainRegion table rest (rename.keepAll outputs) with
        | .ok bodies, .ok rest =>
            .ok (.letOp (.choose participants tag captures outputs covered)
              (rename.operands arguments) bodies rest)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments _ rest, _, rename =>
        match table.find callee none,
            plainRegion table rest (rename.keepAll (header.outputs.map (Located.rename roleMap))) with
        | some image, .ok rest =>
            .ok (.letOp (.apply (header := header) image roleMap site permitted)
              (rename.operands arguments) .nil rest)
        | none, _ => .error .image
        | _, .error refusal => .error refusal

  def plainRegions (table : CalleeTable t.header old new)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions old deployed) signatures →
        Except StepRefusal (Regions (ProtocolDialect operations functions new deployed) signatures)
    | .nil => .ok .nil
    | .cons (inputs := inputs) body tail =>
        match plainRegion table body (Renaming.identity inputs), plainRegions table tail with
        | .ok body, .ok tail => .ok (.cons body tail)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
end

/-! ## Threading -/

/-- The context after values that follow two new values, with the renaming and the two
values. A closed region that takes the two before its inputs starts with the renaming of
the empty context. -/
@[expose] def afterTwo (first second : Located) {Γ Δ : List Located} (rename : Renaming Γ Δ)
    (added : List Located) :
    Renaming (bindAll Γ added) (bindAll (second :: first :: Δ) added) ×
      Var (bindAll (second :: first :: Δ) added) first ×
      Var (bindAll (second :: first :: Δ) added) second :=
  (Renaming.keepAll ((rename.weakenOne first).weakenOne second) added,
    (Var.there .here : Var (second :: first :: Δ) first).weaken added,
    (Var.here : Var (second :: first :: Δ) second).weaken added)

/-- A context in which the two values stand after some new values and before others, with
the renaming and the two values: the region of a loop that carries the two takes them
after the iteration numbers, and the results of such a loop have them after the collected
sequences. -/
@[expose] def afterLeading (first second : Located) :
    {Γ Δ : List Located} → Renaming Γ Δ → (leading added : List Located) →
      Renaming (bindAll Γ (leading ++ added))
          (bindAll Δ (leading ++ (first :: second :: added))) ×
        Var (bindAll Δ (leading ++ (first :: second :: added))) first ×
        Var (bindAll Δ (leading ++ (first :: second :: added))) second
  | _, _, rename, [], added => afterTwo first second rename added
  | _, _, rename, located :: rest, added =>
      afterLeading first second (rename.keep located located fun _ same => same.symm) rest added

/-- The image that threads of an applied protocol, with the callee's transcript roles
and the facts that they run as the caller's. -/
structure ThreadedCallee (new : List ProtocolHeader) (roles : TranscriptRoles) (roleMap : RoleMap)
    (header : ProtocolHeader) where
  inner : TranscriptRoles
  prover : roleMap.apply inner.prover = roles.prover
  verifier : roleMap.apply inner.verifier = roles.verifier
  image : Var new (t.header (some inner) header)

/-- The image that threads of a callee, when it has one for the preimages of the two
roles. -/
@[expose] def threadedCallee (table : CalleeTable t.header old new) (roles : TranscriptRoles)
    (roleMap : RoleMap) {header : ProtocolHeader} (callee : Var old header) :
    Option (ThreadedCallee t new roles roleMap header) :=
  match preimage roleMap roles.prover, preimage roleMap roles.verifier with
  | some ⟨prover, isProver⟩, some ⟨verifier, isVerifier⟩ =>
      match table.find callee (some ⟨prover, verifier⟩) with
      | some image => some ⟨⟨prover, verifier⟩, isProver, isVerifier, image⟩
      | none => none
  | _, _ => none

variable (rule : Rule t operations functions)

/-- What an exchange becomes, when it is from the prover to the verifier: the receiver's
value and the two new threaded values. -/
@[expose] def rewrittenExchange (place : Place) (sender receiver site : Nat) (type : Ty)
    {Δ : List Located} (value : Var Δ ⟨type, sender⟩) (first : Var Δ (t.first place.roles))
    (second : Var Δ (t.second place.roles)) :
    Option (Except StepRefusal
      (Emitted (ProtocolDialect operations functions new deployed) Δ
        [⟨type, receiver⟩, t.first place.roles, t.second place.roles])) :=
  if between : sender = place.roles.prover ∧ receiver = place.roles.verifier then
    match rule.exchange place site type (value.retype (by rw [between.1])) first second with
    | .ok emitted =>
        some (.ok { emitted with
          values := .cons ((emitted.values.get .here).retype (by rw [between.2]))
            emitted.values.tail })
    | .error refusal => some (.error refusal)
  else none

/-- What a draw with one receiver becomes, when it is between the transcript roles: the
owner's coin, the receiver's coin and the two new threaded values. -/
@[expose] def rewrittenDraw (place : Place) (owner receiver site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) {Δ : List Located}
    (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles)) :
    Option (Except StepRefusal
      (Emitted (ProtocolDialect operations functions new deployed) Δ
        [⟨output, owner⟩, ⟨output, receiver⟩, t.first place.roles, t.second place.roles])) :=
  if byVerifier : owner = place.roles.verifier ∧ receiver = place.roles.prover then
    match rule.draw place site law first second with
    | .ok emitted =>
        some (.ok { emitted with
          values := .cons ((emitted.values.get (.there .here)).retype (by rw [byVerifier.1]))
            (.cons ((emitted.values.get .here).retype (by rw [byVerifier.2]))
              emitted.values.tail.tail) })
    | .error refusal => some (.error refusal)
  else if byProver : owner = place.roles.prover ∧ receiver = place.roles.verifier then
    match rule.draw place site law first second with
    | .ok emitted =>
        some (.ok { emitted with
          values := .cons ((emitted.values.get .here).retype (by rw [byProver.1]))
            (.cons ((emitted.values.get (.there .here)).retype (by rw [byProver.2]))
              emitted.values.tail.tail) })
    | .error refusal => some (.error refusal)
  else none

mutual
  /-- The rewrite of a region of a definition that threads, in a context that renames
  the old one and holds the two threaded values. -/
  @[expose] def threadRegion (table : CalleeTable t.header old new) (place : Place)
      {Γ out : List Located} :
      Region (ProtocolDialect operations functions old deployed) Γ out →
        {Δ : List Located} → Renaming Γ Δ → Var Δ (t.first place.roles) →
          Var Δ (t.second place.roles) →
            Except StepRefusal (Region (ProtocolDialect operations functions new deployed) Δ
              (t.states place.roles ++ out))
    | .ret values, _, rename, first, second =>
        .ok (.ret (.cons first (.cons second (rename.operands values))))
    | .stop reason, _, _, _, _ => .ok (.stop reason)
    | .bind (mid := mid) body rest, _, rename, first, second =>
        let next := afterTwo (t.first place.roles) (t.second place.roles) rename mid
        match threadRegion table place body rename first second,
            threadRegion table place rest next.1 next.2.1 next.2.2 with
        | .ok body, .ok rest => .ok (.bind body rest)
        | .error refusal, _ => .error refusal
        | _, .error refusal => .error refusal
    | .letOp (.at role op bodies) arguments _ rest, _, rename, first, second =>
        -- The local operation and its nested regions are the old ones: they are typed
        -- over the operation table and the function headers only.
        match threadRegion table place rest (rename.keepAll (Located.atRole role op.results))
            (first.weaken _) (second.weaken _) with
        | .ok rest => .ok (.letOp (.at role op bodies) (rename.operands arguments) .nil rest)
        | .error refusal => .error refusal
    | .letOp (.sample owner site (output := output) law populated) arguments _ rest, _, rename, first,
        second =>
        match threadRegion table place rest (rename.keepAll [⟨output, owner⟩]) first.there
            second.there with
        | .ok rest => .ok (.letOp (.sample owner site law populated) (rename.operands arguments) .nil rest)
        | .error refusal => .error refusal
    | .letOp (.exchange sender receiver site type) arguments _ rest, _, rename, first, second =>
        match rewrittenExchange t rule place sender receiver site type
            (rename.rename (arguments.get .here)) first second with
        | some (.ok emitted) =>
            match threadRegion table place rest
                ((rename.extend emitted.grows).to (emitted.values.get .here))
                (emitted.values.get (.there .here)) (emitted.values.get (.there (.there .here))) with
            | .ok rest => .ok (emitted.wrap rest)
            | .error refusal => .error refusal
        | some (.error refusal) => .error refusal
        | none =>
            match threadRegion table place rest (rename.keepAll [⟨type, receiver⟩]) first.there
                second.there with
            | .ok rest =>
                .ok (.letOp (.exchange sender receiver site type) (rename.operands arguments) .nil
                  rest)
            | .error refusal => .error refusal
    | .letOp (.draw owner [receiver] site (output := output) law populated) arguments _ rest, _, rename,
        first, second =>
        match rewrittenDraw t rule place owner receiver site law first second with
        | some (.ok emitted) =>
            match threadRegion table place rest
                (((rename.extend emitted.grows).to (emitted.values.get .here)).to
                  (emitted.values.get (.there .here)))
                (emitted.values.get (.there (.there .here)))
                (emitted.values.get (.there (.there (.there .here)))) with
            | .ok rest => .ok (emitted.wrap rest)
            | .error refusal => .error refusal
        | some (.error refusal) => .error refusal
        | none =>
            match threadRegion table place rest
                (rename.keepAll [⟨output, owner⟩, ⟨output, receiver⟩]) first.there.there
                second.there.there with
            | .ok rest =>
                .ok (.letOp (.draw owner [receiver] site law populated) (rename.operands arguments) .nil rest)
            | .error refusal => .error refusal
    | .letOp (.draw owner receivers site (output := output) law populated) arguments _ rest, _, rename,
        first, second =>
        match threadRegion table place rest
            (rename.keepAll (⟨output, owner⟩ :: Located.ofRoles output receivers))
            (first.weaken _) (second.weaken _) with
        | .ok rest =>
            .ok (.letOp (.draw owner receivers site law populated) (rename.operands arguments) .nil rest)
        | .error refusal => .error refusal
    | .letOp (.repeat participants count carried collected captures covered) arguments
        bodies rest, _, rename,
        first, second =>
        match touchesRegions t rule.derives table place.definition (some place.roles.prover)
            (some place.roles.verifier) bodies with
        | .ok true =>
            match bodies with
            | .cons body .nil =>
            -- The loop carries the two values before its own carried values, so its
            -- results are the collected sequences, the two values, then the carried
            -- results. Its region takes the two after the iteration numbers and returns
            -- them after the values it collects.
            let next := afterLeading (t.first place.roles) (t.second place.roles) rename
              (collectedSequencesAt count.size collected) carried
            let start := afterLeading (t.first place.roles) (t.second place.roles)
              (Mapping.start (Δ := ([] : List Located)) 0 rfl)
              (Located.ofRoles .nat participants) (carried ++ captures)
            match threadRegion table place body start.1 start.2.1 start.2.2,
                threadRegion table place rest next.1 next.2.1 next.2.2 with
            | .ok body, .ok rest =>
                let parts := Values.split (count.operands participants)
                  (rename.operands arguments)
                .ok (.letOp
                  (.repeat participants count (t.states place.roles ++ carried) collected captures
                    covered)
                  (parts.1.append (.cons first (.cons second parts.2)))
                  (.cons
                    (Region.returnAfter (dialect := ProtocolDialect operations functions new deployed)
                      (t.states place.roles) collected body) .nil) rest)
            | .error refusal, _ => .error refusal
            | _, .error refusal => .error refusal
        | .ok false =>
            match plainRegions t table bodies,
                threadRegion table place rest
                  (rename.keepAll (collectedSequencesAt count.size collected ++ carried))
                  (first.weaken _) (second.weaken _) with
            | .ok bodies, .ok rest =>
                .ok (.letOp (.repeat participants count carried collected captures covered)
                  (rename.operands arguments) bodies rest)
            | .error refusal, _ => .error refusal
            | _, .error refusal => .error refusal
        | .error refusal => .error refusal
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, _, rename,
        first, second =>
        match touchesRegions t rule.derives table place.definition (some place.roles.prover)
            (some place.roles.verifier) bodies with
        | .ok true =>
            -- Every arm captures and returns the two values, also an arm that leaves them
            -- as they are.
            if held : Located.heldBy participants (t.states place.roles ++ outputs) = true then
              let next := afterTwo (t.first place.roles) (t.second place.roles) rename outputs
              match threadRegions table place bodies
                    (t.choice place.roles participants captures outputs tag),
                  threadRegion table place rest next.1 next.2.1 next.2.2 with
              | .ok bodies, .ok rest =>
                  let parts := Values.split (Located.ofRoles tag.type participants)
                    (rename.operands arguments)
                  .ok (.letOp
                    (.choose participants tag (t.states place.roles ++ captures)
                      (t.states place.roles ++ outputs) held)
                    (parts.1.append (.cons first (.cons second parts.2)))
                    bodies rest)
              | .error refusal, _ => .error refusal
              | _, .error refusal => .error refusal
            else .error .image
        | .ok false =>
            match plainRegions t table bodies,
                threadRegion table place rest (rename.keepAll outputs) (first.weaken outputs)
                  (second.weaken outputs) with
            | .ok bodies, .ok rest =>
                .ok (.letOp (.choose participants tag captures outputs covered)
                  (rename.operands arguments) bodies rest)
            | .error refusal, _ => .error refusal
            | _, .error refusal => .error refusal
        | .error refusal => .error refusal
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments _ rest, _, rename,
        first, second =>
        match threadedCallee t table place.roles roleMap callee with
        | some callee =>
            -- The callee's image takes the two values, held by the callee roles that run
            -- as the caller's prover and verifier, and returns the new ones.
            let next := afterTwo (Located.rename roleMap (t.first callee.inner))
              (Located.rename roleMap (t.second callee.inner)) rename
              (header.outputs.map (Located.rename roleMap))
            match threadRegion table place rest next.1
                (next.2.1.retype (congrArg (Located.mk t.prover) callee.prover))
                (next.2.2.retype (congrArg (Located.mk t.verifier) callee.verifier)) with
            | .ok rest =>
                .ok (.letOp (.apply callee.image roleMap site permitted)
                  (.cons (first.retype (congrArg (Located.mk t.prover) callee.prover.symm))
                    (.cons (second.retype (congrArg (Located.mk t.verifier) callee.verifier.symm))
                      (rename.operands arguments))) .nil rest)
            | .error refusal => .error refusal
        | none =>
            match table.find callee none,
                threadRegion table place rest
                  (rename.keepAll (header.outputs.map (Located.rename roleMap))) (first.weaken _)
                  (second.weaken _) with
            | some image, .ok rest =>
                .ok (.letOp (.apply (header := header) image roleMap site permitted)
                  (rename.operands arguments) .nil rest)
            | none, _ => .error .image
            | _, .error refusal => .error refusal

  /-- Nested regions take the two threaded values among their inputs, after the values
  that lead them, and return them before their outputs. -/
  def threadRegions (table : CalleeTable t.header old new) (place : Place)
      {signatures targets : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions old deployed) signatures →
        ThreadedRegions t place.roles signatures targets →
          Except StepRefusal (Regions (ProtocolDialect operations functions new deployed) targets)
    | regions, threads =>
        match threads, regions with
        | .nil, .nil => .ok .nil
        | .cons leading added threads, .cons body tail =>
            let start := afterLeading (t.first place.roles) (t.second place.roles)
              (Mapping.start (Δ := ([] : List Located)) 0 rfl) leading added
            match threadRegion table place body start.1 start.2.1 start.2.2,
                threadRegions table place tail threads with
            | .ok body, .ok tail => .ok (.cons body tail)
            | .error refusal, _ => .error refusal
            | _, .error refusal => .error refusal
end

end Step

end Zkc.Core
