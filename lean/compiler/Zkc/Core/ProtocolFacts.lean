module

public import Zkc.Core.Facts

public section

/-! The check of facts over a protocol body.

A value of a protocol body has one holder, and a role computes on the values it holds. What
is known is therefore kept role by role: for each role, the facts of the local check about
the values of the body, of which only the role's own operations say anything. A fact of one
role never reaches another: a value that a role receives has what its type gives and
nothing more, whatever the sender knew of it.

What the protocol operations give:

- `at(r, ℓ)`: the rules of the local operation `ℓ` on what `r` knows: its requirement, the
  shapes and intervals of its results, the facts of a `guard`, and the facts at the start
  of its nested regions;
- `exchange`, `draw`, `sample`, `apply`, and the results of a `repeat`: new values of which
  nothing is known;
- `choose` on a condition: in the region of `false` each participant knows its own copy of
  the condition taken false, in the region of `true` taken true; on an arm number or a
  variant nothing is added;
- the results of a `choose` and of a block: the holder of a `nat` result knows the smaller
  `lo` and the larger `hi` of what it knows of that result where the regions return, as for
  the results of an `if`;
- `repeat`: each participant knows the interval of its iteration number, `0 .. n - 1` for
  the count `n` of the operation and `0 .. hi(count) - 1` for a count that is a value, and
  in the second case, when the region captures the participant's own copy of the count,
  the order of the iteration number below it; nothing is known of the carried values in
  the region; the region of a `repeat` over the count 0 of the operation never runs, and
  nothing in it needs a justification;
- a nested region: each role keeps the facts all of whose values are captured;
- a value of a type without a value: the role that holds it never runs past the place
  where the value is bound, and none of its applications there needs a justification. The
  place is the inputs of the protocol, the inputs of a nested region, the results of an
  instruction or the results of a block. The other roles run: a side without the holder
  has no value there, and their applications are checked as before.

The path of an application that is not justified numbers the instructions of the body and
of its nested regions as the local check does; the regions of a local operation inside an
`at` are numbered under the instruction of the `at`.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- What is known of the values of a protocol body at one instruction, role by role. Each
role that has computed has its own facts about the values of the body; of a role that is
not listed nothing is known. `depth` is the number of values, and `dead` marks a region
that never runs for any role. A region that never runs for one role, the holder of a
value of a type without a value, is marked in the facts of that role. -/
structure RoleFacts where
  depth : Nat
  roles : List (Nat × Facts)
  dead : Bool
  deriving Repr, Inhabited

namespace RoleFacts

/-- Nothing known of `count` values by any role. -/
@[expose] def start (count : Nat) : RoleFacts := ⟨count, [], false⟩

/-- The facts listed for a role. -/
@[expose] def find (role : Nat) : List (Nat × Facts) → Option Facts
  | [] => none
  | entry :: rest => if entry.1 = role then some entry.2 else find role rest

/-- The facts of a role in place of the ones listed for it, or listed for it first. -/
@[expose] def put (role : Nat) (facts : Facts) : List (Nat × Facts) → List (Nat × Facts)
  | [] => [(role, facts)]
  | entry :: rest => if entry.1 = role then (role, facts) :: rest else entry :: put role facts rest

/-- What a role knows: the facts listed for it, or nothing. -/
@[expose] def view (state : RoleFacts) (role : Nat) : Facts :=
  match find role state.roles with
  | some facts => facts
  | none => cond state.dead (Facts.start state.depth).kill (Facts.start state.depth)

/-- One role knows something else. -/
@[expose] def set (state : RoleFacts) (role : Nat) (facts : Facts) : RoleFacts :=
  { state with roles := put role facts state.roles }

/-- Every role's facts changed in one way, over a context of `depth` values. -/
@[expose] def each (state : RoleFacts) (depth : Nat) (change : Facts → Facts) : RoleFacts :=
  ⟨depth, state.roles.map fun entry => (entry.1, change entry.2), state.dead⟩

/-- `count` new values of which no role knows anything. -/
@[expose] def bind (state : RoleFacts) (count : Nat) : RoleFacts :=
  state.each (state.depth + count) fun facts => facts.after (List.replicate count .other) []

/-- What each role knows at the start of a nested region: the facts all of whose values
are captured. -/
@[expose] def enter (state : RoleFacts) (sources : List (Option Nat)) : RoleFacts :=
  state.each sources.length fun facts => facts.enter sources

/-- The facts of a region that never runs. -/
@[expose] def kill (state : RoleFacts) : RoleFacts :=
  ⟨state.depth, state.roles.map fun entry => (entry.1, entry.2.kill), true⟩

/-- What the roles know with values of the given located types in scope: the holder of a
value of a type without a value never runs. -/
@[expose] def inScope (state : RoleFacts) : List Located → RoleFacts
  | [] => state
  | located :: rest =>
      inScope
        (cond located.type.populated state
          (state.set located.holder (state.view located.holder).kill)) rest

/-- Each participant of a `choose` on a condition knows its own copy of the condition,
taken with the given truth. The copies are listed in the order of the participants. -/
@[expose] def assumeTags (truth : Bool) : List Nat → List Nat → RoleFacts → RoleFacts
  | role :: participants, tag :: tags, state =>
      assumeTags truth participants tags
        (state.set role ((state.view role).assume state.depth tag truth))
  | _, _, state => state

/-- What the roles know of the values that a region returns: of each value, the interval
that its holder knows. -/
@[expose] def returned (state : RoleFacts) (depth : Nat) {Γ : List Located} :
    {out : List Located} → Operands Γ out → List Returned
  | _, .nil => []
  | _, .cons (ty := located) reference rest =>
      ⟨(state.view located.holder).interval (Scope.number depth reference), []⟩ ::
        returned state depth rest

/-- Each holder of a `nat` result knows the interval of that result. The results are the
values from `level` on, with the intervals that the regions return for them. -/
@[expose] def withResults : (level : Nat) → List Located → List Interval → RoleFacts → RoleFacts
  | level, located :: outputs, interval :: intervals, state =>
      withResults (level + 1) outputs intervals
        (match located.type with
          | .nat =>
              state.set located.holder
                ((state.view located.holder).bound level interval.lo interval.hi)
          | _ => state)
  | _, _, _, state => state

end RoleFacts

/-- What a participant of a `repeat` knows of its iteration number, the value at `level`:
it is at most `hi`, and below the participant's count when the region captures it. -/
@[expose] def Facts.iteration (facts : Facts) (level : Nat) (hi : Option Nat) : Option Nat → Facts
  | some captured => (facts.bound level 0 hi).order true level captured
  | none => facts.bound level 0 hi

namespace RoleFacts

/-- Each participant of a `repeat` over the count `count` of the operation knows the
interval of its iteration number. The iteration numbers are the first inputs of the
region, in the order of the participants, from `level` on. -/
@[expose] def countStatic (count : Nat) : (level : Nat) → List Nat → RoleFacts → RoleFacts
  | _, [], state => state
  | level, role :: participants, state =>
      countStatic count (level + 1) participants
        (state.set role ((state.view role).iteration level (some (count - 1)) none))

/-- Each participant of a `repeat` over a count that is a value knows the interval of its
iteration number, from what it knows of its own copy of the count outside the region, and
the order of the iteration number below that copy when the region captures it. `counts`
are the copies, in the order of the participants. -/
@[expose] def countRuntime (outer : RoleFacts) (sources : List (Option Nat)) :
    (level : Nat) → List Nat → List Nat → RoleFacts → RoleFacts
  | level, role :: participants, count :: counts, state =>
      countRuntime outer sources (level + 1) participants counts
        (state.set role
          ((state.view role).iteration level (Facts.before ((outer.view role).hi count))
            (Facts.sourceOf count sources 0)))
  | _, _, _, state => state

end RoleFacts

/-! ## A local operation of one role

`at(r, ℓ)` is checked against what `r` knows, in three parts: the requirement of `ℓ`, the
facts at the start of each nested region of `ℓ`, and what the roles know after it. Each
part is a function of the role, the operation and the levels of its operands, and none
reads the nested regions. -/

section Role

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

namespace RoleFacts

/-- Each participant of a `repeat` knows its copy of the count to be within a maximum; a
participant whose region never runs needs nothing. `counts` are the levels of the copies, in
the order of the participants (the first operands of the instruction). -/
@[expose] def countsWithin (state : RoleFacts) (maximum : Nat) : List Nat → List Nat → Bool
  | role :: participants, count :: counts =>
      ((state.view role).dead || within ((state.view role).hi count) maximum) &&
        countsWithin state maximum participants counts
  | _, _ => true

/-- The requirement that the local operation of a role does not meet, against what the role
knows; none when it is justified, and none in a region that never runs, for any role or
for this one. -/
@[expose] def unjustifiedLocal (state : RoleFacts) (role : Nat)
    (op : LocalOp operations functions deployed) (levels : List Nat) : Option Requirement :=
  cond (state.dead || (state.view role).dead) none
    (LocalOp.unjustified (state.view role) op levels)

/-- The facts at the start of the nested region with the number `number` of the local
operation of a role: what the operation gives the region from what the role knows. -/
@[expose] def localRegionFacts (state : RoleFacts) (role : Nat)
    (op : LocalOp operations functions deployed) (levels : List Nat) (number : Nat) : Facts :=
  LocalOp.regionFacts (state.view role) op levels number

/-- What the roles know after the local operation of a role, from what its nested regions
return: the results are new values; the role knows what the operation gives of them, or
the facts of its condition for a `guard`, with `shape` in place of the shape of the first
result when there is one (`LocalOp.branchShape`); no other role knows anything of them. -/
@[expose] def afterLocal (state : RoleFacts) (role : Nat)
    (op : LocalOp operations functions deployed) (levels : List Nat) (outcomes : List Outcome)
    (shape : Option Shape) : RoleFacts :=
  (state.bind op.results.length).set role
    ((LocalOp.factsAfter (state.view role) op levels outcomes).reshape state.depth shape)

end RoleFacts

end Role

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

namespace ProtocolOp

/-- The check of one instruction on the levels of its operands: the first application in
it that is not justified, or what the roles know after it. `path` is where the
instruction is.

- `at(r, ℓ)`: the requirement of `ℓ` against what `r` knows (`RoleFacts.unjustifiedLocal`),
  then the nested regions of `ℓ`, each from the facts that `ℓ` gives it
  (`RoleFacts.localRegionFacts`); afterwards `r` knows what `ℓ` gives of its results, or
  the facts of its condition for a `guard`, and no other role knows anything of the
  results (`RoleFacts.afterLocal`).
- `repeat` with a count that is a value: each participant knows its copy of the count to be
  within the maximum (`RoleFacts.countsWithin`). A count above the maximum is outside the
  domain of the operation.
- Every other instruction: its results are new values of which no role knows anything,
  until `joined` adds what the regions of a `choose` return. -/
@[expose] def justify (path : List Nat) (state : RoleFacts) :
    ProtocolOp operations functions protocols deployed → List Nat → Except Unjustified RoleFacts
  | .at role op bodies, levels =>
      match state.unjustifiedLocal role op levels with
      | some requirement => .error ⟨path, requirement⟩
      | none =>
          match justifyRegions path (state.localRegionFacts role op levels) 0 bodies with
          | .error unjustified => .error unjustified
          | .ok outcomes =>
              .ok (state.afterLocal role op levels outcomes (LocalOp.branchShape op levels bodies))
  | .repeat participants (.runtime maximum) carried collected captures covered, levels =>
      cond (state.dead || state.countsWithin maximum participants levels)
        (.ok (state.bind
          (ProtocolOp.repeat (operations := operations) (functions := functions)
            (protocols := protocols) (deployed := deployed) participants (.runtime maximum) carried
            collected captures covered).results.length))
        (.error ⟨path, .maximum⟩)
  | op, _ => .ok (state.bind op.results.length)

/-- What an instruction gives the roles at the start of the nested region with the number
`number`, from what they know at the instruction.

- `choose` on a condition: each participant knows its own copy of the condition, taken
  false in the first region and true in the second; then the captures.
- `choose` on an arm number: the captures. On a variant: the captures; nothing is known of
  the payloads.
- `repeat`: the captures; each participant knows the interval of its iteration number,
  and nothing is known of the carried values. A count of the operation gives
  `0 .. n - 1`; a count that is a value gives each participant `0 .. hi(count) - 1` for its
  own copy and, when the region captures that copy, the order of the iteration number
  below it. The region of a `repeat` over the count 0 of the operation never runs. -/
@[expose] def regionEntry (state : RoleFacts) :
    ProtocolOp operations functions protocols deployed → List Nat → Nat → RoleFacts
  | .choose participants .condition _ _ _, levels, number =>
      (RoleFacts.assumeTags (decide (number = 1)) participants levels state).enter
        ((levels.drop participants.length).map some)
  | .choose participants (.arm _) _ _ _, levels, _ =>
      state.enter ((levels.drop participants.length).map some)
  | .choose participants (.alternative ..) _ _ _, levels, _ =>
      state.enter (List.replicate participants.length none ++
        (levels.drop participants.length).map some)
  | .repeat participants (.static count) carried _ _ _, levels, _ =>
      cond (decide (count = 0))
        (RoleFacts.countStatic count 0 participants
          (state.enter (List.replicate (participants.length + carried.length) none ++
            (levels.drop carried.length).map some))).kill
        (RoleFacts.countStatic count 0 participants
          (state.enter (List.replicate (participants.length + carried.length) none ++
            (levels.drop carried.length).map some)))
  | .repeat participants (.runtime _) carried _ _ _, levels, _ =>
      let sources := List.replicate (participants.length + carried.length) none ++
        ((levels.drop participants.length).drop carried.length).map some
      RoleFacts.countRuntime state sources 0 participants levels (state.enter sources)
  | _, _, _ => state

/-- The located types of the inputs of the nested region with the number `number`; none
when the instruction has no such region. -/
@[expose] def regionInputs (op : ProtocolOp operations functions protocols deployed)
    (number : Nat) : List Located :=
  match op.regions[number]? with
  | some signature => signature.1
  | none => []

/-- What the roles know at the start of the nested region with the number `number`: what
the instruction gives them (`regionEntry`), with the inputs of the region in scope. A
participant of a `choose` on a variant never runs the region of an alternative whose
payload has a type without a value. -/
@[expose] def regionState (state : RoleFacts)
    (op : ProtocolOp operations functions protocols deployed) (levels : List Nat)
    (number : Nat) : RoleFacts :=
  (op.regionEntry state levels number).inScope (op.regionInputs number)

/-- What the roles know of the results of an instruction from what its nested regions
return, after the results are bound from `level` on: each holder of a `nat` result of a
`choose` knows the smaller `lo` and the larger `hi` of the regions that return. -/
@[expose] def joined (level : Nat) :
    ProtocolOp operations functions protocols deployed → List Outcome → RoleFacts → RoleFacts
  | .choose _ _ _ outputs _, outcomes, state =>
      state.withResults level outputs (Outcome.joinAll outcomes).intervals
  | _, _, state => state

end ProtocolOp

mutual
  /-- The check of a region of a protocol body from what the roles know at its start: the
  first application that is not justified, or what the region returns. `path` and `index`
  say where the region's next instruction is. -/
  @[expose] def justifyProtocol (path : List Nat) (index : Nat) (state : RoleFacts)
      {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out →
        Except Unjustified Outcome
    | .ret values => .ok (some (state.returned state.depth values))
    | .stop reason =>
        if reason = .undefined then .error ⟨path ++ [index], .reservedStop⟩ else .ok none
    | .letOp op arguments bodies next =>
        match ProtocolOp.justify (path ++ [index]) state op
            (Scope.numbers state.depth arguments) with
        | .error unjustified => .error unjustified
        | .ok after =>
            match justifyProtocols (path ++ [index])
                (ProtocolOp.regionState state op (Scope.numbers state.depth arguments)) 0
                bodies with
            | .error unjustified => .error unjustified
            | .ok outcomes =>
                justifyProtocol path (index + 1)
                  ((ProtocolOp.joined state.depth op outcomes after).inScope op.results) next
    | .bind (mid := mid) body next =>
        match justifyProtocol (path ++ [index]) 0 state body with
        | .error unjustified => .error unjustified
        | .ok outcome =>
            justifyProtocol path (index + 1)
              (((state.bind mid.length).withResults state.depth mid outcome.intervals).inScope
                mid) next

  /-- The check of the nested regions of a protocol instruction, each from what the roles
  know at its start. -/
  @[expose] def justifyProtocols (path : List Nat) (stateOf : Nat → RoleFacts) (number : Nat)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures →
        Except Unjustified (List Outcome)
    | .nil => .ok []
    | .cons body tail =>
        match justifyProtocol (path ++ [number]) 0 (stateOf number) body with
        | .error unjustified => .error unjustified
        | .ok outcome =>
            match justifyProtocols path stateOf (number + 1) tail with
            | .error unjustified => .error unjustified
            | .ok outcomes => .ok (outcome :: outcomes)
end

end Protocol

/-! ## Definitions and programs -/

/-- The first application of a protocol's body that is not justified; none when the
protocol passes the check of facts. Nothing is known of the inputs but that they are in
scope. -/
@[expose] def ProtocolDefinition.unjustified {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader} {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) : Option Unjustified :=
  match justifyProtocol [] 0 ((RoleFacts.start header.inputs.length).inScope header.inputs)
      definition.body with
  | .error unjustified => some unjustified
  | .ok _ => none

/-- A protocol passes the check of facts. -/
@[expose] def ProtocolDefinition.justified {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader} {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) : Bool :=
  definition.unjustified.isNone

/-- Every protocol passes the check of facts. -/
@[expose] def Protocols.justified {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols → Bool
  | _, .nil => true
  | _, .snoc earlier definition _ => earlier.justified && definition.justified

/-- The protocols that do not pass, by their numbers in program order, each with its first
application that is not justified. -/
@[expose] def Protocols.unjustified {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      List (Nat × Unjustified)
  | _, .nil => []
  | _, .snoc (protocols := protocols) earlier definition _ =>
      earlier.unjustified ++
        match definition.unjustified with
        | some unjustified => [(protocols.length, unjustified)]
        | none => []

/-- Every function and every protocol of a program passes the check of facts. -/
@[expose] def Program.justified {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    (program : Program typeTable operations functions protocols) : Bool :=
  program.functions.justified && program.protocols.justified

end Zkc.Core
