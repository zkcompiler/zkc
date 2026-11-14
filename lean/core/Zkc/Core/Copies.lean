module

public import Zkc.Core.Unelaborate
public import Zkc.Core.Meaning

public section

/-! The check of copies: values that several roles hold are one value where the program needs
them to be.

A `choose` and a `repeat` stop `incomplete` when the copies of the tag, or of the count, that
the participants in the side hold differ. An application assumes the agreements of the
callee's inputs, and an output agreement is a promise to callers and to the statement of a
scheme. The check walks a protocol body and gives every value a *class* and a *support*.

- Values of one class are copies of one value. The copies of an input agreement are one
  class. An exchange gives the receiver's result the class of the value sent. The copies of a
  draw are one class. The results of `at(r, ℓ)` have the classes named by `ℓ` as code (its
  regions included) and the classes of its operands: two roles that perform the same code on
  copies of the same values get copies of the same results. The results of an application
  are classed by the callee's output agreements. The outputs of a `choose` are one class when
  the values returned are one class in every arm, and each a class of its own when no arm
  returns: nothing then says that two outputs are one value. The values carried by a `repeat`
  have the coarsest partition that the body keeps, found by refining the partition of the
  values before the first iteration; the collections are one class when the values collected
  are; the iteration numbers are one class.
- The support of a value is the set of roles that must be in a side for the value to be the
  value of its class there. It contains the holder. An input has its holder; the result of an
  exchange has the support of the value sent and the receiver; a draw gives the owner its own
  role and a receiver the owner and its own; a local operation gives the supports of its
  operands and the role; a result of an application has its holder.
- A *requirement* is a list of copies that must be one value: the tags of a `choose`, the
  counts of a `repeat`, the operands at an input agreement of a callee, the copies of an
  output agreement. The check refuses a requirement whose copies are not one class.

What the check returns for a protocol is its requirements, each copy with its role and its
support, the requirements of the protocols it applies included. A side *supports* them when,
for every requirement of which it has two or more copies, it contains the support of each of
those copies.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

deriving instance DecidableEq for Raw.LocalStep, Raw.LocalRegion, Raw.LocalArms

namespace Copies

/-- Copies that must be one value: each with the role that holds it and its support. -/
abbrev Requirement := List (Nat × List Nat)

/-- What of the check of copies a body does not meet. -/
inductive Unmet where
  /-- The tags of a `choose` are not copies of one value. -/
  | tags
  /-- The counts of a `repeat` are not copies of one value. -/
  | counts
  /-- The operands at an input agreement of a callee are not copies of one value. -/
  | operands
  /-- The copies of an output agreement are not copies of one value. -/
  | outputs
  /-- The values carried by a `repeat` did not settle: a defect of the check. -/
  | unsettled
  deriving Repr, Inhabited, DecidableEq

/-- A requirement that is not met, and the path of its instruction (in the numbering of the
check of facts); an output agreement has the path after the last instruction. -/
structure Refusal where
  path : List Nat
  unmet : Unmet
  deriving Repr, Inhabited, DecidableEq

/-- A value as the check knows it: its class and its support. -/
structure Copy where
  class_ : Nat
  support : List Nat
  deriving Repr, Inhabited, DecidableEq

/-- What is known at a point of a body: each value in scope by level, the next class that no
value has, and the local operations already made, by their code on classes of operands, with
the classes of their results. -/
structure State where
  values : List Copy
  next : Nat
  made : List (Raw.LocalStep × List Nat)
  deriving Inhabited

/-- A support with one more role. -/
@[expose] def withRole (support : List Nat) (role : Nat) : List Nat :=
  cond (support.contains role) support (role :: support)

/-- The union of two supports. -/
@[expose] def union (first second : List Nat) : List Nat :=
  second.foldl withRole first

/-- The same roles, in any order. -/
@[expose] def sameRoles (first second : List Nat) : Bool :=
  first.all second.contains && second.all first.contains

namespace State

/-- The value at a level. -/
@[expose] def at_ (state : State) (level : Nat) : Copy := state.values.getD level default

/-- The state with new values, the last the most recent. -/
@[expose] def push (state : State) (copies : List Copy) : State :=
  { state with values := state.values ++ copies }

/-- The classes from the next one on, as many as asked, and the state after them. -/
@[expose] def fresh (state : State) (count : Nat) : List Nat × State :=
  ((List.range count).map (state.next + ·), { state with next := state.next + count })

end State

/-- Whether copies are one class. -/
@[expose] def oneClass : List Copy → Bool
  | [] => true
  | first :: rest => rest.all fun copy => Nat.beq copy.class_ first.class_

/-- The classes of results of a local operation: those of an earlier operation with the same
code on the same classes and as many results, or new ones. -/
@[expose] def numbered (state : State) (key : Raw.LocalStep) (count : Nat) : List Nat × State :=
  match state.made.find? fun entry => decide (entry.1 = key) && decide (entry.2.length = count) with
  | some entry => (entry.2, state)
  | none =>
      let (classes, state) := state.fresh count
      (classes, { state with made := (key, classes) :: state.made })

/-- One step of `blocks`, on the keys seen with their classes, the classes given so far and
the next class: the class of a key seen before, or the next class. -/
@[expose] def blockStep (found : List (List Nat × Nat) × List Nat × Nat) (key : List Nat) :
    List (List Nat × Nat) × List Nat × Nat :=
  match found.1.find? fun entry => entry.1 == key with
  | some entry => (found.1, found.2.1 ++ [entry.2], found.2.2)
  | none => ((key, found.2.2) :: found.1, found.2.1 ++ [found.2.2], found.2.2 + 1)

/-- One class per block of a partition given by keys: values with equal keys get one new
class. -/
@[expose] def blocks (state : State) (keys : List (List Nat)) : List Nat × State :=
  let found := keys.foldl blockStep ([], [], state.next)
  (found.2.1, { state with next := found.2.2 })

/-- The requirements of a callee, in the roles of the caller. -/
@[expose] def mapped (roleMap : RoleMap) (requirements : List Requirement) : List Requirement :=
  requirements.map fun requirement =>
    requirement.map fun (role, support) => (roleMap.apply role, support.map roleMap.apply)

/-- What a region returns: a copy per output, or nothing when it stops; with the next class,
the local operations made up to its end, and the requirements found in it. -/
structure Returned where
  copies : Option (List Copy)
  next : Nat
  made : List (Raw.LocalStep × List Nat)
  requirements : List Requirement
  deriving Inhabited

/-! ### The outputs of a choice -/

/-- What the arms of a choice start with besides the captures: for a variant, the payload of
each participant, all of one class, each with the support of the participant's tag. -/
@[expose] def choiceOwn (tag : ChoiceTag) (payload : Nat) (tags : List Copy) : List Copy :=
  match tag with
  | .alternative .. => tags.map fun copy => ⟨payload, copy.support⟩
  | _ => []

/-- The keys of the outputs of a choice: for each output, the classes that the arms return at
its position; its position when no arm returns, since nothing then says that two outputs are
one value. -/
@[expose] def choiceKeys (returning : List (List Copy)) (count : Nat) : List (List Nat) :=
  (List.range count).map fun position =>
    match returning with
    | [] => [position]
    | _ :: _ => returning.map fun copies => (copies.getD position default).class_

/-- The class of an output of a choice: the class that every arm returns at its position, when
it is one class, so that a value passed around the choice is that value; the class of its key
otherwise. -/
@[expose] def choiceClass (class_ : Nat) (key : List Nat) : Nat :=
  match key with
  | first :: rest => cond (rest.all (Nat.beq · first)) first class_
  | [] => class_

/-- The classes of the outputs of a choice, from the classes of their keys. -/
@[expose] def choiceClasses (returning : List (List Copy)) (made : List Nat)
    (keys : List (List Nat)) : List Nat :=
  match returning with
  | [] => made
  | _ :: _ => (made.zip keys).map fun entry => choiceClass entry.1 entry.2

/-- The support of an output of a choice: its holder and the supports of what the arms return
at its position. -/
@[expose] def choiceSupport (returning : List (List Copy)) (holder position : Nat) : List Nat :=
  returning.foldl (init := [holder]) fun support copies =>
    union support (copies.getD position default).support

/-- The copies of the outputs of a choice. -/
@[expose] def choiceResults (returning : List (List Copy)) (classes : List Nat)
    (outputs : List Located) : List Copy :=
  ((classes.zip outputs).zip (List.range outputs.length)).map fun entry =>
    ⟨entry.1.1, choiceSupport returning entry.1.2.holder entry.2⟩

/-- The state after a choice whose arms return `returning` and leave `next` as the next
class: the outputs are one class when the values returned are one class in every arm. What
the arms made is not kept: an arm may not have run. -/
@[expose] def afterChoice (state : State) (next : Nat) (returning : List (List Copy))
    (outputs : List Located) : State :=
  let found := blocks { state with next := next } (choiceKeys returning outputs.length)
  found.2.push (choiceResults returning
    (choiceClasses returning found.1 (choiceKeys returning outputs.length)) outputs)

/-! ### The values that a loop carries -/

/-- The copies of the counts of a loop, one per participant when the count is a value, and
the operands after them. -/
@[expose] def loopOperands (count : RepeatCount) (participants : Nat) (operands : List Copy) :
    List Copy × List Copy :=
  match count with
  | .runtime _ => (operands.take participants, operands.drop participants)
  | .static _ => ([], operands)

/-- What the body of a loop starts with besides the captures: the iteration number of each
participant, all of one class, and the carried values with the classes and supports at
hand. -/
@[expose] def loopOwn (participants : List Nat) (number : Nat) (classes : List Nat)
    (supports : List (List Nat)) : List Copy :=
  participants.map (fun role => ⟨number, [role]⟩) ++
    (classes.zip supports).map fun entry => ⟨entry.1, entry.2⟩

/-- The partition of the carried values of a loop that its body keeps, and their supports,
found by refining the partition given by `keys` and widening `supports` until the body
returns the carried values in the classes and with the supports that they entered with.
`check` is the check of the body from a state. It returns what the body collects, each
carried value with whether the body returns it as it entered (then every iteration leaves
it as it was), the next class and the requirements found. Without fuel left it refuses. -/
@[expose] def settle (state : State) (participants : List Nat) (collected : Nat)
    (captured : List Copy) (unsettled : Refusal)
    (check : State → Except Refusal (List (Option (List Copy)) × Nat × List Requirement)) :
    Nat → List (List Nat) → List (List Nat) →
      Except Refusal (List Copy × List (Copy × Bool) × Nat × List Requirement)
  | 0, _, _ => .error unsettled
  | fuel + 1, keys, supports =>
      let numbered : State := { state with next := state.next + 1 }
      let found := blocks numbered keys
      match check { found.2 with
          values := loopOwn participants state.next found.1 supports ++ captured } with
      | .error refusal => .error refusal
      | .ok (bodies, next, inner) =>
          match bodies.headD none with
          | none =>
              -- a region of a protocol body does not stop: kept for totality
              .ok ([], (found.1.zip supports).map fun entry => (⟨entry.1, entry.2⟩, false),
                next, inner)
          | some returned =>
              let after := returned.drop collected
              let refined := (keys.zip after).map fun entry => entry.1 ++ [entry.2.class_]
              let widened := (supports.zip after).map fun entry => union entry.1 entry.2.support
              -- the same classes from the same start: the same partition
              if (blocks numbered refined).1 == found.1 &&
                  (supports.zip widened).all (fun entry => sameRoles entry.1 entry.2) then
                .ok (returned.take collected, ((found.1.zip supports).zip after).map
                  fun entry => (⟨entry.1.1, entry.1.2⟩, Nat.beq entry.2.class_ entry.1.1),
                  next, inner)
              else settle state participants collected captured unsettled check fuel refined
                widened

/-- The key of the collection at a position: the class of what the body collects there, and
the position of the first collected entry of its type, so that collections of one class have
one type also when no iteration runs; its own position when the body collects nothing. -/
@[expose] def collectionKey (gathered : List Copy) (collected : List Located) (position : Nat) :
    List Nat :=
  [(gathered.getD position ⟨position, []⟩).class_, cond gathered.isEmpty (position + 1) 0,
    collected.findIdx fun other => decide (other.type = (collected.getD position default).type)]

/-- The copies of the results of a loop: a collection has the class of its key and the support
of what the body collects there, with its holder; a carried value that no iteration changes
has the class of the value before the loop, and another the class of its settled class, each
with the support that it enters the body with. -/
@[expose] def loopResults (collections finals : List Nat) (gathered : List Copy)
    (kept : List (Copy × Bool)) (initial : List Copy) (collected : List Located) : List Copy :=
  ((collections.zip collected).zip (List.range collected.length)).map
      (fun entry =>
        (⟨entry.1.1, withRole (gathered.getD entry.2 default).support entry.1.2.holder⟩ : Copy)) ++
    ((finals.zip kept).zip initial).map fun entry =>
      ⟨cond entry.1.2.2 entry.2.class_ entry.1.1, entry.1.2.1.support⟩

/-- The state after a loop whose body collects `gathered` and keeps the carried values as
`kept`: the collections are one class when the values collected are, and a carried value that
no iteration changes is the value before the loop. -/
@[expose] def afterLoop (state : State) (next : Nat) (gathered : List Copy)
    (kept : List (Copy × Bool)) (initial : List Copy) (collected : List Located) : State :=
  let collections := blocks { state with next := next }
    ((List.range collected.length).map (collectionKey gathered collected))
  let finals := blocks collections.2 (kept.map fun entry => [entry.1.class_])
  finals.2.push (loopResults collections.1 finals.1 gathered kept initial collected)

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The copies of an agreement among the values at given levels, each with its role. -/
@[expose] def agreed {ports : List Located} (rename : Nat → Nat) (copies : List Copy)
    (agreement : Agreement ports) : Requirement × List Copy :=
  let found := agreement.copies.map fun copy =>
    (rename copy.holder, copies.getD copy.port.index default)
  (found.map fun (role, copy) => (role, copy.support), found.map (·.2))

/-- The key of a port under agreements: the number of the first agreement that has a copy at
the port, or the port's own position. -/
@[expose] def portKey {ports : List Located} (agreements : List (Agreement ports))
    (position : Nat) : List Nat :=
  match (agreements.zip (List.range agreements.length)).find? fun entry =>
      entry.1.copies.any fun copy => Nat.beq copy.port.index position with
  | some entry => [0, entry.2]
  | none => [1, position]

/-- The classes of ports under agreements: the copies of an agreement are one class, and every
other port a class of its own. -/
@[expose] def portClasses {ports : List Located} (state : State)
    (agreements : List (Agreement ports)) : List Nat × State :=
  blocks state ((List.range ports.length).map (portKey agreements))

mutual
  /-- The check of a region of a protocol body. `summaries` are the requirements of the
  protocols it may apply, the most recent first; `roles` bounds the roles of a support. -/
  @[expose] def checkRegion (summaries : List (List Requirement)) (roles : Nat) (path : List Nat)
      (index : Nat) (state : State) {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out →
        Except Refusal Returned
    | .ret values =>
        .ok ⟨some ((Scope.numbers state.values.length values).map state.at_), state.next,
          state.made, []⟩
    -- a region of a protocol body does not stop (`protocolStop`): kept for totality
    | .stop _ => .ok ⟨none, state.next, state.made, []⟩
    | .bind (mid := mid) body next =>
        match checkRegion summaries roles (path ++ [index]) 0 state body with
        | .error refusal => .error refusal
        | .ok inner =>
            -- a block always runs to its end, so what it made is made for what follows it
            let (classes, after) :=
              ({ state with next := inner.next, made := inner.made } : State).fresh mid.length
            let copies := match inner.copies with
              | some copies => copies
              | none => classes.map fun class_ => ⟨class_, []⟩
            match checkRegion summaries roles path (index + 1) (after.push copies) next with
            | .error refusal => .error refusal
            | .ok rest => .ok { rest with requirements := inner.requirements ++ rest.requirements }
    | .letOp op arguments bodies next =>
        let levels := Scope.numbers state.values.length arguments
        let operands := levels.map state.at_
        let continue_ (state : State) (requirements : List Requirement) : Except Refusal Returned :=
          match checkRegion summaries roles path (index + 1) state next with
          | .error refusal => .error refusal
          | .ok rest => .ok { rest with requirements := requirements ++ rest.requirements }
        match op, bodies with
        | .at role local_ regions, _ =>
            let key := unelaborateLocalStep functions.length local_ (operands.map (·.class_))
              (unelaborateLocalRegions functions.length regions)
            let support := operands.foldl (fun support copy => union support copy.support) [role]
            let (classes, state) := numbered state key local_.results.length
            continue_ (state.push (classes.map fun class_ => ⟨class_, support⟩)) []
        | .exchange _ receiver _ _, _ =>
            let sent := operands.headD default
            continue_ (state.push [⟨sent.class_, withRole sent.support receiver⟩]) []
        | .draw owner receivers _ _ _, _ =>
            let (classes, state) := state.fresh 1
            let class_ := classes.headD 0
            continue_ (state.push (⟨class_, [owner]⟩ ::
              receivers.map fun receiver => ⟨class_, withRole [owner] receiver⟩)) []
        | .sample owner _ _ _, _ =>
            let (classes, state) := state.fresh 1
            continue_ (state.push [⟨classes.headD 0, [owner]⟩]) []
        | .apply (header := header) callee roleMap _ _, _ =>
            -- the operands at each input agreement of the callee are one class
            let required := header.agreements.inputs.map (agreed roleMap.apply operands)
            match required.find? fun entry => !oneClass entry.2 with
            | some _ => .error ⟨path ++ [index], .operands⟩
            | none =>
                let (classes, state) := portClasses state header.agreements.outputs
                let results := (classes.zip header.outputs).map fun (class_, located) =>
                  (⟨class_, [roleMap.apply located.holder]⟩ : Copy)
                continue_ (state.push results)
                  (required.map (·.1) ++ mapped roleMap (summaries.getD callee.index []))
        | .choose participants tag _ outputs _, bodies =>
            let tags := operands.take participants.length
            let captured := operands.drop participants.length
            if !oneClass tags then .error ⟨path ++ [index], .tags⟩ else
            -- the payload of an alternative, at each participant, has the support of its tag
            match checkRegions summaries roles (path ++ [index])
                (fun _ => { state with
                  next := state.next + 1
                  values := choiceOwn tag state.next tags ++ captured }) 0 (state.next + 1)
                bodies with
            | .error refusal => .error refusal
            | .ok (arms, next, inner) =>
                continue_ (afterChoice state next (arms.filterMap id) outputs)
                  ((participants.zip tags).map (fun (role, copy) => (role, copy.support)) :: inner)
        | .repeat participants count carried collected _ _, bodies =>
            let counts := (loopOperands count participants.length operands).1
            let rest := (loopOperands count participants.length operands).2
            let initial := rest.take carried.length
            let captured := rest.drop carried.length
            if !oneClass counts then .error ⟨path ++ [index], .counts⟩ else
            match settle state participants collected.length captured
                ⟨path ++ [index], .unsettled⟩
                (fun start => checkRegions summaries roles (path ++ [index]) (fun _ => start) 0
                  start.next bodies)
                (carried.length * (roles + 2) + 2) (initial.map fun copy => [copy.class_])
                ((initial.zip carried).map fun (copy, located) =>
                  withRole copy.support located.holder) with
            | .error refusal => .error refusal
            | .ok (gathered, kept, next, inner) =>
                continue_ (afterLoop state next gathered kept initial collected)
                  ((participants.zip counts).map (fun (role, copy) => (role, copy.support)) :: inner)

  /-- The check of the nested regions of an instruction, each from the state at its start.
  It returns what each region returns, the next class, and the requirements found. -/
  @[expose] def checkRegions (summaries : List (List Requirement)) (roles : Nat) (path : List Nat)
      (stateOf : Nat → State) (number : Nat) (next : Nat)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures →
        Except Refusal (List (Option (List Copy)) × Nat × List Requirement)
    | .nil => .ok ([], next, [])
    | .cons body tail =>
        match checkRegion summaries roles (path ++ [number]) 0
            { stateOf number with next := next } body with
        | .error refusal => .error refusal
        | .ok returned =>
            match checkRegions summaries roles path stateOf (number + 1) returned.next tail with
            | .error refusal => .error refusal
            | .ok (others, next, requirements) =>
                .ok (returned.copies :: others, next, returned.requirements ++ requirements)
end

end Protocol

end Copies

section Definitions

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- The check of copies of a protocol: its requirements, or the first that is not met.
`summaries` are the requirements of the protocols before it, the most recent first. -/
@[expose] def ProtocolDefinition.copies {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (summaries : List (List Copies.Requirement)) : Except Copies.Refusal (List Copies.Requirement) :=
  let (classes, state) := Copies.portClasses ⟨[], 0, []⟩ header.agreements.inputs
  let inputs := (classes.zip header.inputs).map fun (class_, located) =>
    (⟨class_, [located.holder]⟩ : Copies.Copy)
  match Copies.checkRegion summaries header.roles [] 0 (state.push inputs) definition.body with
  | .error refusal => .error refusal
  | .ok returned =>
      match returned.copies with
      | none => .ok returned.requirements
      | some copies =>
          let required := header.agreements.outputs.map (Copies.agreed id copies)
          match required.find? fun entry => !Copies.oneClass entry.2 with
          | some _ => .error ⟨[], .outputs⟩
          | none => .ok (returned.requirements ++ required.map (·.1))

/-- The requirements of every protocol of a program, the most recent first, or the protocols
whose check of copies fails, by their numbers in program order, each with its refusal. -/
@[expose] def Protocols.copies {typeTable : TypeTable} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      List (List Copies.Requirement) × List (Nat × Copies.Refusal)
  | _, .nil => ([], [])
  | _, .snoc (protocols := protocols) earlier definition _ =>
      let (summaries, refused) := earlier.copies
      match definition.copies summaries with
      | .ok requirements => (requirements :: summaries, refused)
      | .error refusal => ([] :: summaries, refused ++ [(protocols.length, refusal)])

/-- Every protocol of a program passes the check of copies. -/
@[expose] def Protocols.coherent {typeTable : TypeTable} {protocols : List ProtocolHeader}
    (program : Protocols typeTable operations functions protocols) : Bool :=
  program.copies.2.isEmpty

end Definitions

/-- A side supports requirements: of every requirement of which it has two or more copies, it
contains the support of each of those copies. -/
@[expose] def Side.supports (side : Side) (requirements : List Copies.Requirement) : Bool :=
  requirements.all fun requirement =>
    let present := requirement.filter fun copy => side copy.1
    decide (present.length ≤ 1) || present.all fun copy => copy.2.all side

end Zkc.Core
