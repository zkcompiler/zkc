import Zkc.Tests.Core.Threading
import Zkc.Tests.Core.ThreadingSumcheck
import Zkc.Tests.Core.ThreadingSchnorr
import Zkc.Core.SerializeReplayEntry

/-! The serialize step replays: the theorem at the fixtures, and its axioms.

`serialize_entry_replays` at the serialize step of three packages, on the result of their
Fiat–Shamir step: `fixtures/construction/collecting.json` (two loops and an applied
protocol that the serialize step copies), `fixtures/construction/sumcheck.json` (an applied
protocol with an image that threads, and functions) and
`fixtures/construction/schnorr-source.json` (a suite whose rule calls functions). For an
arbitrary model, each statement is `SerializedReplays` of the entry after the Fiat–Shamir
step and of the entry after both steps. The equation of the step and the position of the
entry are discharged by the kernel. What remains of the hypotheses is what
`SerializedReplays` itself asks: the laws of the layout (`Layout.Lawful`, an argument of
each statement), that every run of the grouped entry returns, and that the value of every
message of the prover is one that the layout can write. That the layout has the rows for the
type of every message is not asked: the step returned.

A package of one protocol, in which the prover sends a value that the verifier checks, with
a layout whose writer is the list of the values written (`Toy`). In the model of these rows
the layout has the laws, so `Layout.Lawful` is not vacuous; `Written`, `Takes` and the
round trip are evaluated at two values; every premise of the theorem holds of the package,
so its conclusion is an instance (`Toy.serialized_accepts`). Over a model whose `take`
returns another value the layout has no laws under which a value is writable
(`Toy.flipped_not_lawful`), and the conclusion fails on the same package: the serialized
verifier stops on the proof that the serialized prover returns (`Toy.flipped_fails`).

The axioms of every theorem of the modules of the replay are printed at the end.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace SerializeReplay

/-! ## The theorem at the fixtures -/

/-- The serialize step of `collecting.json` replays. -/
theorem collecting_replays (model : Model) (laws : Threading.layout.Lawful model) :
    SerializedReplays Threading.layout laws Threading.roles Threading.onceHeader
      ((Threading.once.protocols.table model (Threading.functionTable model)
        Threading.once.identities).get Threading.onceEntry)
      ((Threading.twice.protocols.table model (Threading.functionTable model)
        Threading.twice.identities).get Threading.twiceEntry) := by
  obtain ⟨image, first, replays⟩ := serialize_entry_replays (model := model) Threading.layout
    Threading.once.identities (Threading.once.headers.length - 1) Threading.roles
    (⟨Threading.typed.program.functions, Threading.once.protocols⟩ :
      Program Threading.typed.typeTable Threading.operations Threading.typed.functions
        Threading.once.headers)
    Threading.twice Threading.serialize_steps Threading.onceEntry (Nat.sub_self _).symm
  have same : image = Threading.twiceEntry := Var.ext first
  subst same
  exact replays laws

/-- The serialize step of `sumcheck.json` replays. -/
theorem sumcheck_replays (model : Model) (laws : ThreadingSumcheck.layout.Lawful model) :
    SerializedReplays ThreadingSumcheck.layout laws Threading.roles ThreadingSumcheck.onceHeader
      ((ThreadingSumcheck.once.protocols.table model (ThreadingSumcheck.functionTable model)
        ThreadingSumcheck.once.identities).get ThreadingSumcheck.onceEntry)
      ((ThreadingSumcheck.twice.protocols.table model (ThreadingSumcheck.functionTable model)
        ThreadingSumcheck.twice.identities).get ThreadingSumcheck.twiceEntry) := by
  obtain ⟨image, first, replays⟩ := serialize_entry_replays (model := model)
    ThreadingSumcheck.layout ThreadingSumcheck.once.identities
    (ThreadingSumcheck.once.headers.length - 1) Threading.roles
    (⟨ThreadingSumcheck.typed.program.functions, ThreadingSumcheck.once.protocols⟩ :
      Program ThreadingSumcheck.typed.typeTable ThreadingSumcheck.operations
        ThreadingSumcheck.typed.functions ThreadingSumcheck.once.headers)
    ThreadingSumcheck.twice ThreadingSumcheck.serialize_steps ThreadingSumcheck.onceEntry
    (Nat.sub_self _).symm
  have same : image = ThreadingSumcheck.twiceEntry := Var.ext first
  subst same
  exact replays laws

/-- The serialize step of `schnorr-source.json` replays. -/
theorem schnorr_replays (model : Model) (laws : ThreadingSchnorr.layout.Lawful model) :
    SerializedReplays ThreadingSchnorr.layout laws Threading.roles ThreadingSchnorr.onceHeader
      ((ThreadingSchnorr.once.protocols.table model (ThreadingSchnorr.functionTable model)
        ThreadingSchnorr.once.identities).get ThreadingSchnorr.onceEntry)
      ((ThreadingSchnorr.twice.protocols.table model (ThreadingSchnorr.functionTable model)
        ThreadingSchnorr.twice.identities).get ThreadingSchnorr.twiceEntry) := by
  obtain ⟨image, first, replays⟩ := serialize_entry_replays (model := model)
    ThreadingSchnorr.layout ThreadingSchnorr.once.identities
    (ThreadingSchnorr.once.headers.length - 1) Threading.roles
    (⟨ThreadingSchnorr.typed.program.functions, ThreadingSchnorr.once.protocols⟩ :
      Program ThreadingSchnorr.typed.typeTable ThreadingSchnorr.operations
        ThreadingSchnorr.typed.functions ThreadingSchnorr.once.headers)
    ThreadingSchnorr.twice ThreadingSchnorr.serialize_steps ThreadingSchnorr.onceEntry
    (Nat.sub_self _).symm
  have same : image = ThreadingSchnorr.twiceEntry := Var.ext first
  subst same
  exact replays laws

/-! ## A layout that has the laws, and one that has not

A package of one nominal type, the wire, six rows over it and one protocol: the prover
sends `true`, and the verifier stops `reject` unless what it receives holds and returns
it. The layout has the wire as its writer, reader and proof, and `bool` as its one message
type. In the model the wire is the list of the values written: `put` appends a value,
`take` removes the first one, `close` and `read` leave the list as it is. With `flip =
false` the model has the laws; with `flip = true` its `take` returns the negation, and no
value is writable under any laws. -/

namespace Toy

/-- The wire. -/
abbrev wire : Ty := .nominal 0

/-- A row of the package, by the letter that names it. -/
abbrev row (letter : Nat) (inputs outputs : List Ty) : Operation :=
  ⟨⟨[letter], []⟩, ⟨inputs, outputs, .pure⟩⟩

/-- The package: the wire; the rows `start`, `put`, `close`, `read`, `take`, `exhausted`;
two functions, one that returns `false` and one that returns its second input, which no
protocol calls (a suite of `Tests/Core/DerivedScheme.lean` starts a transcript with the
first and absorbs a message with the second); and the protocol of a prover, role 0, and a
verifier, role 1. -/
abbrev packageRaw : Raw.Package :=
  ⟨[⟨[119], []⟩], [], [],
    [row 115 [] [wire], row 112 [wire, .bool] [wire], row 99 [wire] [wire], row 114 [wire] [wire],
      row 116 [wire] [.bool, .bool, wire], row 101 [wire] [.bool]],
    [⟨false, [], [.bool], some (.step (.literal (.bool false)) (.ret [0]))⟩,
      ⟨false, [.bool, .bool], [.bool], some (.ret [1])⟩],
    [⟨false, 2, [], [⟨.bool, 1⟩], [],
      .step (.at 0 (.literal (.bool true))) <|
      .step (.exchange 0 1 0 0) <|
      .step (.at 1 (.guard .reject 1)) <|
      .ret [1]⟩],
    none⟩

kernel_refl package_elaborates : (elaborate packageRaw).isOk equals true

noncomputable def packageElaborated : Typed := Typed.ofRaw packageRaw package_elaborates

typed_literal typed := packageElaborated

kernel_refl typed_eq : elaborate packageRaw equals Except.ok typed

/-- The rows of the package. -/
noncomputable abbrev rows : List OperationSignature := typed.table.map (·.signature)

/-- The header of the protocol, and the protocol. -/
abbrev header : ProtocolHeader := ⟨2, [], [⟨.bool, 1⟩], .none, false⟩

abbrev entry : Var typed.protocols header := ⟨0, rfl⟩

/-- The prover and the verifier. -/
abbrev roles : TranscriptRoles := ⟨0, 1⟩

/-- The side of the prover and the verifier. -/
abbrev both : Side := (single 0).union (single 1)

/-- The layout: the values of `bool` are the only messages. -/
noncomputable def layout : Layout rows where
  writer := wire
  reader := wire
  proof := wire
  writerPopulated := rfl
  readerPopulated := rfl
  proofPopulated := rfl
  start := ⟨0, kernel_rfl%⟩
  put := fun type =>
    match type with
    | .bool => some ⟨1, kernel_rfl%⟩
    | _ => none
  close := ⟨2, kernel_rfl%⟩
  read := ⟨3, kernel_rfl%⟩
  take := fun type =>
    match type with
    | .bool => some ⟨4, kernel_rfl%⟩
    | _ => none
  exhausted := ⟨5, kernel_rfl%⟩

/-- The model: the wire is the list of the values written. `take` returns the first value,
negated when `flip` holds. -/
def model (flip : Bool) : Model where
  Carrier _ := List Bool
  pure row populated arguments :=
    match row, populated, arguments with
    | ⟨0, [], [.nominal 0]⟩, _, _ => .cons ([] : List Bool) .nil
    | ⟨1, [.nominal 0, .bool], [.nominal 0]⟩, _, .cons writer (.cons value .nil) =>
        .cons (writer ++ [value] : List Bool) .nil
    | ⟨2, [.nominal 0], [.nominal 0]⟩, _, arguments => arguments
    | ⟨3, [.nominal 0], [.nominal 0]⟩, _, arguments => arguments
    | ⟨4, [.nominal 0], [.bool, .bool, .nominal 0]⟩, _, .cons reader .nil =>
        match (reader : List Bool) with
        | [] => .cons false (.cons false (.cons ([] : List Bool) .nil))
        | value :: rest => .cons true (.cons (value != flip) (.cons rest .nil))
    | ⟨5, [.nominal 0], [.bool]⟩, _, .cons reader .nil =>
        .cons (reader : List Bool).isEmpty .nil
    | row, populated, _ => Ty.inhabitants (fun _ => ([] : List Bool)) row.outputs populated
  restricted _ _ := none
  «opaque» _ _ := .error .abort
  literal _ _ := []

/-- The content that a value is written as: a value of `bool` as itself. -/
def encode (flip : Bool) : (type : Ty) → (model flip).Value type → List Bool
  | .bool, value => [value]
  | _, _ => []

/-- The model that does not flip has the laws: every value of `bool` is writable. -/
noncomputable def laws : layout.Lawful (model false) where
  Wire := List Bool
  empty := []
  append := fun first second => first ++ second
  append_assoc := List.append_assoc
  empty_append := List.nil_append
  append_empty := List.append_nil
  encode := encode false
  Writable := fun type _ => type = .bool
  ofWriter := fun writer => writer
  toReader := fun content => content
  start_empty := rfl
  put_appends := by
    intro type put row value writable writer
    subst writable
    have same : put = ⟨1, kernel_rfl%⟩ := (Option.some.inj row).symm
    subst same
    cases value <;> rfl
  close_read := fun _ => rfl
  take_reads := by
    intro type take populated row value writable rest
    subst writable
    have same : take = ⟨4, kernel_rfl%⟩ := (Option.some.inj row).symm
    subst same
    cases value <;> rfl
  exhausted_empty := rfl

/-- The layout carries the values of `bool`, and under the laws each can be sent. -/
theorem sendable (value : Bool) : laws.Sendable .bool value :=
  ⟨⟨rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩

/-- Putting `true` and `false` on the writer that `start` opens gives the writer of both. -/
theorem written : layout.Written (model false) (layout.opened (model false))
    [⟨.bool, true⟩, ⟨.bool, false⟩] ([true, false] : List Bool) :=
  .cons ⟨1, kernel_rfl%⟩ rfl (.cons ⟨1, kernel_rfl%⟩ rfl (.nil _))

/-- Taking `true` and `false` from the reader of both leaves the reader of nothing. -/
theorem takes : layout.Takes (model false) ([true, false] : List Bool)
    [⟨.bool, true⟩, ⟨.bool, false⟩] ([] : List Bool) :=
  .cons ⟨4, kernel_rfl%⟩ rfl rfl rfl (.cons ⟨4, kernel_rfl%⟩ rfl rfl rfl (.nil _))

/-- The reader does not give `false` before `true`. -/
theorem takes_in_order : ¬layout.Takes (model false) ([true, false] : List Bool)
    [⟨.bool, false⟩, ⟨.bool, true⟩] ([] : List Bool) := by
  intro taken
  obtain ⟨middle, first, _⟩ := Layout.Takes.split (first := [⟨.bool, false⟩]) taken
  obtain ⟨take, populated, row, gives⟩ := first.single
  have same : take = ⟨4, kernel_rfl%⟩ := (Option.some.inj row).symm
  subst same
  have value : true = false := congrArg (fun values => values.tail.get .here) gives
  cases value

/-- The round trip at `true` and `false`: they are taken from the reader of the closed
writer, which is then exhausted. -/
theorem round_trip : ∃ reader,
    layout.Takes (model false)
      (layout.reading (model false) (layout.closed (model false) ([true, false] : List Bool)))
      [⟨.bool, true⟩, ⟨.bool, false⟩] reader ∧
    layout.isExhausted (model false) reader = true :=
  laws.round_trip
    (fun message member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact sendable true
      · rw [List.mem_singleton.mp later]
        exact sendable false)
    written

/-- A layout whose `take` returns another value has no laws under which a value is
writable: the reader of what `close` makes of the writer of a value gives its negation. -/
theorem flipped_not_lawful (flipped : layout.Lawful (model true)) (value : Bool) :
    ¬flipped.Writable .bool value := by
  intro writable
  have start : flipped.ofWriter ([] : List Bool) = flipped.empty := flipped.start_empty
  have put : flipped.ofWriter ([value] : List Bool) =
      flipped.append (flipped.ofWriter ([] : List Bool)) (flipped.encode .bool value) :=
    flipped.put_appends (type := .bool) ⟨1, kernel_rfl%⟩ rfl value writable []
  have closeRead : ([value] : List Bool) = flipped.toReader (flipped.ofWriter ([value] : List Bool)) :=
    flipped.close_read [value]
  have content : flipped.encode .bool value = flipped.ofWriter ([value] : List Bool) := by
    rw [put, start, flipped.empty_append]
  have take := flipped.take_reads (type := .bool) ⟨4, kernel_rfl%⟩ rfl rfl value writable
    flipped.empty
  rw [flipped.append_empty, content, ← closeRead] at take
  have same : (value != true) = value := congrArg (fun values => values.tail.get .here) take
  cases value <;> cases same

/-! ### The serialize step on the package -/

/-- The serialize step on the protocols of the package. -/
noncomputable abbrev step : Except StepRefusal (Stepped typed.typeTable rows typed.functions) :=
  stepProtocols layout.threads (serializeRule layout) Identities.written 0 roles
    typed.program.protocols

kernel_refl step_returns : step.isOk equals true

noncomputable def serialized : Stepped typed.typeTable rows typed.functions :=
  Threading.okValue step step_returns

theorem steps : step = .ok serialized := Threading.okValue_eq _ _

/-- The header of the serialized entry, and the serialized entry. -/
noncomputable abbrev serializedHeader : ProtocolHeader :=
  (serializeRule (functions := typed.functions) layout).entryHeader roles header

noncomputable abbrev serializedEntry : Var serialized.headers serializedHeader := ⟨0, kernel_rfl%⟩

/-- The meaning of the entry, and of the serialized entry, in a model. -/
noncomputable abbrev entryMeaning (flip : Bool) : header.Meaning (model flip) :=
  (typed.program.protocolTable (model flip) Identities.written).get entry

noncomputable abbrev serializedMeaning (flip : Bool) : serializedHeader.Meaning (model flip) :=
  (serialized.protocols.table (model flip) (typed.program.functionTable (model flip))
    serialized.identities).get serializedEntry

/-- The serialize step on the package replays, in the model that has the laws. -/
theorem replays : SerializedReplays layout laws roles header (entryMeaning false)
    (serializedMeaning false) := by
  obtain ⟨image, first, related⟩ := serialize_entry_replays (model := model false) layout
    Identities.written 0 roles typed.program serialized steps entry kernel_rfl%
  have same : image = serializedEntry := Var.ext first
  subst same
  exact related laws

/-- The value that a process returns at once. -/
def returned {flip : Bool} {α : Type} : PIR.Process (Effects (model flip)) α → Option α
  | .done value => some value
  | _ => none

/-- The value of `bool` that a process sends before it returns. -/
def sent {flip : Bool} {α : Type} : PIR.Process (Effects (model flip)) α → Option Bool
  | .call (.send _ .bool value) next =>
      match next PUnit.unit with
      | .done _ => some value
      | _ => none
  | _ => none

/-- The reason for which a process stops at once. -/
def stopped {flip : Bool} {α : Type} : PIR.Process (Effects (model flip)) α → Option PIR.Stop
  | .halt reason => some reason
  | _ => none

/-- The verifier's result. -/
abbrev accepted (flip : Bool) (outputs : Values (SideValue (model flip) both) header.outputs) :
    Bool :=
  Held.value (X := Bool) (both 1) rfl (outputs.get .here)

-- The grouped entry returns `true`, in both models.
kernel_refl grouped_accepts :
  ((returned (entryMeaning false [] both .nil)).map (accepted false),
    (returned (entryMeaning true [] both .nil)).map (accepted true))
  equals (some true, some true)

-- The entry for the prover alone sends `true` and returns.
kernel_refl prover_sends : sent (entryMeaning false [] (single 0) .nil) equals some true

/-- Every run of the grouped entry returns outputs that the verifier accepts. -/
theorem every (flip : Bool) :
    EveryRun (fun outputs => accepted flip outputs = true) (entryMeaning flip [] both .nil) := by
  have observed : (returned (entryMeaning flip [] both .nil)).map (accepted flip) = some true := by
    cases flip
    · exact congrArg Prod.fst grouped_accepts
    · exact congrArg Prod.snd grouped_accepts
  generalize entryMeaning flip [] both .nil = process at observed
  cases process with
  | done value => exact Option.some.inj observed
  | halt reason => cases observed
  | call effect next => cases observed

/-- Every message of the entry for the prover alone is one that the layout can write. -/
theorem writable :
    EverySend laws.Writable (fun _ => True)
      (entryMeaning false [] (single 0) (leftValues (model false) (single 0) (single 1) .nil)) := by
  have observed : sent (entryMeaning false [] (single 0) .nil) = some true := prover_sends
  show EverySend laws.Writable (fun _ => True) (entryMeaning false [] (single 0) .nil)
  generalize entryMeaning false [] (single 0) .nil = process at observed
  cases process with
  | done value => cases observed
  | halt reason => cases observed
  | call effect next =>
      cases effect with
      | send site type value =>
          cases type <;> try cases observed
          simp only [sent] at observed
          split at observed
          · rename_i result returns
            cases observed
            exact ⟨rfl, by rw [returns]; trivial⟩
          · cases observed
      | receive site type => cases observed
      | draw site law inputs => cases observed
      | sample site law inputs => cases observed
      | read site type position => cases observed

/-- Every premise of the theorem holds of the package, the layout and the model: for every
sampler the serialized prover returns a proof on which the serialized verifier returns the
accepted output. -/
theorem serialized_accepts (sampler : Sampler (model false)) :
    ∃ (outputs : Values (SideValue (model false) both) header.outputs) (proof : List Bool),
      accepted false outputs = true ∧
      ReturnsAlone sampler
        (serializedMeaning false [] (single 0)
          (Values.cons (Value := SideValue (model false) (single 0)) (ty := ⟨wire, 1⟩) PUnit.unit
            (leftValues (model false) (single 0) (single 1) .nil)))
        Asked.start
        (Values.cons (Value := SideValue (model false) (single 0)) (ty := ⟨wire, 0⟩) proof
          (leftValues (model false) (single 0) (single 1) outputs)) ∧
      ReturnsAlone sampler
        (serializedMeaning false [] (single 1)
          (Values.cons (Value := SideValue (model false) (single 1)) (ty := ⟨wire, 1⟩) proof
            (rightValues (model false) (single 0) (single 1) .nil)))
        Asked.start
        (Values.cons (Value := SideValue (model false) (single 1)) (ty := ⟨wire, 0⟩) PUnit.unit
          (rightValues (model false) (single 0) (single 1) outputs)) :=
  replays .nil (fun outputs => accepted false outputs = true) (every false) writable sampler
    PUnit.unit

/-! ### The same package over the layout without the laws -/

-- In the model that flips, the serialized prover returns the proof of `true`, and the
-- serialized verifier stops `reject` on it: it takes `false`.
kernel_refl flipped_prover_proof :
  (returned (serializedMeaning true [] (single 0)
    (Values.cons (Value := SideValue (model true) (single 0)) (ty := ⟨wire, 1⟩) PUnit.unit .nil))).map
    (fun outputs => (outputs.get .here : List Bool))
  equals some [true]

kernel_refl flipped_verifier_rejects :
  stopped (serializedMeaning true [] (single 1)
    (Values.cons (Value := SideValue (model true) (single 1)) (ty := ⟨wire, 1⟩)
      ([true] : List Bool) .nil))
  equals some .reject

/-- The conclusion of the theorem fails over the layout without the laws, although every
run of the grouped entry returns an accepted output (`every true`): no proof that the
serialized prover returns is one on which the serialized verifier returns. -/
theorem flipped_fails (sampler : Sampler (model true)) :
    ¬∃ (proof : List Bool) (proverOutputs : Values (SideValue (model true) (single 0)) header.outputs)
        (verifierOutputs : Values (SideValue (model true) (single 1)) serializedHeader.outputs),
      ReturnsAlone sampler
        (serializedMeaning true [] (single 0)
          (Values.cons (Value := SideValue (model true) (single 0)) (ty := ⟨wire, 1⟩) PUnit.unit .nil))
        Asked.start
        (Values.cons (Value := SideValue (model true) (single 0)) (ty := ⟨wire, 0⟩) proof
          proverOutputs) ∧
      ReturnsAlone sampler
        (serializedMeaning true [] (single 1)
          (Values.cons (Value := SideValue (model true) (single 1)) (ty := ⟨wire, 1⟩) proof .nil))
        Asked.start verifierOutputs := by
  rintro ⟨proof, proverOutputs, verifierOutputs, proves, verifies⟩
  have observed := flipped_prover_proof
  have isProof : proof = [true] := by
    generalize serializedMeaning true [] (single 0)
      (Values.cons (Value := SideValue (model true) (single 0)) (ty := ⟨wire, 1⟩) PUnit.unit .nil) =
        process at observed proves
    cases proves with
    | done value asked => exact Option.some.inj observed
    | draw site law inputs next asked value returns => cases observed
    | sample site law inputs next asked value returns => cases observed
  subst isProof
  have rejects := flipped_verifier_rejects
  generalize serializedMeaning true [] (single 1)
    (Values.cons (Value := SideValue (model true) (single 1)) (ty := ⟨wire, 1⟩)
      ([true] : List Bool) .nil) = process at rejects verifies
  cases verifies with
  | done value asked => cases rejects
  | draw site law inputs next asked value returns => cases rejects
  | sample site law inputs next asked value returns => cases rejects

end Toy

end SerializeReplay

/-! ## Axioms -/

#print axioms SerializeReplay.collecting_replays
#print axioms SerializeReplay.sumcheck_replays
#print axioms SerializeReplay.schnorr_replays
#print axioms SerializeReplay.Toy.sendable
#print axioms SerializeReplay.Toy.written
#print axioms SerializeReplay.Toy.takes
#print axioms SerializeReplay.Toy.takes_in_order
#print axioms SerializeReplay.Toy.round_trip
#print axioms SerializeReplay.Toy.flipped_not_lawful
#print axioms SerializeReplay.Toy.replays
#print axioms SerializeReplay.Toy.every
#print axioms SerializeReplay.Toy.writable
#print axioms SerializeReplay.Toy.serialized_accepts
#print axioms SerializeReplay.Toy.flipped_fails

#print axioms EveryRun.runs
#print axioms EverySend.mono
#print axioms EverySend.trivial
#print axioms Held.of_value
#print axioms Held.value_inj
#print axioms Layout.Lawful.round_trip
#print axioms Layout.Lawful.takes_content
#print axioms Layout.Lawful.written_content
#print axioms Layout.Takes.append
#print axioms Layout.Takes.nil_inv
#print axioms Layout.Takes.single
#print axioms Layout.Takes.split
#print axioms Layout.Written.append
#print axioms Layout.closing_prover
#print axioms Layout.closing_verifier
#print axioms Layout.opening_prover
#print axioms Layout.opening_verifier
#print axioms Mirrors.refl
#print axioms Mirrors.runs
#print axioms PartsReplay.bind
#print axioms PartsReplay.congr
#print axioms PartsReplay.done
#print axioms PartsReplay.halt
#print axioms PartsReplay.iterations
#print axioms PartsReplay.never
#print axioms PartsReplay.ofPasses
#print axioms PartsReplay.proverMirrors
#print axioms PartsReplay.receive
#print axioms PartsReplay.send
#print axioms PartsReplay.verifierMirrors
#print axioms Reached.earlier
#print axioms Reached.newest
#print axioms RegionsReplay.ofPasses
#print axioms RunsTo.bind
#print axioms RunsTo.returnsAlone
#print axioms Side.Holds.callee
#print axioms Side.Holds.member
#print axioms accepted_letOp
#print axioms agreed_replays
#print axioms agreed_replays_keyed
#print axioms alternativeProcess_replays
#print axioms alternativeProcess_replaysFirst
#print axioms alternativeProcess_replaysSecond
#print axioms apply_admits
#print axioms apply_replays
#print axioms at_replays
#print axioms bothTouch_ok
#print axioms choose_replays
#print axioms definition_replays_plain
#print axioms definition_replays_threaded
#print axioms drawFits_passes
#print axioms draw_admits
#print axioms draw_apart
#print axioms draw_replays
#print axioms draw_results_outside
#print axioms entry_reached
#print axioms everySend_bind
#print axioms exchangeStep_replays
#print axioms exchange_admits
#print axioms exchange_apart
#print axioms exchange_forward
#print axioms exchange_forward_only
#print axioms exchange_replays
#print axioms letOp_replays
#print axioms natBeq_swap
#print axioms operation_admits_plain
#print axioms passHandler_passes
#print axioms passRegions_passAll
#print axioms performStep_replays
#print axioms preimageBelow_none
#print axioms propagate_reached_applied
#print axioms receiverReplies_replays
#print axioms region_admits
#print axioms region_admits_plain
#print axioms region_replays
#print axioms regions_admit
#print axioms regions_admit_plain
#print axioms regions_replay
#print axioms repeatProcess_replays
#print axioms repeat_replays
#print axioms returns_through
#print axioms rewriteDefinition_carries
#print axioms rewriteProtocols_newest_carries
#print axioms rewriteProtocols_newest_images
#print axioms rewriteProtocols_replays
#print axioms roles_apart
#print axioms sample_replays
#print axioms selectArm_replays
#print axioms selectArm_replaysFirst
#print axioms selectArm_replaysSecond
#print axioms serializeMeaning_exchange_prover
#print axioms serializeMeaning_exchange_verifier
#print axioms serializeRule_entry_threads
#print axioms serializeRule_exchange_carries
#print axioms serialize_entry_replays
#print axioms single_holds
#print axioms singles_disjoint
#print axioms threadRegion_carries
#print axioms threadRegions_carry
#print axioms threadedCallee_none
#print axioms threadedCallee_some
#print axioms untouched_apply
#print axioms untouched_carries
#print axioms untouched_operation_carries
#print axioms untouched_regions_carry
