import Zkc.Tests.Core.Declare
import Zkc.Core.VocabularyExecute

/-! Checks that the executor's runs are runs of the relations of the endpoint statements.

- One role. The verifier of the serialized program of `fixtures/construction/units.json`, on
  the honest proof of five units, returns in a run that the kernel computes; so its program of
  the meaning returns alone with the collection (`honest_verifier`). On a proof cut short the
  run stops `reject`, and so does the program of the meaning (`cut_verifier`).
- Two roles. The prover and the verifier of the interactive program of
  `fixtures/construction/collecting.json` run against each other: both return, which is the
  hypothesis of `collecting_together`, whose conclusion is that the two programs of the meaning
  return together with those outputs.
- A receiver that hears late. An owner that announces two coins at a site and then sends,
  against a receiver that takes the message and then hears twice: the executor gives the
  receiver the two coins in the order announced. That run is a run of the relation
  (`late_receiver_together`, and `owner_together` from the facts of the run that the checks
  evaluate), and the relation has no run in which the receiver holds the second coin twice
  (`late_receiver_in_order`).
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core Zkc.Core.Vocabulary Zkc.Core.Concrete

namespace ExecutorRuns

def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"executor runs: {label}")

/-! ## One role -/

raw_package serialized from file "fixtures/construction/units.serialized.json"

kernel_refl serialized_elaborates : (elaborate serialized).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw serialized serialized_elaborates

/-- The inputs of the verifier: the bytes of a proof, and nothing for the port of the prover. -/
def proofInputs (bytes : Bytes) : List (Option (Checked table serialized)) :=
  [some (Checked.ofBytes table serialized bytes), none]

kernel_refl honest_run :
  runRole table serialized typed typed.program.protocols Identities.written 1
      (proofInputs [⟨5, by decide⟩]) (seededCoins table serialized [1]) equals
    Except.ok (Execute.Outcome.returned [Datum.sequence (List.replicate 5 (Datum.sequence []))])

/-- The verifier returns in a run on the honest proof, so its program of the meaning, without a
limit, returns alone with a value whose datum is the collection. -/
theorem honest_verifier :
    ∃ (header : ProtocolHeader)
      (program : RoleHeader.Meaning (model table serialized) (roleHeader 1 header))
      (data : List Datum)
      (arguments : Values (model table serialized).Value (roleHeader 1 header).inputs)
      (values : Values (model table serialized).Value (roleHeader 1 header).outputs),
      wholeEntry table serialized typed typed.program.protocols Identities.written 1 =
          .ok ⟨header, program⟩ ∧
        ownInputs 1 header.inputs (proofInputs [⟨5, by decide⟩]) = some data ∧
        Execute.roleValues (model table serialized) rfl (roleHeader 1 header).inputs data =
          some arguments ∧
        ReturnsAlone (seededCoins table serialized [1]).sampler (program [] arguments)
          Asked.start values ∧
        [Datum.sequence (List.replicate 5 (Datum.sequence []))] =
          Execute.roleData (model table serialized) rfl (roleHeader 1 header).outputs values :=
  runRole_returned table serialized typed typed.program.protocols Identities.written honest_run

kernel_refl cut_run :
  runRole table serialized typed typed.program.protocols Identities.written 1
      (proofInputs [⟨128, by decide⟩]) (seededCoins table serialized [1]) equals
    Except.ok (Execute.Outcome.stopped PIR.Stop.reject)

/-- The verifier stops `reject` in a run on a proof cut short, so its program of the meaning
stops alone with `reject`. -/
theorem cut_verifier :
    ∃ (header : ProtocolHeader)
      (program : RoleHeader.Meaning (model table serialized) (roleHeader 1 header))
      (data : List Datum)
      (arguments : Values (model table serialized).Value (roleHeader 1 header).inputs),
      wholeEntry table serialized typed typed.program.protocols Identities.written 1 =
          .ok ⟨header, program⟩ ∧
        ownInputs 1 header.inputs (proofInputs [⟨128, by decide⟩]) = some data ∧
        Execute.roleValues (model table serialized) rfl (roleHeader 1 header).inputs data =
          some arguments ∧
        Execute.StopsAlone (seededCoins table serialized [1]).sampler (program [] arguments)
          Asked.start .reject :=
  runRole_stopped table serialized typed typed.program.protocols Identities.written cut_run

/-! ## Two roles -/

raw_package collecting from file "fixtures/construction/collecting.json"

kernel_refl collecting_elaborates : (elaborate collecting).isOk equals true

noncomputable def collectingTyped : Typed := Typed.ofRaw collecting collecting_elaborates

/-- The statement about a run of two roles, at the interactive program of `collecting`: a run
of its prover and its verifier in which both return is a run in which their two programs of the
meaning return together. The checks below run it. -/
theorem collecting_together {inputs : List (Option (Checked table collecting))}
    {coins : Execute.Coins (model table collecting)} {result : RolesRun}
    {prover verifier : List Datum}
    (ran : runRoles table collecting collectingTyped collectingTyped.program.protocols
      Identities.written [0, 1] inputs coins = .ok result)
    (returned : result.outcomes = [.returned prover, .returned verifier]) :
    ∃ wholeProver wholeVerifier,
      roleProcess table collecting 0 inputs (wholeEntry table collecting collectingTyped
        collectingTyped.program.protocols Identities.written 0) = .ok wholeProver ∧
      roleProcess table collecting 1 inputs (wholeEntry table collecting collectingTyped
        collectingTyped.program.protocols Identities.written 1) = .ok wholeVerifier ∧
      ReturnTogether coins.sampler wholeProver wholeVerifier Mail.empty Board.empty Heard.start
        Heard.start Asked.start prover verifier :=
  runRoles_together table collecting collectingTyped collectingTyped.program.protocols
    Identities.written ran returned

#eval show IO Unit from do
  let text ← IO.FS.readFile (package_file "fixtures/construction/collecting.json")
  let package ← match Raw.parsePackage text with
    | .ok package => pure package
    | .error message => throw (IO.userError message)
  let data : List Datum := [.number 5, .number 5, .number 2, .number 2]
  for seed in [[1], [11, 12, 13], []] do
    match runEntry table package [0, 1] data seed with
    | .error message => throw (IO.userError message)
    | .ok result =>
      check s!"the two roles of `collecting` return, seed {seed}" (match result.outcomes with
        | [.returned _, .returned _] => true
        | _ => false)
  -- the same inputs, validated once, in several runs
  match elaborate package with
  | .error _ => throw (IO.userError "refused")
  | .ok elaborated =>
    let inputs := checkedInputs table package ((elaborated.protocols.head?.map (·.inputs)).getD []) data
    check "the inputs of `collecting` are values of their types" (inputs.all (·.isSome))
    for seed in [[2], [3]] do
      match runRoles table package elaborated elaborated.program.protocols Identities.written [0, 1]
          inputs (seededCoins table package seed) with
      | .ok result =>
        check s!"the validated inputs run, seed {seed}" (match result.outcomes with
          | [.returned _, .returned _] => true
          | _ => false)
      | .error message => throw (IO.userError message)

/-! ## A receiver that hears late -/

def site (number : Nat) : Site := ⟨[], 0, number⟩

def law : SamplingRow := ⟨0, [], .bool, rfl⟩

/-- An owner that announces two coins at one site and then sends. -/
def owner : PIR.Process (Effects Model.unit) (List Bool) :=
  .call (.draw (site 0) law .nil) fun first =>
    .call (.draw (site 0) law .nil) fun second =>
      .call (.send (site 1) .bool true) fun _ => .done [first, second]

/-- A receiver that takes the message and then hears the site of the coins twice. -/
def receiver : PIR.Process (Effects Model.unit) (List Bool) :=
  .call (.receive (site 1) .bool) fun _ =>
    .call (.receive (site 0) .bool) fun first =>
      .call (.receive (site 0) .bool) fun second => .done [first, second]

/-- A receiver that hears each coin before it takes the message. -/
def prompt : PIR.Process (Effects Model.unit) (List Bool) :=
  .call (.receive (site 0) .bool) fun first =>
    .call (.receive (site 0) .bool) fun second =>
      .call (.receive (site 1) .bool) fun _ => .done [first, second]

/-- Coins that alternate: `true`, `false`, … at every site, and none at another type. -/
def alternating : Execute.Coins Model.unit := fun _ count type =>
  match type with
  | .bool => some (count % 2 == 0)
  | _ => none

/-- The statement about a run of two processes, at the owner and a receiver: a run in which
both return is a run of the relation, whatever the order in which the receiver hears. -/
theorem owner_together (other : PIR.Process (Effects Model.unit) (List Bool))
    {first second : List Bool}
    (returned : (Execute.run Model.unit alternating [owner, other]).roles.map (·.process) =
      [.done first, .done second]) :
    ReturnTogether alternating.sampler owner other Mail.empty Board.empty Heard.start Heard.start
      Asked.start first second :=
  Execute.run_together alternating owner other returned

/-- The mail after the owner's message. -/
theorem sent : (Mail.empty.put (site 1) .bool true : Mail Model.unit) (site 1) =
    [⟨.bool, true⟩] :=
  Mail.put_empty_self (site 1) .bool true

/-- The run of the late receiver, in the order of the executor, is a run of the relation: the
owner announces `true` and then `false` and sends, and the receiver takes the message and then
hears `true` and `false`, in the order announced. -/
theorem late_receiver_together :
    ReturnTogether alternating.sampler owner receiver Mail.empty Board.empty Heard.start
      Heard.start Asked.start [true, false] [true, false] := by
  refine .drawLeft (.drawLeft (.sendLeft (.receiveRight (value := true) (rest := []) sent ?_)))
  refine .hearRight (value := true) rfl rfl (.hearRight (value := false) rfl rfl ?_)
  exact .done _ _ _ _ _ _ _

/-- The relation has no run of the owner and the late receiver in which the receiver holds
anything but the two coins in the order announced: not the second coin twice, which the
relation with the coin last announced gave it. -/
theorem late_receiver_in_order {held heard : List Bool}
    (together : ReturnTogether alternating.sampler owner receiver Mail.empty Board.empty
      Heard.start Heard.start Asked.start held heard) : heard = [true, false] := by
  -- The receiver waits for the message, which the owner sends after its two draws.
  cases together with
  | receiveRight found _ => cases found
  | hearRight _ announced _ => cases announced
  | drawLeft together =>
    cases together with
    | receiveRight found _ => cases found
    | hearRight _ announced _ => cases announced
    | drawLeft together =>
      cases together with
      | receiveRight found _ => cases found
      | hearRight _ announced _ => cases announced
      | sendLeft together =>
        cases together with
        | hearRight empty _ _ => cases empty
        | receiveRight found together =>
          -- The receiver hears at the site of the coins, with the message taken.
          cases together with
          | receiveRight found _ => cases found
          | hearRight _ first together =>
            cases together with
            | receiveRight found _ => cases found
            | hearRight _ second together =>
              cases together
              cases first
              cases second
              rfl

#print axioms owner_together
#print axioms late_receiver_together
#print axioms late_receiver_in_order

#eval show IO Unit from do
  let returned (process : PIR.Process (Effects Model.unit) (List Bool)) : Option (List Bool) :=
    match process with
    | .done value => some value
    | _ => none
  -- the receiver that hears each coin as it is announced
  let inStep := Execute.run Model.unit alternating [owner, prompt]
  check "the prompt receiver hears the coins in order"
    (inStep.roles.map (fun role => returned role.process) ==
      [some [true, false], some [true, false]])
  -- the receiver that takes the message first hears the first coin after the second one was
  -- announced: the executor gives it the coins in the order announced, and both return, which
  -- is the hypothesis of `owner_together`
  let late := Execute.run Model.unit alternating [owner, receiver]
  check "the late receiver hears the coins in the order announced"
    (late.roles.map (fun role => returned role.process) ==
      [some [true, false], some [true, false]])
  check "the board of the late run holds both coins of the site, in order"
    ((late.shared.board (site 0)).length == 2 && (late.roles.map (·.heard (site 0))) == [0, 2])
  -- a source without a coin at the type: the draw is not performed, and the role has failed
  let none : Execute.Coins Model.unit := fun _ _ _ => none
  check "a draw without a coin fails the role"
    (match (Execute.runAll Model.unit none #[owner]).toList with
      | [Execute.Outcome.failed _] => true
      | _ => false)
  check "a run of one process without a coin fails"
    (match Execute.runAlone Model.unit none owner with
      | .failed _ => true
      | _ => false)

end ExecutorRuns
