import Zkc.Tests.Core.Check
import Zkc.Tests.Core.Reflexivity
import Zkc.Core.EndpointsCompleteness
import Zkc.Core.ThreadPlain
import Zkc.Core.Legal

/-! Samplers exist, completeness of a grouped program separates programs, and the endpoint
lemma has an instance.

- A coin at every type does not exist: `fin 0` has no value. A sampler gives a coin at
  every type that has a value, and every model has one, the one-point model included.
- A table whose sampling row has an output type without a value is refused, as one whose
  pure row has.
- Two packages of two roles, a prover and a verifier, with the law of `bool`. In the first
  the prover samples a secret and sends it, the verifier draws a public coin, the prover
  answers whether the secret is the coin, and the verifier checks the answer and returns
  that it holds. In the second the verifier stops `reject` on a condition that is false.
  For an arbitrary model the first is complete, with the verifier's result `true` as the
  accepted one, and it is not complete with `false` as the accepted one; the second is not
  complete even when every result is accepted. The kernel runs the first on every coin.
- The endpoint lemma at the first package and the sampler of a model: the programs of the
  two roles, run against each other, return together, the verifier `true`.
- The conditions that the statements of the package take of a program hold at the first
  package: the domain laws of the one-point model, functions without an effect, legal
  headers, a protocol that is idle for a side without its roles, the restriction law and
  the soundness of the role programs.
- Completeness of a derived scheme is a condition: it holds of a prover that returns a
  proof and a verifier that returns `true`, and fails of a verifier that stops `reject`.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Samplers

/-! ## Samplers -/

/-- A coin at every type does not exist, whatever the model. -/
theorem no_coin_at_every_type (model : Model) (coin : (type : Ty) → model.Value type) : False :=
  Fin.elim0 (coin (.fin 0))

/-- Every model has a sampler. -/
def sampler (model : Model) : Sampler model := Sampler.constant model

/-- The one-point model has a sampler. -/
def unitSampler : Sampler Model.unit := sampler Model.unit

/-- The coins of the one-point model's sampler at `bool` and at a sequence of four of
`fin 3`. -/
theorem unit_coin_bool (site : Site) (count : Nat) :
    unitSampler.coin site count .bool rfl = false := rfl

theorem unit_coin_sequence (site : Site) (count : Nat) :
    (unitSampler.coin site count (.seq (.fin 3) (some 4)) rfl).val = [0, 0, 0, 0] := rfl

/-! ## The table -/

/-- The catalogue name `law.uniform`. -/
abbrev lawName : Name := [108, 97, 119, 46, 117, 110, 105, 102, 111, 114, 109]

/-- The law of a type. -/
abbrev lawOf (type : Ty) : Operation := ⟨⟨lawName, [.type type]⟩, ⟨[], [type], .sampling⟩⟩

kernel_refl law_table : tablesViolation [] [] [] [lawOf .bool] equals none

-- A law of a type without a value: the table is refused.
kernel_refl empty_law_table :
    tablesViolation [] [] [] [lawOf (.fin 0)] equals some .unpopulatedOutput
kernel_refl empty_law_refused :
    elaborate ⟨[], [], [], [lawOf (.fin 0)], [], [], none⟩ equals
      .error ⟨.residual .unpopulatedOutput, none, []⟩

-- A sequence of no element of a type without a value has a value: the table is accepted.
kernel_refl empty_sequence_law_table :
    tablesViolation [] [] [] [lawOf (.seq (.fin 0) (some 0))] equals none

/-! ## Two packages -/

/-- A package of one protocol of a prover, role 0, and a verifier, role 1, which returns
one `bool`, with the law of `bool`. -/
abbrev packageOf (body : Raw.ProtocolRegion) : Raw.Package :=
  ⟨[], [], [], [lawOf .bool], [], [⟨false, 2, [], [⟨.bool, 1⟩], [], body⟩], none⟩

/-- The prover samples a secret and sends it. The verifier draws a public coin. The prover
answers whether its secret is the coin. The verifier compares the answer with its own
comparison, stops `reject` when they differ, and returns that they agree. -/
abbrev honestRaw : Raw.Package :=
  packageOf <|
    .step (.sample 0 0 0 []) <|
    .step (.exchange 0 1 1 0) <|
    .step (.draw 1 [0] 2 0 []) <|
    .step (.at 0 (.builtin .boolEqual [0, 3])) <|
    .step (.exchange 0 1 3 4) <|
    .step (.at 1 (.builtin .boolEqual [1, 2])) <|
    .step (.at 1 (.builtin .boolEqual [5, 6])) <|
    .step (.at 1 (.guard .reject 7)) <|
    .ret [7]

/-- The verifier stops `reject` on a condition that is false. -/
abbrev rejectingRaw : Raw.Package :=
  packageOf <|
    .step (.at 1 (.literal (.bool false))) <|
    .step (.at 1 (.guard .reject 0)) <|
    .ret [0]

kernel_refl honest_elaborates : (elaborate honestRaw).isOk equals true
kernel_refl rejecting_elaborates : (elaborate rejectingRaw).isOk equals true

noncomputable def honestElaborated : Typed := Typed.ofRaw honestRaw honest_elaborates
noncomputable def rejectingElaborated : Typed := Typed.ofRaw rejectingRaw rejecting_elaborates

typed_literal honest := honestElaborated
typed_literal rejecting := rejectingElaborated

kernel_refl honest_eq : elaborate honestRaw equals Except.ok honest
kernel_refl rejecting_eq : elaborate rejectingRaw equals Except.ok rejecting

/-- The header of the protocol of both packages. -/
abbrev header : ProtocolHeader := ⟨2, [], [⟨.bool, 1⟩], .none, false⟩

abbrev honestEntry : Var honest.protocols header := ⟨0, rfl⟩
abbrev rejectingEntry : Var rejecting.protocols header := ⟨0, rfl⟩

/-- The side of the prover and the verifier. -/
abbrev both : Side := (single 0).union (single 1)

/-- The grouped meaning of the protocol of a package: its meaning for the side of both
roles. -/
noncomputable abbrev grouped (model : Model) (typed : Typed)
    (entry : Var typed.protocols header) :
    PIR.Process (Effects model) (Values (SideValue model both) header.outputs) :=
  (typed.program.protocols.table model (typed.program.functionTable model)
    Identities.written).get entry [] both .nil

/-! ## Completeness -/

/-- The verifier returns this result. -/
abbrev returned (model : Model) (result : Bool) :
    Values (SideValue model both) header.outputs → Prop :=
  fun outputs => Held.value (X := Bool) (both 1) rfl (outputs.get .here) = result

/-- Whether a process returns a result that `accepted` holds of on every coin, when the
laws of its draws and samples are `bool`: both coins are tried at each. A process that
sends, receives, stops or asks at another type does not. -/
def returnsOnEveryCoin {model : Model} {α : Type} (accepted : α → Bool) :
    Nat → PIR.Process (Effects model) α → Bool
  | _, .done value => accepted value
  | steps + 1, .call (.draw _ ⟨_, _, .bool, _⟩ _) next =>
      returnsOnEveryCoin accepted steps (next false) &&
        returnsOnEveryCoin accepted steps (next true)
  | steps + 1, .call (.sample _ ⟨_, _, .bool, _⟩ _) next =>
      returnsOnEveryCoin accepted steps (next false) &&
        returnsOnEveryCoin accepted steps (next true)
  | _, _ => false

/-- A process that returns an accepted result on every coin returns one for every sampler,
whatever the counters. -/
theorem returnsOnEveryCoin_sound {model : Model} {α : Type} (sampler : Sampler model)
    (accepted : α → Bool) :
    ∀ (steps : Nat) (process : PIR.Process (Effects model) α) (asked : Asked),
      returnsOnEveryCoin accepted steps process = true →
        ∃ value, ReturnsAlone sampler process asked value ∧ accepted value = true := by
  intro steps
  induction steps with
  | zero =>
      intro process asked holds
      cases process with
      | done value => exact ⟨value, .done value asked, holds⟩
      | halt reason => exact absurd holds Bool.false_ne_true
      | call effect next =>
          cases effect with
          | draw site law inputs =>
              obtain ⟨_, _, output, _⟩ := law
              cases output <;> exact absurd holds Bool.false_ne_true
          | sample site law inputs =>
              obtain ⟨_, _, output, _⟩ := law
              cases output <;> exact absurd holds Bool.false_ne_true
          | _ => exact absurd holds Bool.false_ne_true
  | succ steps ih =>
      intro process asked holds
      cases process with
      | done value => exact ⟨value, .done value asked, holds⟩
      | halt reason => exact absurd holds Bool.false_ne_true
      | call effect next =>
          cases effect with
          | send site type value => exact absurd holds Bool.false_ne_true
          | receive site type => exact absurd holds Bool.false_ne_true
          | read site type position => exact absurd holds Bool.false_ne_true
          | draw site law inputs =>
              obtain ⟨row, lawInputs, output, populated⟩ := law
              cases output with
              | bool =>
                  have both := Bool.and_eq_true_iff.mp holds
                  cases coin :
                      sampler.answer site (asked site) ⟨row, lawInputs, .bool, populated⟩ with
                  | false =>
                      obtain ⟨value, returns, accepts⟩ := ih (next false) (asked.next site) both.1
                      exact ⟨value, .draw _ _ _ _ _ _ (coin ▸ returns), accepts⟩
                  | true =>
                      obtain ⟨value, returns, accepts⟩ := ih (next true) (asked.next site) both.2
                      exact ⟨value, .draw _ _ _ _ _ _ (coin ▸ returns), accepts⟩
              | _ => exact absurd holds Bool.false_ne_true
          | sample site law inputs =>
              obtain ⟨row, lawInputs, output, populated⟩ := law
              cases output with
              | bool =>
                  have both := Bool.and_eq_true_iff.mp holds
                  cases coin :
                      sampler.answer site (asked site) ⟨row, lawInputs, .bool, populated⟩ with
                  | false =>
                      obtain ⟨value, returns, accepts⟩ := ih (next false) (asked.next site) both.1
                      exact ⟨value, .sample _ _ _ _ _ _ (coin ▸ returns), accepts⟩
                  | true =>
                      obtain ⟨value, returns, accepts⟩ := ih (next true) (asked.next site) both.2
                      exact ⟨value, .sample _ _ _ _ _ _ (coin ▸ returns), accepts⟩
              | _ => exact absurd holds Bool.false_ne_true

/-- A run of one process returns one value: the sampler and the counters determine it. -/
theorem ReturnsAlone.unique {model : Model} {sampler : Sampler model} {α : Type}
    {process : PIR.Process (Effects model) α} {asked : Asked} {first second : α}
    (returns : ReturnsAlone sampler process asked first)
    (again : ReturnsAlone sampler process asked second) : first = second := by
  induction returns with
  | done value asked => cases again; rfl
  | draw site law inputs next asked value _ ih =>
      cases again with | draw _ _ _ _ _ _ later => exact ih later
  | sample site law inputs next asked value _ ih =>
      cases again with | sample _ _ _ _ _ _ later => exact ih later

/-- Whether the verifier returns this result, as the kernel decides it. -/
abbrev isResult (model : Model) (result : Bool) :
    Values (SideValue model both) header.outputs → Bool :=
  fun outputs => decide (returned model result outputs)

/-- On every coin the honest package returns, the verifier `true`. -/
theorem honest_every_coin (model : Model) :
    returnsOnEveryCoin (isResult model true) 2 (grouped model honest honestEntry) = true :=
  kernel_rfl%

/-- On no coin does the verifier of the honest package return `false`. -/
theorem honest_never_false (model : Model) :
    returnsOnEveryCoin (isResult model false) 2 (grouped model honest honestEntry) = false :=
  kernel_rfl%

/-- The honest package is complete, with the verifier's `true` as the accepted result. -/
theorem honest_complete (model : Model) :
    GroupedComplete (grouped model honest honestEntry) (returned model true) := by
  intro sampler
  obtain ⟨outputs, returns, accepts⟩ :=
    returnsOnEveryCoin_sound sampler (isResult model true) 2 _ Asked.start (honest_every_coin model)
  exact ⟨outputs, returns, of_decide_eq_true accepts⟩

/-- The honest package is not complete with the verifier's `false` as the accepted result:
completeness is a condition on what the run returns. -/
theorem honest_not_complete_false (model : Model) :
    ¬ GroupedComplete (grouped model honest honestEntry) (returned model false) := by
  intro complete
  obtain ⟨outputs, returns, isFalse⟩ := complete (sampler model)
  obtain ⟨others, again, isTrue⟩ := honest_complete model (sampler model)
  have same := ReturnsAlone.unique returns again
  subst same
  exact Bool.noConfusion (isFalse.symm.trans isTrue)

/-- The grouped meaning of the rejecting package stops `reject`. -/
theorem rejecting_stops (model : Model) :
    grouped model rejecting rejectingEntry = .halt .reject := kernel_rfl%

/-- The rejecting package is not complete, even when every result is accepted: no run of it
returns. -/
theorem rejecting_not_complete (model : Model) :
    ¬ GroupedComplete (grouped model rejecting rejectingEntry) (fun _ => True) := by
  intro complete
  obtain ⟨outputs, returns, _⟩ := complete (sampler model)
  rw [rejecting_stops] at returns
  cases returns

/-! ## The endpoint lemma -/

/-- The value of a result that the kernel evaluates to one. -/
def okValue {ε α : Type} (result : Except ε α) (isOk : result.isOk = true) : α :=
  match result, isOk with
  | .ok value, _ => value

theorem okValue_eq {ε α : Type} (result : Except ε α) (isOk : result.isOk = true) :
    result = .ok (okValue result isOk) := by
  match result, isOk with
  | .ok value, _ => rfl

kernel_refl honest_projects : (projectProtocols honest.program.protocols).isOk equals true

/-- The role programs of the honest package. -/
noncomputable def honestRoles :
    Projected (honest.table.map (·.signature)) honest.functions honest.protocols :=
  okValue (projectProtocols honest.program.protocols) honest_projects

kernel_refl prover_named : (honestRoles.callees.find honestEntry 0).isSome equals true
kernel_refl verifier_named : (honestRoles.callees.find honestEntry 1).isSome equals true

/-- The endpoint lemma at the honest package and the sampler of a model: the grouped run
returns, so the programs of the prover and of the verifier, run against each other from an
empty mail and an empty board, return together what each holds of what the grouped run
returns, the verifier `true`. -/
theorem honest_endpoints (model : Model) :
    ∃ (prover : Var honestRoles.headers (roleHeader 0 header))
      (verifier : Var honestRoles.headers (roleHeader 1 header)),
      honestRoles.callees.find honestEntry 0 = some prover ∧
      honestRoles.callees.find honestEntry 1 = some verifier ∧
      ∃ outputs, returned model true outputs ∧
        ReturnTogether (sampler model)
          ((honestRoles.programs.table model (honest.program.functionTable model)
              Identities.written).get prover []
            (ownValues model (single 0) 0 (Side.single_inside 0) header.inputs
              (leftValues model (single 0) (single 1) .nil)))
          ((honestRoles.programs.table model (honest.program.functionTable model)
              Identities.written).get verifier []
            (ownValues model (single 1) 1 (Side.single_inside 1) header.inputs
              (rightValues model (single 0) (single 1) .nil)))
          Mail.empty Board.empty Heard.start Heard.start Asked.start
          (ownValues model (single 0) 0 (Side.single_inside 0) header.outputs
            (leftValues model (single 0) (single 1) outputs))
          (ownValues model (single 1) 1 (Side.single_inside 1) header.outputs
            (rightValues model (single 0) (single 1) outputs)) := by
  obtain ⟨prover, namedProver⟩ := Option.isSome_iff_exists.mp prover_named
  obtain ⟨verifier, namedVerifier⟩ := Option.isSome_iff_exists.mp verifier_named
  obtain ⟨outputs, returns, accepts⟩ := honest_complete model (sampler model)
  exact ⟨prover, verifier, namedProver, namedVerifier, outputs, accepts,
    program_endpoints_return (sampler model) (honest.program.functionTable model)
      (Functions.table_quiet honest.program.functions) Identities.written
      honest.program.protocols honestRoles (okValue_eq _ honest_projects)
      honestEntry (single 0) (single 1) single_disjoint 0 1 (Side.only_single 0 _)
      (Side.only_single 1 _) (Side.single_inside 0) (Side.single_inside 1) prover verifier
      namedProver namedVerifier [] .nil outputs Asked.start returns⟩

/-! ## What the statements about a program assume

The conditions that the statements of the package take of a program, a model and two
sides, at the honest package: each holds. -/

/-- The one-point model satisfies the domain laws of the table. -/
theorem honest_laws : Model.unit.DomainLaws (honest.table.map (·.signature)) :=
  Model.unit_domainLaws _

/-- The functions perform no effect. -/
theorem honest_quiet (model : Model) : QuietTable (honest.program.functionTable model) :=
  Functions.table_quiet honest.program.functions

/-- The ports of the protocol are held by its roles. -/
theorem honest_headers : HeadersLegal honest.protocols := honest.program.protocols.headersLegal

/-- The protocol does nothing for a side without any of its roles. -/
theorem honest_idle (model : Model) :
    CalleesIdle (honest.program.protocolTable model Identities.written) :=
  program_idle (honest.program.functionTable model) Identities.written honest.program.protocols

/-- The listeners of the protocol for the prover and the verifier are those of the protocol:
each of the two sides holds at most one of its roles. -/
theorem honest_listened :
    ((honest.program.protocols.listens
        (honest.program.protocols.listeners honestEntry [] (single 0) (single 1))
        Identities.written).get honestEntry) [] (single 0) (single 1) :=
  Protocols.entry_listened Identities.written honest.program.protocols honestEntry []
    (single 0) (single 1) (Side.only_single 0 _).atMostOne (Side.only_single 1 _).atMostOne

/-- The restriction law, for the sampler of a model and the listeners of the protocol for the
prover and the verifier. -/
theorem honest_together (model : Model) :
    TableTogether (sampler model)
      (honest.program.protocols.listeners honestEntry [] (single 0) (single 1))
      (honest.program.protocols.listens
        (honest.program.protocols.listeners honestEntry [] (single 0) (single 1))
        Identities.written)
      (honest.program.protocolTable model Identities.written) :=
  program_together (sampler model) _ (honest.program.functionTable model) (honest_quiet model)
    Identities.written honest.program.protocols

/-- The role programs denote the protocol's meaning for the side of each role. -/
theorem honest_roles_sound (model : Model) :
    CalleesSound model (honest.program.protocolTable model Identities.written)
      (honestRoles.programs.table model (honest.program.functionTable model) Identities.written)
      honestRoles.callees :=
  projectProtocols_sound Identities.written honest.program.protocols honestRoles
    (okValue_eq _ honest_projects)

/-! ## Completeness of a derived scheme -/

section Derived

variable (model : Model)

/-- The handler that lets every effect through and keeps its state. -/
def passing : PIR.StatefulInterpretation (Effects model) (Effects model) Unit :=
  fun effect state => .call effect fun reply => .done (reply, state)

/-- A prover that returns an empty proof at once. -/
abbrev proves : PIR.Process (Effects model) (Unit × Unit) := .done ((), ())

/-- A scheme whose verifier returns `true` is complete with `true` as the accepted
decision. -/
theorem accepting_derived_complete :
    DerivedComplete (proves model) (fun _ => (.done true : PIR.Process (Effects model) Bool))
      (· = true) :=
  fun _ => ⟨(), (), .done _ _, true, .done _ _, rfl⟩

/-- A scheme whose verifier stops `reject` is not complete, even when every decision is
accepted. -/
theorem rejecting_derived_not_complete :
    ¬ DerivedComplete (proves model)
      (fun _ => (.halt .reject : PIR.Process (Effects model) Bool)) (fun _ => True) := by
  intro complete
  obtain ⟨_, _, _, _, returns, _⟩ := complete (sampler model)
  cases returns

end Derived

#print axioms no_coin_at_every_type
#print axioms unit_coin_sequence
#print axioms returnsOnEveryCoin_sound
#print axioms honest_complete
#print axioms honest_not_complete_false
#print axioms rejecting_not_complete
#print axioms honest_endpoints
#print axioms honest_listened
#print axioms honest_together
#print axioms accepting_derived_complete
#print axioms rejecting_derived_not_complete

end Samplers
