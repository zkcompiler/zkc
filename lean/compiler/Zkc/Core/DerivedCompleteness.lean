module

public import Zkc.Core.EndpointsCompleteness
public import Zkc.Core.ThreadCompose
public import Zkc.Core.ThreadEntryRules
public import Zkc.Core.ThreadRules

public section

/-! The role programs and the values of a derived scheme.

What the statements about a derived scheme (`Zkc.Core.DerivedScheme`) are stated with, and
the structural statements that relate a role program to the side of its role alone.

- `onlyValues_ownValues`: the values of the side of a role alone are determined by the
  values that the role holds. `single_disjoint_of_ne`, `oneTranscriptRole_prover`,
  `oneTranscriptRole_verifier`: the sides of two different roles are disjoint, and each
  holds exactly one of the two roles.
- `role_program_threads`: when the image of an entry, for the side of a role alone, is the
  entry interpreted by a handler between a start and a finish, the role program of the
  image is the role program of the entry interpreted by the same handler from the same
  start; its finish (`roleFinish`) is the side's finish on the role's values. It is an
  equation of processes and assumes the equation for the side, which
  `stepProtocols_entry` gives for a threading step.
- `proverShare`, `verifierShare`: what the prover and the verifier hold of the values of a
  run of the two roles together. `inputsWithoutProof`, `proofInputs`, `provedOutputs`: the
  inputs of the prover and of the verifier of a serialized entry, and the proof with the
  other outputs of its prover; a proof put before values is the proof that is read before
  them (`provedOutputs_proofInputs`).
- `serialize_prover_arguments`, `serialize_verifier_arguments` and the two for both steps:
  the entries of the two rules send the inputs of the derived role programs to the roles'
  shares of the inputs of the interactive run.
- `construct_steps`: a declaration whose pipeline has a result (`construct … = .ok …`)
  names a suite and a layout, its Fiat–Shamir step has a result, and the two steps are two
  equations of `stepProtocols` (`fiatShamir_steps`, `construct_serializes`); it names two
  different roles (`fiatShamir_roles_differ`).

Nothing is assumed beyond the equations in the statements. No statement here is about
completeness: those are in `Zkc.Core.DerivedScheme`.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## The values of the side of a role alone -/

section Values

variable {model : Model}

/-- A kept value, taken apart again. -/
theorem unkeep_consKept {type : Ty} {rest : List Ty} :
    ∀ (present : Bool) (held : Held (model.Value type) present) (values : Values model.Value rest),
      unkeep present (consKept present (fun member => Held.value present member held) values) =
        (held, values)
  | true, _, _ => rfl
  | false, _, _ => rfl

/-- Every tuple of values of the side of a role alone is made from the values that the
role holds. -/
theorem onlyValues_surjective (role : Nat) :
    ∀ (ports : List Located) (values : Values (SideValue model (single role)) ports),
      ∃ held : Values model.Value (own role ports), onlyValues model role ports held = values
  | [], .nil => ⟨.nil, rfl⟩
  | located :: rest, .cons value values => by
      obtain ⟨held, same⟩ := onlyValues_surjective role rest values
      refine ⟨consKept (Nat.beq located.holder role)
        (fun member => Held.value (Nat.beq located.holder role) member value) held, ?_⟩
      show Values.cons (ty := located)
          (unkeep (Nat.beq located.holder role)
            (consKept (Nat.beq located.holder role)
              (fun member => Held.value (Nat.beq located.holder role) member value) held)).1
          (onlyValues model role rest
            (unkeep (Nat.beq located.holder role)
              (consKept (Nat.beq located.holder role)
                (fun member => Held.value (Nat.beq located.holder role) member value) held)).2) =
        Values.cons value values
      rw [unkeep_consKept, same]

/-- The values of the side of a role alone are those made from the values that the role
holds of them. -/
theorem onlyValues_ownValues (role : Nat) (inside : single role role = true)
    (ports : List Located) (values : Values (SideValue model (single role)) ports) :
    onlyValues model role ports (ownValues model (single role) role inside ports values) =
      values := by
  obtain ⟨held, rfl⟩ := onlyValues_surjective role ports values
  exact congrArg (onlyValues model role ports) (ownValues_onlyValues model role ports held)

/-- Two different roles are disjoint sides. -/
theorem single_disjoint_of_ne {first second : Nat} (differ : first ≠ second) :
    (single first).Disjoint (single second) := by
  intro role
  show (Nat.beq role first && Nat.beq role second) = false
  cases inFirst : Nat.beq role first with
  | false => rfl
  | true =>
      cases inSecond : Nat.beq role second with
      | false => rfl
      | true =>
          exact absurd
            ((Nat.eq_of_beq_eq_true inFirst).symm.trans (Nat.eq_of_beq_eq_true inSecond)) differ

/-- The side of the prover alone holds exactly one transcript role when the verifier is
another role. -/
theorem oneTranscriptRole_prover {roles : TranscriptRoles}
    (differ : roles.prover ≠ roles.verifier) :
    OneTranscriptRole (single roles.prover roles.prover) (single roles.prover roles.verifier) :=
  .inl ⟨Nat.beq_refl _, by
    show Nat.beq roles.verifier roles.prover = false
    cases same : Nat.beq roles.verifier roles.prover with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true same).symm differ⟩

/-- The side of the verifier alone holds exactly one transcript role when the prover is
another role. -/
theorem oneTranscriptRole_verifier {roles : TranscriptRoles}
    (differ : roles.prover ≠ roles.verifier) :
    OneTranscriptRole (single roles.verifier roles.prover) (single roles.verifier roles.verifier) :=
  .inr ⟨by
    show Nat.beq roles.prover roles.verifier = false
    cases same : Nat.beq roles.prover roles.verifier with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true same) differ, Nat.beq_refl _⟩

end Values

/-! ## Role programs -/

section Roles

variable {model : Model}

/-- What the program of a role does after its interactive program, from what the side of
the role alone does: the side's finish on the role's values, and the role's values of its
result. -/
@[expose] def roleFinish (model : Model) (role : Nat) {outputs later : List Located} {state : Type}
    (finish : Values (SideValue model (single role)) outputs × state →
      PIR.Process (Effects model) (Values (SideValue model (single role)) later))
    (result : Values model.Value (own role outputs) × state) :
    PIR.Process (Effects model) (Values model.Value (own role later)) :=
  (finish (onlyValues model role outputs result.1, result.2)).bind fun values =>
    .done (ownValues model (single role) role (Side.single_inside role) later values)

/-- The role program of an image that threads is the role program of the entry, threaded.
`table` and `called` are the meanings of the protocols and of the role programs of the
interactive program, `laterTable` and `laterCalled` those of the later one. When the image
of the entry, for the side of the role alone on the role's inputs, is the entry interpreted
by a handler between a start and a finish, the role program of the image on those inputs is
the role program of the entry interpreted by the same handler from the same start. -/
theorem role_program_threads {old new : List ProtocolHeader}
    {programs laterPrograms : List RoleHeader}
    {table : ProtocolTable model old} {called : RoleTable model programs}
    {callees : ProjectedCallees old programs} (sound : CalleesSound model table called callees)
    {laterTable : ProtocolTable model new} {laterCalled : RoleTable model laterPrograms}
    {laterCallees : ProjectedCallees new laterPrograms}
    (laterSound : CalleesSound model laterTable laterCalled laterCallees)
    {header later : ProtocolHeader} (entry : Var old header) (image : Var new later) (role : Nat)
    (program : Var programs (roleHeader role header))
    (named : callees.find entry role = some program)
    (laterProgram : Var laterPrograms (roleHeader role later))
    (laterNamed : laterCallees.find image role = some laterProgram) (path : List Nat)
    (inputs : Values model.Value (own role later.inputs))
    (arguments : Values (SideValue model (single role)) header.inputs) {state : Type}
    (handler : PIR.StatefulInterpretation (Effects model) (Effects model) state)
    (start : PIR.Process (Effects model) state)
    (finish : Values (SideValue model (single role)) header.outputs × state →
      PIR.Process (Effects model) (Values (SideValue model (single role)) later.outputs))
    (threads : laterTable.get image path (single role)
        (onlyValues model role later.inputs inputs) =
      threadedProgram handler start (table.get entry path (single role) arguments) finish) :
    laterCalled.get laterProgram path inputs =
      threadedProgram handler start
        (called.get program path
          (ownValues model (single role) role (Side.single_inside role) header.inputs arguments))
        (roleFinish model role finish) := by
  have imageMeaning := laterSound.program image role laterProgram laterNamed path (single role)
    (Side.only_single role later.roles) (Side.single_inside role)
    (onlyValues model role later.inputs inputs)
  rw [ownValues_onlyValues] at imageMeaning
  rw [imageMeaning, threads, sound.program entry role program named path (single role)
    (Side.only_single role header.roles) (Side.single_inside role) arguments,
    threadedProgram_bind]
  unfold threadedProgram
  congr 1
  funext first
  rw [PIR.Process.interpretWith_bind, PIR.Process.bind_assoc]
  congr 1
  funext result
  show _ = roleFinish model role finish (_, result.2)
  unfold roleFinish
  rw [onlyValues_ownValues]

end Roles

/-! ## The shares of the two transcript roles -/

section Shares

/-- The prover's share of the values of a grouped run of the two transcript roles: the
values that the prover holds. -/
@[expose, reducible] def proverShare (model : Model) (roles : TranscriptRoles)
    {ports : List Located}
    (values : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      ports) :
    Values model.Value (own roles.prover ports) :=
  ownValues model (single roles.prover) roles.prover (Side.single_inside roles.prover) ports
    (leftValues model (single roles.prover) (single roles.verifier) values)

/-- The verifier's share of the values of a grouped run of the two transcript roles: the
values that the verifier holds. -/
@[expose, reducible] def verifierShare (model : Model) (roles : TranscriptRoles)
    {ports : List Located}
    (values : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      ports) :
    Values model.Value (own roles.verifier ports) :=
  ownValues model (single roles.verifier) roles.verifier (Side.single_inside roles.verifier) ports
    (rightValues model (single roles.prover) (single roles.verifier) values)

end Shares

/-! ## The values of the two roles of a serialized entry -/

section Serialize

-- A hypothesis that only the pattern match uses is named for what it says.
set_option linter.unusedVariables false

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {functionTable : FunctionTable model functions}

/-- The proof and the other outputs of the prover of a serialized entry: the proof is the
first output. -/
@[expose] def provedOutputs (model : Model) (role : Nat) {proof : Ty} {rest : List Located}
    (outputs : Values model.Value (own role (⟨proof, role⟩ :: rest))) :
    model.Value proof × Values model.Value (own role rest) :=
  (Held.value (Nat.beq role role) (Nat.beq_refl role) (unkeep (Nat.beq role role) outputs).1,
    (unkeep (Nat.beq role role) outputs).2)

/-- The inputs of the verifier of a serialized entry: the proof, then the other inputs. -/
@[expose] def proofInputs (model : Model) (role : Nat) {proof : Ty} {rest : List Located}
    (value : model.Value proof) (inputs : Values model.Value (own role rest)) :
    Values model.Value (own role (⟨proof, role⟩ :: rest)) :=
  consKept (Nat.beq role role) (fun _ => value) inputs

/-- The inputs of the prover of a serialized entry. The proof is an input of the verifier,
which is another role, so the prover's inputs are its inputs of the entry before the
step. -/
@[expose] def inputsWithoutProof (model : Model) {prover verifier : Nat}
    (differ : prover ≠ verifier) {proof : Ty} {rest : List Located}
    (inputs : Values model.Value (own prover rest)) :
    Values model.Value (own prover (⟨proof, verifier⟩ :: rest)) :=
  consKept (Nat.beq verifier prover)
    (fun member => absurd (Nat.eq_of_beq_eq_true member).symm differ) inputs

/-- A proof put before values is the proof that is read before them. -/
theorem provedOutputs_proofInputs (role : Nat) {proof : Ty} {rest : List Located}
    (value : model.Value proof) (values : Values model.Value (own role rest)) :
    provedOutputs model role (proofInputs model role value values) = (value, values) := by
  unfold provedOutputs proofInputs
  have taken := unkeep_consKept (model := model) (Nat.beq role role)
    (Held.of (Nat.beq role role) value) values
  have same : (fun _ : Nat.beq role role = true => value) =
      fun member => Held.value (Nat.beq role role) member (Held.of (Nat.beq role role) value) := by
    funext member
    generalize Nat.beq role role = present at member
    subst member
    rfl
  rw [same, taken]
  generalize Nat.beq_refl role = member
  generalize Nat.beq role role = present at member
  subst member
  rfl

/-- A value that is not kept leaves the values after it. -/
theorem unkeep_consKept_absent {type : Ty} {rest : List Ty} :
    ∀ (present : Bool) (absent : present = false) (value : present = true → model.Value type)
      (values : Values model.Value rest),
      (unkeep present (consKept present value values)).2 = values
  | false, _, _, _ => rfl

/-- The entry of the serialize step sends the inputs of the derived prover to the prover's
share of the inputs of the grouped run: it drops the proof, which the prover does not
hold. -/
theorem serialize_prover_arguments (layout : Layout operations) (roles : TranscriptRoles)
    (differ : roles.prover ≠ roles.verifier) (header : ProtocolHeader)
    (inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      header.inputs) :
    (serializeEntry (functions := functions) layout).arguments (single roles.prover) roles header
        (onlyValues model roles.prover (⟨layout.proof, roles.verifier⟩ :: header.inputs)
          (inputsWithoutProof model differ (proverShare model roles inputs))) =
      leftValues model (single roles.prover) (single roles.verifier) inputs := by
  have absent : Nat.beq roles.verifier roles.prover = false := by
    cases same : Nat.beq roles.verifier roles.prover with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true same).symm differ
  show onlyValues model roles.prover header.inputs
      (unkeep (Nat.beq roles.verifier roles.prover)
        (inputsWithoutProof model differ (proverShare model roles inputs))).2 = _
  unfold inputsWithoutProof
  rw [unkeep_consKept_absent _ absent, onlyValues_ownValues]

/-- The entry of the serialize step sends the inputs of the derived verifier, the proof
before its share of the inputs of the grouped run, to that share: it drops the proof. -/
theorem serialize_verifier_arguments (layout : Layout operations) (roles : TranscriptRoles)
    (header : ProtocolHeader)
    (inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      header.inputs)
    (proof : model.Value layout.proof) :
    (serializeEntry (functions := functions) layout).arguments (single roles.verifier) roles
        header
        (onlyValues model roles.verifier (⟨layout.proof, roles.verifier⟩ :: header.inputs)
          (proofInputs model roles.verifier proof (verifierShare model roles inputs))) =
      rightValues model (single roles.prover) (single roles.verifier) inputs := by
  show onlyValues model roles.verifier header.inputs
      (unkeep (Nat.beq roles.verifier roles.verifier)
        (proofInputs model roles.verifier proof (verifierShare model roles inputs))).2 = _
  have taken : (unkeep (Nat.beq roles.verifier roles.verifier)
      (proofInputs model roles.verifier proof (verifierShare model roles inputs))).2 =
      verifierShare model roles inputs :=
    congrArg Prod.snd (provedOutputs_proofInputs (model := model) roles.verifier proof _)
  rw [taken, onlyValues_ownValues]

/-- The entries of the Fiat–Shamir step and of the serialize step together send the inputs
of the derived prover to the prover's share of the inputs of the grouped run: the entry of
the Fiat–Shamir step keeps its inputs. -/
theorem fiatShamir_serialize_prover_arguments (suite : Suite operations functions)
    (layout : Layout operations) (roles : TranscriptRoles)
    (differ : roles.prover ≠ roles.verifier) (header : ProtocolHeader)
    (inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      header.inputs) :
    composedArguments (fiatShamirEntry suite functionTable) (serializeEntry layout)
        (single roles.prover) roles header
        (onlyValues model roles.prover (⟨layout.proof, roles.verifier⟩ :: header.inputs)
          (inputsWithoutProof model differ (proverShare model roles inputs))) =
      leftValues model (single roles.prover) (single roles.verifier) inputs :=
  serialize_prover_arguments (functions := functions) layout roles differ header inputs

/-- The entries of the Fiat–Shamir step and of the serialize step together send the inputs
of the derived verifier to the verifier's share of the inputs of the grouped run. -/
theorem fiatShamir_serialize_verifier_arguments (suite : Suite operations functions)
    (layout : Layout operations) (roles : TranscriptRoles) (header : ProtocolHeader)
    (inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      header.inputs)
    (proof : model.Value layout.proof) :
    composedArguments (fiatShamirEntry suite functionTable) (serializeEntry layout)
        (single roles.verifier) roles header
        (onlyValues model roles.verifier (⟨layout.proof, roles.verifier⟩ :: header.inputs)
          (proofInputs model roles.verifier proof (verifierShare model roles inputs))) =
      rightValues model (single roles.prover) (single roles.verifier) inputs :=
  serialize_verifier_arguments (functions := functions) layout roles header inputs proof

end Serialize

/-! ## The pipeline of a declaration -/

section Construct

/-- The transcript roles that a declaration names. -/
@[expose, reducible] def Raw.Declaration.roles (declaration : Raw.Declaration) : TranscriptRoles :=
  ⟨declaration.prover, declaration.verifier⟩

/-- What the Fiat–Shamir step of a declaration computed: the step of the Fiat–Shamir rule
of the declared suite on the protocols of the package, with the declared entry, the
declared roles and the identities of a program as written. -/
theorem fiatShamir_steps (typed : Typed) (declaration : Raw.Declaration)
    (suite : Suite (typed.table.map (·.signature)) typed.functions)
    (isSuite : declaration.suite.map
        (Suite.ofRaw (tableScope (typed.table.map (·.signature))) (tableScope typed.functions)) =
      some suite)
    (once : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (derives : fiatShamir typed declaration = .ok once) :
    stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) Identities.written
        declaration.entry declaration.roles typed.program.protocols = .ok once := by
  cases found : declaration.suite with
  | none =>
      rw [found] at isSuite
      cases isSuite
  | some raw =>
      rw [found] at isSuite
      have same := Option.some.inj isSuite
      subst same
      unfold fiatShamir at derives
      rw [found] at derives
      dsimp only at derives
      split at derives
      · cases derives
      · exact derives

/-- What the serialize step of a declaration computed: the step of the serialize rule of
the declared layout on the result of the Fiat–Shamir step, with its newest protocol as the
entry and the identities that the Fiat–Shamir step left. -/
theorem construct_serializes (typed : Typed) (declaration : Raw.Declaration)
    (layout : Layout (typed.table.map (·.signature)))
    (isLayout : declaration.layout.bind
        (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout)
    (once : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (derives : fiatShamir typed declaration = .ok once)
    (serialized : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (constructs : construct typed declaration = .ok serialized) :
    stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) once.identities
        (once.headers.length - 1) declaration.roles once.protocols = .ok serialized := by
  unfold construct at constructs
  rw [derives] at constructs
  dsimp only at constructs
  unfold serializeProtocols at constructs
  rw [isLayout] at constructs
  exact constructs

/-- A declaration whose pipeline has a result names a suite and a layout, its Fiat–Shamir
step has a result, and the two steps are these: `construct … = .ok …` unfolds to the two
equations of `stepProtocols`. -/
theorem construct_steps (typed : Typed) (declaration : Raw.Declaration)
    (serialized : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (constructs : construct typed declaration = .ok serialized) :
    ∃ (suite : Suite (typed.table.map (·.signature)) typed.functions)
      (layout : Layout (typed.table.map (·.signature)))
      (once : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions),
      declaration.suite.map
          (Suite.ofRaw (tableScope (typed.table.map (·.signature)))
            (tableScope typed.functions)) = some suite ∧
        declaration.layout.bind
          (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout ∧
        fiatShamir typed declaration = .ok once ∧
        stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) Identities.written
          declaration.entry declaration.roles typed.program.protocols = .ok once ∧
        stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) once.identities
          (once.headers.length - 1) declaration.roles once.protocols = .ok serialized := by
  cases derives : fiatShamir typed declaration with
  | error refusal =>
      unfold construct at constructs
      rw [derives] at constructs
      cases constructs
  | ok once =>
      cases found : declaration.suite with
      | none =>
          unfold fiatShamir at derives
          rw [found] at derives
          cases derives
      | some raw =>
          cases laid : declaration.layout.bind
              (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) with
          | none =>
              unfold construct at constructs
              rw [derives] at constructs
              dsimp only at constructs
              unfold serializeProtocols at constructs
              rw [laid] at constructs
              cases constructs
          | some layout =>
              have isSuite : declaration.suite.map
                  (Suite.ofRaw (tableScope (typed.table.map (·.signature)))
                    (tableScope typed.functions)) =
                  some (Suite.ofRaw (tableScope (typed.table.map (·.signature)))
                    (tableScope typed.functions) raw) := by
                rw [found]
                rfl
              exact ⟨Suite.ofRaw (tableScope (typed.table.map (·.signature)))
                  (tableScope typed.functions) raw, layout, once, rfl, rfl, rfl,
                fiatShamir_steps typed declaration _ isSuite once derives,
                construct_serializes typed declaration layout laid once derives serialized
                  constructs⟩

/-- A declaration whose Fiat–Shamir step has a result names two different roles. -/
theorem fiatShamir_roles_differ (typed : Typed) (declaration : Raw.Declaration)
    (once : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (derives : fiatShamir typed declaration = .ok once) :
    declaration.roles.prover ≠ declaration.roles.verifier := by
  cases found : declaration.suite with
  | none =>
      unfold fiatShamir at derives
      rw [found] at derives
      cases derives
  | some raw =>
      exact stepProtocols_roles_differ Identities.written declaration.entry declaration.roles
        typed.program.protocols once
        (fiatShamir_steps typed declaration _ (by rw [found]; rfl) once derives)

end Construct

end Zkc.Core
