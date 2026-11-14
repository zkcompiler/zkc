import Zkc.Tests.Core.Samplers
import Zkc.Core.DerivedCompleteness

/-! Two handlers in sequence are one handler, and the role program of an image that threads
is the role program of the entry, threaded.

- A handler that performs every effect twice and counts the effects it handled, followed
  by a handler that counts: on a process of one effect the first counts one and the second
  two. The composed handler reaches the same counts from the pair of the two states, and
  the law of composition relates the two interpretations.
- A process that starts, interprets a source and finishes, interpreted by a second handler
  that passes its start and its finish, is the source interpreted by the composed handler.
- The structural equation of a role program has an instance: at the honest package of
  `Samplers`, for the handler that lets every effect through, the program of the prover is
  itself interpreted by that handler from a start and followed by a finish without an
  effect.
- A proof put before the values of a role is the proof that is read before them, and a
  prover that is not the verifier holds no proof among its inputs.
- The axioms of every public theorem of `Zkc.Core.EndpointsCompleteness`,
  `Zkc.Core.ThreadCompose` and `Zkc.Core.DerivedCompleteness`.

The statements about completeness of a derived scheme are checked in
`Tests/Core/DerivedScheme.lean`.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core
open Samplers (passing proves honest honestRoles honestEntry header)

namespace DerivedCompleteness

section Handlers

variable (model : Model)

/-- The handler that performs every effect and counts the effects it handled. -/
def counting : PIR.StatefulInterpretation (Effects model) (Effects model) Nat :=
  fun effect count => .call effect fun reply => .done (reply, count + 1)

/-- The handler that performs every effect twice, keeps the second reply and counts the
effects it handled. -/
def doubling : PIR.StatefulInterpretation (Effects model) (Effects model) Nat :=
  fun effect count => .call effect fun _ => .call effect fun reply => .done (reply, count + 1)

/-- A process of one effect: it receives a value and returns it. -/
def receives : PIR.Process (Effects model) (model.Value .bool) :=
  .call (.receive ⟨[], 0, 0⟩ .bool) .done

/-- What both interpretations perform: the effect twice. -/
def receivesTwice {α : Type} (pack : model.Value .bool → α) : PIR.Process (Effects model) α :=
  .call (.receive ⟨[], 0, 0⟩ .bool) fun _ =>
    .call (.receive ⟨[], 0, 0⟩ .bool) fun reply => .done (pack reply)

/-- One handler after the other: the first handled one effect, the second two. -/
theorem doubling_then_counting :
    ((receives model).interpretWith (doubling model) 0).interpretWith (counting model) 10 =
      receivesTwice model fun reply => ((reply, 1), 12) :=
  rfl

/-- The composed handler reaches the same counts from the pair of the two states. -/
theorem composed_counts :
    (receives model).interpretWith (PIR.composeHandlers (doubling model) (counting model))
        (0, 10) =
      receivesTwice model fun reply => (reply, (1, 12)) :=
  rfl

/-- The law of composition at these handlers. -/
theorem composed_law :
    ((receives model).interpretWith (doubling model) 0).interpretWith (counting model) 10 =
      ((receives model).interpretWith (PIR.composeHandlers (doubling model) (counting model))
        (0, 10)).bind fun result => .done ((result.1, result.2.1), result.2.2) :=
  PIR.Process.interpretWith_interpretWith (doubling model) (counting model) (receives model) 0 10

/-- A start and a finish without an effect are passed by the second handler: the program
that starts from a count, interprets the source by the first handler and returns the
count, interpreted by the second handler, is the source under the composed handler. -/
theorem threaded_then_counting :
    ((PIR.Process.done 0 : PIR.Process (Effects model) Nat).bind fun count =>
        ((receives model).interpretWith (doubling model) count).bind fun result =>
          (.done result.2 : PIR.Process (Effects model) Nat)).interpretWith (counting model) 10 =
      (PIR.Process.done 0 : PIR.Process (Effects model) Nat).bind fun count =>
        ((receives model).interpretWith (PIR.composeHandlers (doubling model) (counting model))
          (count, 10)).bind fun result =>
          (PIR.Process.done result.2.1 : PIR.Process (Effects model) Nat).bind fun value =>
            .done (value, result.2.2) :=
  PIR.Process.interpretWith_threadedProcess (doubling model) (counting model) (.done 0)
    (receives model) (fun result => .done result.2) (PIR.Passes.done _ _)
    (fun _ => PIR.Passes.done _ _) 10

end Handlers

section Roles

variable (model : Model)

/-- The handler that lets every effect through passes every process. -/
theorem passing_passes {α : Type} (source : PIR.Process (Effects model) α) :
    PIR.Passes (passing model) source := by
  intro state
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op next ih =>
      simp only [PIR.Process.interpretWith, passing, PIR.Process.bind]
      congr 1
      funext reply
      exact ih reply

/-- A process interpreted by the handler that lets every effect through, from a start and
with a finish that do nothing, is the process. -/
theorem threaded_passing {α : Type} (source : PIR.Process (Effects model) α) :
    threadedProgram (passing model) (.done ()) source (fun result => .done result.1) = source := by
  unfold threadedProgram
  rw [PIR.Process.done_bind, passing_passes model source (), PIR.Process.bind_assoc]
  exact PIR.Process.bind_done source

/-- The structural equation of a role program at the honest package: the program of the
prover is itself interpreted by the handler that lets every effect through. The premise of
`role_program_threads`, that the entry for the side of the prover alone is the entry under
the handler, holds there. -/
theorem honest_prover_threads :
    ∃ prover : Var honestRoles.headers (roleHeader 0 header),
      honestRoles.callees.find honestEntry 0 = some prover ∧
      (honestRoles.programs.table model (honest.program.functionTable model)
          Identities.written).get prover [] .nil =
        threadedProgram (passing model) (.done ())
          ((honestRoles.programs.table model (honest.program.functionTable model)
              Identities.written).get prover []
            (ownValues model (single 0) 0 (Side.single_inside 0) header.inputs .nil))
          (roleFinish model 0 fun result => .done result.1) := by
  obtain ⟨prover, named⟩ := Option.isSome_iff_exists.mp Samplers.prover_named
  exact ⟨prover, named,
    role_program_threads (Samplers.honest_roles_sound model) (Samplers.honest_roles_sound model)
      honestEntry honestEntry 0 prover named prover named [] .nil .nil (passing model) (.done ())
      (fun result => .done result.1) (threaded_passing model _).symm⟩

/-- A proof put before the values of a role is the proof that is read before them. -/
theorem proof_read_back (role : Nat) (proof : model.Value .bool) :
    provedOutputs model role (proofInputs model role (rest := []) proof .nil) = (proof, .nil) :=
  provedOutputs_proofInputs (rest := []) role proof .nil

/-- A prover, role 0, that is not the verifier, role 1, holds no proof among the inputs of
a serialized entry: its inputs of the serialized entry are its inputs of the entry before
the step. -/
theorem prover_holds_no_proof (ports : List Located) (differ : (0 : Nat) ≠ 1)
    (inputs : Values model.Value (own 0 ports)) :
    inputsWithoutProof model (verifier := 1) (proof := .bool) differ inputs = inputs :=
  rfl

end Roles

#print axioms doubling_then_counting
#print axioms composed_law
#print axioms threaded_then_counting
#print axioms honest_prover_threads
#print axioms proof_read_back
#print axioms prover_holds_no_proof

end DerivedCompleteness

/-! ## Axioms of the library theorems -/

section Axioms

open Zkc.Core

-- `Zkc.Core.EndpointsCompleteness`
#print axioms threadedProgram_bind

-- `Zkc.Core.ThreadProgram`: what the derivation takes from the driver of a step
#print axioms rewriteProtocols_declared_origin
#print axioms rewriteProtocols_newest
#print axioms stepProtocols_newest

-- `Zkc.Core.ThreadCompose`
#print axioms PIR.Process.interpretWith_threadedProcess
#print axioms composedStart_quiet
#print axioms composedFinish_quiet
#print axioms Stepped.rewroteEntry_newest
#print axioms stepProtocols_copied_newest
#print axioms stepProtocols_idle_rewroteEntry
#print axioms stepProtocols_has_newest
#print axioms stepProtocols_idle_after
#print axioms stepProtocols_entry_rewritten
#print axioms stepProtocols_entry_copied
#print axioms stepProtocols_twice_entry
#print axioms stepProtocols_plain_then_entry
#print axioms stepProtocols_roles_differ

-- `Zkc.Core.DerivedCompleteness`
#print axioms unkeep_consKept
#print axioms onlyValues_surjective
#print axioms onlyValues_ownValues
#print axioms single_disjoint_of_ne
#print axioms oneTranscriptRole_prover
#print axioms oneTranscriptRole_verifier
#print axioms role_program_threads
#print axioms provedOutputs_proofInputs
#print axioms unkeep_consKept_absent
#print axioms serialize_prover_arguments
#print axioms serialize_verifier_arguments
#print axioms fiatShamir_serialize_prover_arguments
#print axioms fiatShamir_serialize_verifier_arguments
#print axioms fiatShamir_steps
#print axioms construct_serializes
#print axioms construct_steps
#print axioms fiatShamir_roles_differ

end Axioms
