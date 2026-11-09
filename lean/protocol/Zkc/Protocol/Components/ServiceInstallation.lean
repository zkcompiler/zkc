module

public import Zkc.Protocol.Components.Representation
public import Zkc.Protocol.Internal.Interpretation

/-!
# Probabilistic installation across service interfaces

One source operation may be implemented by an entire target Process. The local joint kernel
must cover its complete returned or stopped outcome, state and accumulated observations.
The generic substitution theorem then covers every adaptive caller, including nested loops.
There is no reset of service state, no assumed independence, and no cryptographic loss.
-/

public section
open PIR PFunctor MeasureTheory ProbabilityTheory

namespace ProtocolProof
variable {E : Type} {I J : Signature} {S T L M A : Type}
  [∀ op, MeasurableSpace (I.Reply op)]
  [∀ op, Countable (I.Reply op)] [∀ op, MeasurableSingletonClass (I.Reply op)]
  [∀ op, MeasurableSpace (J.Reply op)]
  [∀ op, Countable (J.Reply op)] [∀ op, MeasurableSingletonClass (J.Reply op)]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace L] [MeasurableSpace M]
  [MeasurableSpace A]

namespace System

/-- Complete meanings of component bodies, retaining the caller's event prefix. -/
@[expose] noncomputable def implementedOperations (system : System E J T M)
    (implementation : OperationInterpretation I J) (environment : E) :
    KernelHandler (Internal.effects I) (T × List M) := fun operation ↦
  (system.runFrom environment (implementation operation)).map Execution.measurableEquiv

omit [∀ op, Countable (I.Reply op)] [∀ op, MeasurableSingletonClass (I.Reply op)] in
private theorem implementedOperations_eq (system : System E J T M)
    (implementation : OperationInterpretation I J) (environment : E) :
    system.implementedOperations implementation environment =
      fun operation ↦ FreeM.runKernel (system.accumulatedOperations environment)
        (Internal.encode (implementation operation)) := by
  funext operation
  unfold implementedOperations runFrom
  rw [← Kernel.map_comp_right _ Execution.measurableEquiv.symm.measurable
    Execution.measurableEquiv.measurable]
  simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply, Kernel.map_id']

/-- Kernel checking of a component body is reusable at every call site and nesting depth. -/
theorem run_interpret_backend (system : System E J T M)
    (implementation : OperationInterpretation I J) (environment : E)
    (client : Process I A) (current : T × List M) :
    FreeM.runKernel (system.accumulatedOperations environment)
      (Internal.encode (client.interpret implementation)) current =
    FreeM.runKernel (system.implementedOperations implementation environment)
      (Internal.encode client) current := by
  rw [Internal.encode_interpret, FreeM.runKernel_liftM, implementedOperations_eq]
  rfl

end System

/-- A local service installation relates one primitive to one fixed component body.
The joint operation law is reusable; it never asks for the whole client's requested theorem. -/
structure ServiceInstallation (source : System E I S L) (target : System E J T M)
    (implementation : OperationInterpretation I J) (admissible : E → Prop)
    (related : E → (S × List L) → (T × List M) → Prop) where
  operations : ∀ e, admissible e →
    KernelHandler.CouplingContract (source.accumulatedOperations e)
      (target.implementedOperations implementation e) (related e)
  initial : ∀ e, admissible e →
    ExpectationWP.CouplingPost (source.initialWithEvents e)
      (target.initialWithEvents e) (related e)

namespace ServiceInstallation
variable {source : System E I S L} {target : System E J T M}
  {implementation : OperationInterpretation I J} {admissible : E → Prop}
  {related : E → (S × List L) → (T × List M) → Prop}

/-- Install a deterministic representation from one complete local law per service operation.
The initial coverage equation concerns the whole law, not an admitted subpopulation. -/
noncomputable def ofMap [MeasurableEq (T × List M)]
    (source : System E I S L) (target : System E J T M)
    (implementation : OperationInterpretation I J) (admissible : E → Prop)
    (encode : (S × List L) → (T × List M)) (measurable : Measurable encode)
    (localLaw : ∀ e, admissible e → ∀ operation state,
      (source.accumulatedOperations e operation state).map (fun out ↦ (out.1, encode out.2)) =
        target.implementedOperations implementation e operation (encode state))
    (initialLaw : ∀ e, admissible e →
      (source.initialWithEvents e).map encode = target.initialWithEvents e) :
    ServiceInstallation source target implementation admissible (fun _ s t ↦ encode s = t) where
  operations e he := Internal.Representation.contractOfMap
    (source.accumulatedOperations e) (target.implementedOperations implementation e)
    encode measurable (localLaw e he)
  initial e he := Internal.Representation.initial_of_map_eq _ _ encode measurable (initialLaw e he)

/-- Transport any fixed measurable upper event through local service installation. -/
theorem event_le (installation : ServiceInstallation source target implementation admissible related)
    (client : E → Process I A) (left : Set (Execution S L A))
    (right : Set (Execution T M A)) (hl : MeasurableSet left) (hr : MeasurableSet right)
    (terminal : ∀ e, admissible e → ∀ outcome s t, related e s t →
      (⟨outcome, s.1, s.2⟩ : Execution S L A) ∈ left →
        (⟨outcome, t.1, t.2⟩ : Execution T M A) ∈ right)
    (e : E) (he : admissible e) :
    (source.experiment client).run e left ≤
      (target.experiment (fun e ↦ (client e).interpret implementation)).run e right := by
  change ((source.initialWithEvents e).bind (FreeM.runKernel _ _)).map
      Execution.measurableEquiv.symm left ≤
    ((target.initialWithEvents e).bind (FreeM.runKernel _ _)).map
      Execution.measurableEquiv.symm right
  rw [Measure.map_apply Execution.measurableEquiv.symm.measurable hl,
    Measure.map_apply Execution.measurableEquiv.symm.measurable hr]
  dsimp only [Internal.backendSystem]
  have equality := funext (target.run_interpret_backend implementation e (client e))
  rw [equality]
  exact Internal.Installation.event_le (installation.operations e he) (installation.initial e he)
    (Internal.encode (client e)) _ _
    (hl.preimage Execution.measurableEquiv.symm.measurable)
    (hr.preimage Execution.measurableEquiv.symm.measurable) (terminal e he)

/-- Completeness needs the reverse terminal implication over the same complete local coupling. -/
theorem event_ge (installation : ServiceInstallation source target implementation admissible related)
    (client : E → Process I A) (left : Set (Execution S L A))
    (right : Set (Execution T M A)) (hl : MeasurableSet left) (hr : MeasurableSet right)
    (terminal : ∀ e, admissible e → ∀ outcome s t, related e s t →
      (⟨outcome, t.1, t.2⟩ : Execution T M A) ∈ right →
        (⟨outcome, s.1, s.2⟩ : Execution S L A) ∈ left)
    (e : E) (he : admissible e) :
    (target.experiment (fun e ↦ (client e).interpret implementation)).run e right ≤
      (source.experiment client).run e left := by
  change ((target.initialWithEvents e).bind (FreeM.runKernel _ _)).map
      Execution.measurableEquiv.symm right ≤
    ((source.initialWithEvents e).bind (FreeM.runKernel _ _)).map
      Execution.measurableEquiv.symm left
  rw [Measure.map_apply Execution.measurableEquiv.symm.measurable hr,
    Measure.map_apply Execution.measurableEquiv.symm.measurable hl]
  dsimp only [Internal.backendSystem]
  have equality := funext (target.run_interpret_backend implementation e (client e))
  rw [equality]
  exact Internal.Installation.event_ge (installation.operations e he) (installation.initial e he)
    (Internal.encode (client e)) _ _
    (hl.preimage Execution.measurableEquiv.symm.measurable)
    (hr.preimage Execution.measurableEquiv.symm.measurable) (terminal e he)

/-- Exact observation agreement reuses the one installation for either property direction. -/
theorem event_eq (installation : ServiceInstallation source target implementation admissible related)
    (client : E → Process I A) (left : Set (Execution S L A))
    (right : Set (Execution T M A)) (hl : MeasurableSet left) (hr : MeasurableSet right)
    (terminal : ∀ e, admissible e → ∀ outcome s t, related e s t →
      ((⟨outcome, s.1, s.2⟩ : Execution S L A) ∈ left ↔
        (⟨outcome, t.1, t.2⟩ : Execution T M A) ∈ right))
    (e : E) (he : admissible e) :
    (source.experiment client).run e left =
      (target.experiment (fun e ↦ (client e).interpret implementation)).run e right :=
  le_antisymm
    (installation.event_le client left right hl hr
      (fun e he outcome s t h ↦ (terminal e he outcome s t h).mp) e he)
    (installation.event_ge client left right hl hr
      (fun e he outcome s t h ↦ (terminal e he outcome s t h).mpr) e he)

end ServiceInstallation
end ProtocolProof
