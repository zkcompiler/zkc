import Zkc.Protocols.Sumcheck.LocalProver.Source
import Zkc.Source.Endpoint
import Zkc.Properties.Judgment

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.Sumcheck.LocalProver.Source
open PIR PIR.Properties

variable {F : Type} [Ring F] [DecidableEq F]

def inputCheck (p : Code) (inputs : List F) : Bool :=
  (Zkc.Protocols.Sumcheck.LocalProver.codeInputs p).all (fun i => decide (i < inputs.length))

omit [Ring F] [DecidableEq F] in
theorem inputCheck_iff (p : Code) (inputs : List F) :
    inputCheck p inputs = true ↔ ∀ i ∈ Zkc.Protocols.Sumcheck.LocalProver.codeInputs p, i < inputs.length := by
  simp [inputCheck, List.all_eq_true]

/-- A standalone local-code frontend; the five-capture setup constraint of
    the service/issuer adapter is not a requirement of local code itself. -/
def frontend : Frontend sig Unit (Cut F) where
  Source := Code
  Binding := List F
  inputs := fun p inputs _ => ∀ i ∈ Zkc.Protocols.Sumcheck.LocalProver.codeInputs p, i < inputs.length
  elaborate := fun p inputs _ =>
    if inputCheck p inputs then some (source p (initial inputs)) else none

def endpointContract (p : Code) (inputs : List F) : EndpointContract localInteraction (Cut F) :=
  ⟨(), calls p, fun out phase => Cut.inputs out = inputs ∧ phase = ()⟩

theorem checked_admitted (p : Code) (inputs : List F)
    (checked : inputCheck p inputs = true) :
    Admitted (frontend (F := F)) (endpointContract p inputs) p inputs () (source p (initial inputs)) := by
  refine ⟨?_, (inputCheck_iff p inputs).mp checked, source_conforms p (initial inputs), source_bound p (initial inputs), ?_⟩
  · simp [frontend, checked]
  · exact source_returns_inputs p (initial inputs)

variable {F S T E G O : Type} [Ring F] [DecidableEq F]

/-- Concrete formation produces the premise of the common endpoint judgment. -/
def formationJudgment (p : Code) : Conditional (List F)
    (fun inputs => Admitted (frontend (F := F)) (endpointContract p inputs)
      p inputs () (source p (initial inputs))) :=
  ⟨fun inputs => inputCheck p inputs = true, fun inputs h => checked_admitted p inputs h⟩

/-- The shared execution rule remains conditional on the actual backend/state
    relation. All subjects are the same source and captured vector. -/
def executionJudgment (p : Code) (R : S → T → Prop) (viewL : E → List O)
    (viewR : G → List O) (h : Handler sig S E) (g : Handler sig T G) (s : S) (t : T) :
    Conditional (List F) (fun inputs =>
      Admitted (frontend (F := F)) (endpointContract p inputs)
        p inputs () (source p (initial inputs)) →
      Related R viewL viewR ((source p (initial inputs)).run h s)
        ((source p (initial inputs)).run g t)) :=
  ⟨fun _ => HandlerRelated R viewL viewR h g ∧ R s t,
   fun inputs laws admitted => admitted_execution_related (frontend (F := F))
    (endpointContract p inputs) p inputs () _ _ admitted admitted
    R viewL viewR h g laws.1 s t laws.2⟩

theorem joined_requirements (p : Code) (R : S → T → Prop) (viewL : E → List O)
    (viewR : G → List O) (h : Handler sig S E) (g : Handler sig T G)
    (s : S) (t : T) (inputs : List F) :
    ((formationJudgment p).transport (executionJudgment p R viewL viewR h g s t)).requires inputs ↔
      inputCheck p inputs = true ∧ HandlerRelated R viewL viewR h g ∧ R s t := Iff.rfl


end Zkc.Protocols.Sumcheck.LocalProver.Source
