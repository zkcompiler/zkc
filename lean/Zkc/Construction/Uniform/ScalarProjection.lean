module

public import Zkc.Construction.Uniform.LoopedSourceProcess
public import Zkc.Construction.ScalarVerifier

@[expose] public section

/-! A derived presentation under the artifact-fixed scalar key map. The nominal
process and its complete histories remain the execution authority. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.ScalarProjection
open Zkc.Source
open DomainAdapter
variable {F G A R : Type}

def iterations (artifact : Participant) : Bool :=
  artifact.instructions.any fun instruction => match instruction.operation with
    | .loop .. => true | _ => false

def key (repeated : Bool) (origin : Origin) : Origin :=
  { origin with event := if repeated then origin.withoutCoordinates.event else origin.event }

theorem key_eq (repeated : Bool) (origin : Origin) :
    key repeated origin = if repeated then origin.withoutCoordinates else origin := by
  cases repeated <;> rfl

theorem key_artifact (artifact : Participant) : key (iterations artifact) = ScalarVerifier.origin artifact := by
  funext origin
  rw [key_eq]
  rfl

def event {carriers : Structured.Carriers} (repeated : Bool) : Domain.Event carriers → Domain.Event carriers
  | .message origin payload => .message (key repeated origin) payload
  | .challenge origin => .challenge (key repeated origin)
  | .publicBinding row => .publicBinding row

def history {carriers : Structured.Carriers} (repeated : Bool)
    (events : Domain.History carriers) : Domain.History carriers := events.map (event repeated)

def operations {carriers : Structured.Carriers} (repeated : Bool) :
    PIR.OperationInterpretation (Domain.effects carriers) (Domain.effects carriers)
  | .checkpoint _ => .done ()
  | .observe observed => .call (.observe (event repeated observed)) .done
  | .query events origin => .call (.query (history repeated events) (key repeated origin)) .done
  | .localService port origin => .call (.localService port (key repeated origin)) .done
  | operation => .call operation .done

section Handler
variable {m : Type → Type} [Monad m]

/-- The key projection precedes the existing oracle, including its cache and
opaque history prefix. No nominal history or physical frame is rewritten. -/
theorem runK_operations (repeated : Bool)
    (initial : History F G) (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (next : A → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK SourceProcess.legacyOrigin initial challenge (process.interpret (operations repeated)) proof next =
      runK (key repeated) initial challenge process proof next := by
  cases repeated with
  | true => exact LoopedSourceProcess.runK_operations initial challenge process proof next
  | false =>
      have same : operations (carriers := Structured.uniformCarriers F G) false =
          Original.forgetCheckpoints := by
        funext operation
        cases operation <;> try rfl
        case observe observed => cases observed <;> rfl
        case query events origin =>
          have identity : history (carriers := Structured.uniformCarriers F G) false events = events := by
            induction events with
            | nil => rfl
            | cons head tail ih => cases head <;> simp_all [history, event, key]
          change PIR.Process.call (I := Domain.effects (Structured.uniformCarriers F G))
            (.query (history false events) origin) PIR.Process.done =
            PIR.Process.call (I := Domain.effects (Structured.uniformCarriers F G))
              (.query events origin) PIR.Process.done
          rw [identity]
      rw [same]
      exact runK_forgetCheckpoints SourceProcess.legacyOrigin initial challenge process proof next

end Handler
end Zkc.Construction.Uniform.ScalarProjection
