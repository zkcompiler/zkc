module

public import Zkc.Source.Structured.OracleProcess
public import Zkc.Source.Structured.OracleProtocol

@[expose] public section

/-! Free presentation of retained-body expansion, decreasing on the immutable older prefix.
Bodies remain `CheckedOracle.denote`, hence the checked source's `Region.denote`.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess

abbrev External (model : DomainModel) :=
  PIR.Signature.sum (participantInterfaceOn model.toCarriers)
    (oracleReadInterface model.toCarriers)

abbrev Interface (model : DomainModel) (S E : Type) := Effect (External model) S E

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

def externalHandler
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) :
    PIR.Handler (External model) S E
  | .inl action => ordinary action
  | .inr request => base request

/-- Only this leaf requests a base provider execution. Local table data is never sampled. -/
def baseCall (request : OracleRead) (state : S) :
    PIR.Process (Interface model S E) (PIR.Execution S E (model.Value request.kind.answer)) :=
  .call (.inr request, state) .done

/-- A semantic view of `OracleStore.answer`, with exactly the same structural recursion. -/
def answer (model : DomainModel) (self : Nat) :
    OracleEntries model snapshot domains math → (request : OracleRead) → (S × Nat) →
      PIR.Process (Interface model S E)
        (PIR.Execution (S × Nat) (OracleEvent E) (model.Value request.kind.answer))
  | [], request, state =>
      .done ⟨.stopped .refused, (state.1, state.2 + 1), [.query request]⟩
  | ⟨row, table⟩ :: older, request, state =>
    if equal : row = request.kind.answer then
      if table.anchor = request.anchor then
        let state := (state.1, state.2 + 1)
        if !OracleStore.visible self table.holder table.receivers ||
            !OracleStore.validRows request.kind table.rows || request.position ≥ table.rows then
          .done ⟨.stopped .refused, state, [.query request]⟩
        else match table.payload with
        | .base _ =>
          mapResult (fun result ↦ ⟨result.outcome, (result.state, state.2),
            .query request :: result.events.map OracleEvent.provider⟩) (baseCall request state.1)
        | .virtual checked answerType captures =>
          if inputShape : checked.declaration.inputs =
              checked.declaration.inputs.dropLast ++ [.index] then
            let args : Values model.Value checked.declaration.inputs :=
              inputShape.symm ▸ captures.append (.cons request.position .nil)
            let body := present
              (fun (child : OracleRead) current ↦
                let expanded : OracleRead := {child with
                  location := {child.location with invocation := request.location.invocation}
                  expansion := request.expansion ++ [(request.anchor, request.location)]}
                answer model self older expanded current) (checked.denote model args.present) state
            mapResult (fun result ↦
              let outcome := match result.outcome with
                | .stopped reason => .stopped reason
                | .returned values => match values.get .here with
                  | none => .stopped .incomplete
                  | some value => .returned (equal ▸ answerType ▸ value)
              ⟨outcome, result.state, .query request :: result.events⟩) body
          else .done ⟨.stopped .refused, state, [.query request]⟩
      else answer model self older request state
    else answer model self older request state

/-- Exact for every provider, including arbitrary replies, refusal, abort and incomplete stops. -/
theorem answer_represents (model : DomainModel)
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) (self : Nat)
    (entries : OracleEntries model snapshot domains math) (request : OracleRead) (state : S × Nat) :
    Represents (handler (externalHandler ordinary base)) (answer model self entries request state)
      (OracleStore.answer model base self entries request state) := by
  induction entries generalizing request state with
  | nil => rfl
  | cons entry older ih =>
    rcases entry with ⟨row, table⟩
    simp only [answer, OracleStore.answer]
    split
    · split
      · split
        · rfl
        · cases table.payload with
          | base data =>
            dsimp only
            exact represents_map _ _ _ _
              (represents_effect (externalHandler ordinary base) (.inr request) state.1)
          | virtual checked answerType captures =>
            dsimp only
            split
            · apply represents_map
              apply represents_present
              intro child current
              exact ih _ current
            · rfl
      · exact ih request state
    · exact ih request state

def read (model : DomainModel) (request : OracleRead)
    (state : OracleRuntimeState model snapshot domains math S) :
    PIR.Process (Interface model S E)
      (PIR.Execution (OracleRuntimeState model snapshot domains math S) (OracleEvent E)
        (model.Value request.kind.answer)) :=
  mapResult (fun result ↦
    ⟨result.outcome, {state with provider := result.state.1, queries := result.state.2},
      result.events⟩)
    (answer model state.self state.entries request (state.provider, state.queries))

theorem read_represents (model : DomainModel)
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) (request : OracleRead)
    (state : OracleRuntimeState model snapshot domains math S) :
    Represents (handler (externalHandler ordinary base)) (read model request state)
      (OracleStore.read model base request state) :=
  represents_map _ _ _ _ (answer_represents model ordinary base state.self _ request _)

end Zkc.Source.Structured.OracleProcess
