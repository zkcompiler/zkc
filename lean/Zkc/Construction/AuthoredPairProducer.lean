module

public import Zkc.Construction.Structured

@[expose] public section

/-! Structural admission of actual compiled producer instructions. The shared
construction step checks calculations, transcript observations, queries and
coordinates. Producer sends append proof payloads and must immediately be
observed. Owner-local field draws preserve transcript state and retain their
separate service-port identity. Receives are unsupported. This checker proves
no source projection theorem by itself.
-/
set_option autoImplicit false
namespace Zkc.Construction.AuthoredPair
open Zkc.Source Zkc.Source.Structured

mutual
def checkProducerFrom (program : Program) (context : Context) :
    CheckState → List Instruction → Except String CheckState
  | state, [] => .ok state
  | state, instruction :: rest => do
      let next ← checkProducerStep program context state instruction
      checkProducerFrom program context next rest

def checkProducerStep (program : Program) (context : Context) (state : CheckState) :
    Instruction → Except String CheckState
  | ⟨.localService port request template coordinates, operands, results, []⟩ =>
      match request with
      | ⟨"draw", [], .field field⟩ =>
          if state.pending = .none ∧ port.owner = context.role context.producer ∧
              port.contract = "random." ++ field ++ "/0" ∧ operands = [] ∧
              results = [.data (.field field)] ∧ template.entry = context.entry ∧
              coordinates = state.inductions ∧ template.repeats = state.inductions.length ∧
              coordinates.all (fun index => state.sorts[index]? == some (.data .index)) then
            .ok { state with sorts := state.sorts ++ results }
          else .error "construction-producer-local-service"
      | _ => .error "construction-producer-local-service-request"
  | ⟨.send site schema peer, [value], [], []⟩ =>
      if state.pending = .none ∧ schema = site ∧ peer = context.role context.validator ∧
          isData state.sorts[value]? then
        .ok { state with pending := .observe value (context.message site context.producer context.validator) }
      else .error "construction-producer-send"
  | ⟨.receive .., _, _, _⟩ => .error "construction-producer-receive"
  | instruction@⟨.call name, operands, results, []⟩ =>
      match program.payload.definitions.find? (·.helper.name == name) with
      | none => .error "construction-producer-helper"
      | some definition =>
          if operands.map (state.sorts[·]?) = definition.helper.inputs.map (some ∘ .data) ∧
              results = definition.helper.outputs.map .data ∧
              definition.helper.inputs.all (fun ty => !(ty matches .service _)) ∧
              definition.helper.outputs.all (fun ty => !(ty matches .service _)) then
            checkStep context state instruction
          else .error "construction-producer-helper-ports"
  | ⟨.loop _ _ yielded, count :: initial, results, body⟩ =>
      match state.pending, initial.idxOf? state.current with
      | .none, some position =>
          let fresh := state.sorts.length
          if state.sorts[count]? = some (.data .index) ∧
              initial.map (state.sorts[·]?) = results.map some ∧
              initial.count state.current = 1 ∧
              (initial.eraseIdx position).all (fun operand => isData state.sorts[operand]?) ∧
              yielded.length = initial.length then
            match checkProducerFrom program context
                { state with
                  sorts := state.sorts ++ .data .index :: results
                  current := fresh + 1 + position
                  pending := .none
                  inductions := state.inductions ++ [fresh] } body with
            | .ok final =>
                if final.pending = .none ∧ yielded.map (final.sorts[·]?) = results.map some ∧
                    yielded[position]? = some final.current then
                  .ok { state with
                    sorts := state.sorts ++ results
                    current := fresh + position
                    seen := final.seen }
                else .error "construction-producer-loop-yield"
            | .error error => .error error
          else .error "construction-producer-loop"
      | .none, none =>
          let fresh := state.sorts.length
          if state.sorts[count]? = some (.data .index) ∧
              initial.map (state.sorts[·]?) = results.map some ∧
              initial.all (fun operand => isData state.sorts[operand]?) ∧
              results.all (fun result => isData (some result)) ∧
              yielded.length = initial.length then
            match checkProducerFrom program context
                { state with
                  sorts := state.sorts ++ .data .index :: results
                  inductions := state.inductions ++ [fresh] } body with
            | .ok final =>
                if final.pending = .none ∧ final.current = state.current ∧
                    yielded.map (final.sorts[·]?) = results.map some then
                  .ok { state with sorts := state.sorts ++ results, seen := final.seen }
                else .error "construction-producer-local-loop-yield"
            | .error error => .error error
          else .error "construction-producer-local-loop"
      | _, _ => .error "construction-producer-loop-transcript"
  | instruction => checkStep context state instruction
end

def checkProducer (program : Program) (context : Context) (participant : Participant) :
    Except String Unit :=
  match participant.inputs.getLast? with
  | some (.transcript suite) =>
      if suite = context.suite ∧ participant.inputs.dropLast.all (fun sort => isData (some sort)) then
        match checkProducerFrom program context
            ⟨participant.inputs, participant.inputs.length - 1, .none, [], [], []⟩ participant.instructions with
        | .ok final =>
            if (context.draws.map Prod.fst).Nodup ∧
                context.draws.all (fun draw => final.seen.contains draw.1) ∧
                final.pending = .none ∧ participant.returned.getLast? = some final.current ∧
                participant.returned.map (final.sorts[·]?) = participant.outputs.map some ∧
                participant.returned.dropLast.all (fun index => isData final.sorts[index]?) then .ok ()
            else .error "construction-producer-final"
        | .error error => .error error
      else .error "construction-producer-inputs"
  | _ => .error "construction-producer-inputs"

end Zkc.Construction.AuthoredPair
