module

public import Zkc.Construction.Context
public import Zkc.Source.Structured.Admission

@[expose] public section

/-! Structural construction admission for explicit plain and Fiat–Shamir profiles.

The plain rule carries data and loop indices only. The Fiat–Shamir rule tracks
its affine transcript and pending observations, admitting recursively typed data.
Both retain the exact declared return ABI. Nominal property consumers prove full
Process equations through `Domain.Correspondence`; this check alone is not a
source compilation or security theorem. The scalar presentation interprets the
same nominal participant; it does not supply a second Instruction meaning or a
generic source-to-participant soundness theorem.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source


/-- What the next transcript operation must observe: a received message, whose
event the interactive reading has already absorbed, or a challenge delivery,
which both readings absorb at the observation. -/
inductive Pending where
  | none
  | observe (value : Nat) (origin : Origin)
  | deliver (value : Nat) (site : String)
  deriving DecidableEq, Repr

structure CheckState where
  sorts : List ValueSort
  current : Nat
  pending : Pending
  /-- Induction references of the enclosing loops, outermost first. -/
  inductions : List Nat
  /-- Static contents of coordinate references. -/
  paths : List (Nat × List Nat)
  /-- Selected query sites already challenged. -/
  seen : List String
  deriving DecidableEq, Repr

def CheckState.path (state : CheckState) (reference : Nat) : Option (List Nat) :=
  state.paths.lookup reference

def isData : Option ValueSort → Bool
  | some (.data ty) => !ty.isHandle
  | _ => false

/-- The transcript occurrence carries exactly the enclosing induction values. -/
def coordinatesValid (state : CheckState) (template : Template) (coordinates : Nat) : Bool :=
  state.sorts[coordinates]? == some .indices && state.path coordinates == some state.inductions &&
    template.repeats == state.inductions.length

mutual
def checkFrom (context : Context) : CheckState → List Instruction → Except String CheckState
  | state, [] => .ok state
  | state, instruction :: rest => do
      let successor ← checkStep context state instruction
      checkFrom context successor rest

/-- One step of the rule. A received message is observed next with its message
occurrence. A challenge needs no pending observation, consumes the current
state, carries a selected query occurrence, and its delivery is observed next.
Calculations, helper calls and guards read data only and may separate a
challenge from its delivery. A loop carries the current transcript exactly once,
starts and ends its body with nothing pending, and yields its final state.
Every other operation refuses. -/
def checkStep (context : Context) (state : CheckState) : Instruction → Except String CheckState
  | ⟨.receive site schema peer ty, [], results, []⟩ =>
      match state.pending with
      | .none =>
          if ty.isHandle then .error "construction-receive-type" else
          if schema = site ∧ peer = context.role context.producer ∧ results = [.data ty] then
            .ok { state with
              sorts := state.sorts ++ [.data ty]
              pending := .observe state.sorts.length
                (context.message site context.producer context.validator) }
          else .error "construction-receive"
      | _ => .error "construction-pending"
  | ⟨.indicesEmpty, [], [.indices], []⟩ =>
      .ok { state with
        sorts := state.sorts ++ [.indices]
        paths := (state.sorts.length, []) :: state.paths }
  | ⟨.indicesAppend, [coordinates, index], [.indices], []⟩ =>
      match state.path coordinates with
      | some path =>
          if state.sorts[coordinates]? = some .indices ∧ state.sorts[index]? = some (.data .index) then
            .ok { state with
              sorts := state.sorts ++ [.indices]
              paths := (state.sorts.length, path ++ [index]) :: state.paths }
          else .error "construction-coordinates"
      | none => .error "construction-coordinates"
  | ⟨.observe suite template, [current, value, coordinates], results, []⟩ =>
      let check (expected : Nat) (origin : Origin) (delivery : Bool) : Except String CheckState :=
        if suite = context.suite ∧ current = state.current ∧ value = expected ∧
            template.entry = context.entry ∧ template.origin context = some origin ∧
            template.sentBy (context.role context.validator) = delivery ∧
            coordinatesValid state template coordinates = true ∧
            results = [.transcript context.suite] then
          .ok { state with
            sorts := state.sorts ++ [.transcript context.suite]
            current := state.sorts.length
            pending := .none }
        else .error "construction-observe"
      match state.pending with
      | .observe expected origin => check expected origin false
      | .deliver expected site =>
          check expected (context.message site context.validator context.producer) true
      | .none => .error "construction-observe-unexpected"
  | ⟨.challenge suite field template, [current, coordinates], results, []⟩ =>
      match state.pending, template.querySite? with
      | .none, some site =>
          match context.draws.lookup site with
          | some delivery =>
              if suite = context.suite ∧ current = state.current ∧ template.entry = context.entry ∧
                  template.origin context = some (context.query site (.draw field)) ∧
                  "random." ++ field ++ "/0" = context.contract ∧ site ∉ state.seen ∧
                  coordinatesValid state template coordinates = true ∧
                  results = [.data (.field field), .transcript context.suite] then
                .ok { state with
                  sorts := state.sorts ++ [.data (.field field), .transcript context.suite]
                  current := state.sorts.length + 1
                  pending := .deliver state.sorts.length delivery
                  seen := site :: state.seen }
              else .error "construction-challenge"
          | none => .error "construction-challenge-site"
      | .none, none => .error "construction-challenge-template"
      | _, _ => .error "construction-pending"
  | ⟨.calculate calculation, operands, results, []⟩ =>
      match state.pending with
      | .observe _ _ => .error "construction-pending"
      | _ =>
          if operands.map (state.sorts[·]?) = calculation.op.arguments.map (some ∘ .data) ∧
              results = calculation.op.results.map .data then
            .ok { state with sorts := state.sorts ++ results }
          else .error "construction-calculation"
  | ⟨.call _, operands, results, []⟩ =>
      match state.pending with
      | .observe _ _ => .error "construction-pending"
      | _ =>
          if operands.all (fun operand => isData state.sorts[operand]?) ∧
              results.all (fun result => isData (some result)) then
            .ok { state with sorts := state.sorts ++ results }
          else .error "construction-call"
  | ⟨.guard _, [condition], [], []⟩ =>
      match state.pending with
      | .observe _ _ => .error "construction-pending"
      | _ =>
          if state.sorts[condition]? = some (.data .boolean) then .ok state
          else .error "construction-guard"
  | ⟨.loop _ _ yielded, count :: initial, results, body⟩ =>
      match state.pending, initial.idxOf? state.current with
      | .none, some position =>
          let fresh := state.sorts.length
          if state.sorts[count]? = some (.data .index) ∧
              initial.map (state.sorts[·]?) = results.map some ∧
              initial.count state.current = 1 ∧
              (initial.eraseIdx position).all (fun operand => isData state.sorts[operand]?) ∧
              yielded.length = initial.length then
            match checkFrom context
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
                else .error "construction-loop-yield"
            | .error error => .error error
          else .error "construction-loop"
      | .none, none => .error "construction-loop-transcript"
      | _, _ => .error "construction-pending"
  | ⟨.send .., _, _, _⟩ => .error "construction-send"
  | ⟨.unsupported _, _, _, _⟩ => .error "construction-unsupported"
  | _ => .error "construction-shape"
end

/-- The complete rule for one exported validator. Inputs are data followed by
one host transcript of the selected suite; the selected query sites are
distinct and each is challenged at exactly one exported operation; nothing
remains pending, the last returned value is the final transcript state and the
other returned values are data matching the declared outputs. -/
def checkFiatShamir (context : Context) (participant : Participant) : Except String Unit :=
  match participant.inputs.getLast? with
  | some (.transcript suite) =>
      if suite = context.suite ∧ participant.inputs.dropLast.all (fun sort => isData (some sort)) then
        match checkFrom context ⟨participant.inputs, participant.inputs.length - 1, .none, [], [], []⟩
            participant.instructions with
        | .ok final =>
            if (context.draws.map Prod.fst).Nodup ∧
                context.draws.all (fun draw => final.seen.contains draw.1) then
              if final.pending = .none ∧ participant.returned.getLast? = some final.current ∧
                  participant.returned.map (final.sorts[·]?) = participant.outputs.map some ∧
                  participant.returned.dropLast.all (fun index => isData final.sorts[index]?) then
                .ok ()
              else .error "construction-final"
            else .error "construction-draws"
        | .error error => .error error
      else .error "construction-inputs"
  | _ => .error "construction-inputs"


/-- A plain frame carries only data and the enclosing induction references.
There is no transcript reference or pending transcript observation. -/
structure PlainState where
  sorts : List ValueSort
  inductions : List Nat := []
  deriving DecidableEq, Repr

mutual
def checkPlainFrom (context : Context) (self peer : Nat) :
    PlainState → List Instruction → Except String PlainState
  | state, [] => .ok state
  | state, instruction :: rest => do
      let next ← checkPlainStep context self peer state instruction
      checkPlainFrom context self peer next rest

def checkPlainStep (context : Context) (self peer : Nat) (state : PlainState) :
    Instruction → Except String PlainState
  | ⟨.receive site schema sender ty, [], results, []⟩ =>
      if !ty.isHandle ∧ schema = site ∧ sender = context.role peer ∧ results = [.data ty] then
        .ok { state with sorts := state.sorts ++ results }
      else .error "construction-plain-receive"
  | ⟨.send site schema receiver, [value], [], []⟩ =>
      if schema = site ∧ receiver = context.role peer ∧ isData state.sorts[value]? then .ok state
      else .error "construction-plain-send"
  | ⟨.calculate calculation, operands, results, []⟩ =>
      if operands.map (state.sorts[·]?) = calculation.op.arguments.map (some ∘ .data) ∧
          results = calculation.op.results.map .data ∧
          results.all (fun sort => isData (some sort)) then
        .ok { state with sorts := state.sorts ++ results }
      else .error "construction-plain-calculation"
  | ⟨.call _, operands, results, []⟩ =>
      if operands.all (fun operand => isData state.sorts[operand]?) ∧
          results.all (fun sort => isData (some sort)) then
        .ok { state with sorts := state.sorts ++ results }
      else .error "construction-plain-call"
  | ⟨.guard _, [condition], [], []⟩ =>
      if state.sorts[condition]? = some (.data .boolean) then .ok state
      else .error "construction-plain-guard"
  | ⟨.localService port request template coordinates, [], results, []⟩ =>
      match request with
      | ⟨"draw", [], .field field⟩ =>
          if port.owner = context.role self ∧ port.contract = "random." ++ field ++ "/0" ∧
              results = [.data (.field field)] ∧ template.entry = context.entry ∧
              coordinates = state.inductions ∧ template.repeats = coordinates.length then
            .ok { state with sorts := state.sorts ++ results }
          else .error "construction-plain-local-service"
      | _ => .error "construction-plain-local-service-request"
  | ⟨.loop _ _ yielded, count :: initial, results, body⟩ =>
      let fresh := state.sorts.length
      if state.sorts[count]? = some (.data .index) ∧
          initial.map (state.sorts[·]?) = results.map some ∧
          results.all (fun sort => isData (some sort)) ∧ yielded.length = results.length then
        match checkPlainFrom context self peer
            ⟨state.sorts ++ .data .index :: results, state.inductions ++ [fresh]⟩ body with
        | .ok final =>
            if yielded.map (final.sorts[·]?) = results.map some then
              .ok { state with sorts := state.sorts ++ results }
            else .error "construction-plain-loop-yield"
        | .error error => .error error
      else .error "construction-plain-loop"
  | ⟨.challenge .., _, _, _⟩ => .error "construction-plain-challenge"
  | ⟨.observe .., _, _, _⟩ => .error "construction-plain-transcript"
  | _ => .error "construction-plain-shape"
end

def checkPlain (context : Context) (self peer : Nat) (participant : Participant) : Except String Unit := do
  if !participant.inputs.all (fun sort => isData (some sort)) then
    throw "construction-plain-inputs"
  let final ← checkPlainFrom context self peer ⟨participant.inputs, []⟩ participant.instructions
  if participant.returned.map (final.sorts[·]?) = participant.outputs.map some ∧
      participant.outputs.all (fun sort => isData (some sort)) then return ()
  else throw "construction-plain-final"

/-- Profile admission follows the actual ABI. Plain checks never append, consume
or remove a transcript value. The legacy uniform theorem has its own explicitly
scoped checker in `Construction.Uniform`. Generic consumers use nominal Process
correspondence, including all frames, replies and stops. -/
def check (context : Context) (participant : Participant) : Except String Unit :=
  match context.profile with
  | .plain => checkPlain context context.validator context.producer participant
  | .fiatShamir _ => checkFiatShamir context participant


end Zkc.Construction
