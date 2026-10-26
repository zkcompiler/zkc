module

public import Zkc.Construction.Semantics

@[expose] public section

/-! The transcript-construction rule.

`check` walks an exported validator once and accepts only programs whose
transcript operations follow the selected construction: every received message
is observed next with its message occurrence and the current transcript state;
each challenge consumes the current state, carries a selected query occurrence
and has its delivery observed next; calculations, helper calls and guards read
data only; a loop carries the current transcript exactly once, starts and ends
its body with nothing pending and yields its final state. Occurrence coordinates
must be exactly the enclosing loop indices. `Zkc.Construction.check_sound`
proves that every accepted program's ideal meaning is the Fiat–Shamir transform
of its interactive reading. Apart from the absence of a pending observation at
the end, the final clauses of `check` and the coordinate and occurrence-count
conditions are deployment checks that the proof does not use.
-/

set_option autoImplicit false

namespace Zkc.Construction.Uniform
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
  | some (.data _) => true
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
      match state.pending, scalarType ty with
      | .none, some _ =>
          if schema = site ∧ peer = context.role context.producer ∧ results = [.data ty] then
            .ok { state with
              sorts := state.sorts ++ [.data ty]
              pending := .observe state.sorts.length
                (context.message site context.producer context.validator) }
          else .error "construction-receive"
      | .none, none => .error "construction-receive-type"
      | _, _ => .error "construction-pending"
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
def check (context : Context) (participant : Participant) : Except String Unit :=
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


end Zkc.Construction.Uniform
