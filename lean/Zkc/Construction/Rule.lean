module

public import Zkc.Construction.Context
public import Zkc.Source.Structured.Admission

@[expose] public section

/-! Structural construction admission for explicit plain and Fiat–Shamir profiles.

The plain rule carries local values, including custody, and loop indices. The Fiat–Shamir rule tracks
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

/-- Wire payload eligibility excludes all handles, including custody. -/
def isData : Option ValueSort → Bool
  | some (.data ty) => !ty.isHandle
  | _ => false

/-- Local frames also carry nominal custody; other handles remain excluded.
This structural transport check does not establish ledger freshness or linearity. -/
def isLocalValue : Option ValueSort → Bool
  | some (.data ty) => ty.isCustody || !ty.isHandle
  | _ => false

/-- Diagnostics retain the distinction between pure Math and stopping local code. -/
def closedDiagnostic (kind : Structured.HelperKind) (detail : String) : String :=
  (if kind == .math then "construction-math-" else "construction-local-") ++ detail

/-- Admission of two closed arms from their independently checked body rows. -/
def checkClosedArmResults (kind : Structured.HelperKind) (results : List ValueSort)
    (yes no : InstructionRegion) (checkedYes checkedNo : Except String (List ValueSort)) :
    Except String Unit := do
  if yes.inputs != no.inputs || !yes.inputs.all (fun s => isData (some s)) ||
      !results.all (fun s => isData (some s)) then throw (closedDiagnostic kind "captures")
  let yesSorts ← checkedYes
  let noSorts ← checkedNo
  if yes.yielded.map (yesSorts[·]?) != results.map some ||
      no.yielded.map (noSorts[·]?) != results.map some then throw (closedDiagnostic kind "yields")

mutual
/-- One formation walk for closed data frames. Both arms form, including dormant
ones. Local frames may reject at guards; Math remains pure. The call predicate
receives each nested frame's kind so a Math arm cannot inherit local call rights.
Transcript, communication, service effects and handles remain excluded. -/
def checkClosedFrom (kind : Structured.HelperKind)
    (admitCall : Structured.HelperKind → String → List ValueSort → List ValueSort → Bool) :
    List ValueSort → List Instruction → Except String (List ValueSort)
  | sorts, [] => .ok sorts
  | sorts, instruction :: rest => do
      let next ← checkClosedStep kind admitCall sorts instruction
      checkClosedFrom kind admitCall next rest

def checkClosedStep (kind : Structured.HelperKind)
    (admitCall : Structured.HelperKind → String → List ValueSort → List ValueSort → Bool)
    (sorts : List ValueSort) : Instruction → Except String (List ValueSort)
  | ⟨.calculate calculation, operands, results, []⟩ =>
      if operands.map (sorts[·]?) = calculation.op.arguments.map (some ∘ .data) ∧
          results = calculation.op.results.map .data ∧ results.all (fun s => isData (some s)) then
        .ok (sorts ++ results)
      else .error (closedDiagnostic kind "calculation")
  | ⟨.call name, operands, results, []⟩ => do
      let some inputs := operands.mapM (sorts[·]?) | throw (closedDiagnostic kind "call")
      if inputs.all (fun s => isData (some s)) ∧ results.all (fun s => isData (some s)) ∧
          admitCall kind name inputs results then return sorts ++ results
      else throw (closedDiagnostic kind "call")
  | ⟨.guard _, [condition], [], []⟩ | ⟨.require _, [condition], [], []⟩ =>
      if kind == .local && sorts[condition]? == some (.data .boolean) then .ok sorts
      else .error (closedDiagnostic kind "operation")
  | ⟨operation, selector :: captures, results,
      [⟨yesInputs, yesBody, yesYielded⟩, ⟨noInputs, noBody, noYielded⟩]⟩ => do
      if operation != .mathBranch && operation != .localBranch then
        throw (closedDiagnostic kind "operation")
      let bodyKind := if operation == .mathBranch then Structured.HelperKind.math else .local
      if kind == .math && bodyKind == .local then throw (closedDiagnostic kind "operation")
      if sorts[selector]? != some (.data .boolean) ||
          captures.map (sorts[·]?) != yesInputs.map some || yesInputs != noInputs ||
          !yesInputs.all (fun s => isData (some s)) ||
          !results.all (fun s => isData (some s)) then throw (closedDiagnostic bodyKind "captures")
      checkClosedArmResults bodyKind results ⟨yesInputs, yesBody, yesYielded⟩ ⟨noInputs, noBody, noYielded⟩
        (checkClosedFrom bodyKind admitCall yesInputs yesBody)
        (checkClosedFrom bodyKind admitCall noInputs noBody)
      return sorts ++ results
  | _ => .error (closedDiagnostic kind "operation")
end

/-- Both closed arms form using the same kind-sensitive traversal as nested code. -/
def checkClosedArms (kind : Structured.HelperKind)
    (admitCall : Structured.HelperKind → String → List ValueSort → List ValueSort → Bool)
    (results : List ValueSort) (yes no : InstructionRegion) : Except String Unit :=
  checkClosedArmResults kind results yes no
    (checkClosedFrom kind admitCall yes.inputs yes.instructions)
    (checkClosedFrom kind admitCall no.inputs no.instructions)

/-- The transcript occurrence carries exactly the enclosing induction values. -/
def coordinatesValid (state : CheckState) (template : Template) (coordinates : Nat) : Bool :=
  state.sorts[coordinates]? == some .indices && state.path coordinates == some state.inductions &&
    template.repeats == state.inductions.length

/-- Shared scalar/block challenge rule. Source association independently checks
that request values are the constants denoted by the original SSA operands. -/
def checkRequestChallenge (context : Context) (state : CheckState) (suite : String)
    (request : Request) (template : Template) (current coordinates : Nat)
    (operands : List Nat) (results : List ValueSort) : Except String CheckState :=
  match state.pending, template.querySite? with
  | .none, some site =>
    match context.draws.lookup site with
    | some delivery =>
      if suite = context.suite ∧ current = state.current ∧ template.entry = context.entry ∧
          context.service.isSome ∧ request.valid ∧ request.nativeSupported ∧
          (request.operation context.contract).isSome ∧
          template.originFor context request = some (context.query site request) ∧
          site ∉ state.seen ∧ coordinatesValid state template coordinates = true ∧
          operands.all (fun reference => state.sorts[reference]? == some (.data .index)) ∧
          results = [.data request.sort, .transcript context.suite] then
        .ok { state with
          sorts := state.sorts ++ results
          current := state.sorts.length + 1
          pending := .deliver state.sorts.length delivery
          seen := site :: state.seen }
      else .error "construction-index-challenge"
    | none => .error "construction-challenge-site"
  | .none, none => .error "construction-challenge-template"
  | _, _ => .error "construction-pending"

/-- Local service formation is independent of public transcript replacement.
Only the owning participant can use the port, with the exact active ancestry. -/
def localServiceValid (context : Context) (self : Nat) (sorts : List ValueSort) (inductions : List Nat)
    (port : ServicePort) (request : Request) (template : Template)
    (coordinates operands : List Nat) (results : List ValueSort) : Bool :=
  request.valid && (request.operation port.contract).isSome &&
    operands.length == request.operands.length &&
    operands.all (fun reference => sorts[reference]? == some (.data .index)) &&
    port.owner == context.role self && results == [.data request.sort] &&
    template.entry == context.entry && coordinates == inductions &&
    coordinates.all (fun reference => sorts[reference]? == some (.data .index)) &&
    template.repeats == coordinates.length

mutual
def checkFrom (context : Context) : CheckState → List Instruction → Except String CheckState
  | state, [] => .ok state
  | state, instruction :: rest => do
      let successor ← checkStep context state instruction
      checkFrom context successor rest

/-- One step of the rule. A received message is observed next with its message
occurrence. A challenge needs no pending observation, consumes the current
state, carries a selected query occurrence, and its delivery is observed next.
Calculations and guards read ordinary data; helper calls also carry local
custody. These steps may separate a challenge from its delivery. A loop carries the current transcript exactly once,
starts and ends its body with nothing pending, and yields its final state.
Every other operation refuses. -/
def checkStep (context : Context) (state : CheckState) : Instruction → Except String CheckState
  | ⟨.localService port request template coordinates, operands, results, []⟩ =>
      match state.pending with
      | .none =>
          if localServiceValid context context.validator state.sorts state.inductions port request template coordinates operands results then
            .ok { state with sorts := state.sorts ++ results }
          else .error "construction-local-service"
      | _ => .error "construction-pending"
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
  | ⟨.indexChallenge suite bound template, [current, boundReference, coordinates], results, []⟩ =>
      checkRequestChallenge context state suite (.sampleIndex bound) template current coordinates
        [boundReference] results
  | ⟨.blockChallenge suite bound count template, [current, coordinates], results, []⟩ =>
      checkRequestChallenge context state suite (.sampleIndices bound count) template current coordinates
        [] results
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
          if operands.all (fun operand => isLocalValue state.sorts[operand]?) ∧
              results.all (fun result => isLocalValue (some result)) then
            .ok { state with sorts := state.sorts ++ results }
          else .error "construction-call"
  | instruction@⟨.mathBranch, _, _, _⟩ => do
      if state.pending matches .observe .. then throw "construction-pending"
      let sorts ← checkClosedStep .math (fun _ _ _ _ => true) state.sorts instruction
      return { state with sorts := sorts }
  | instruction@⟨.localBranch, _, _, _⟩ => do
      if state.pending matches .observe .. then throw "construction-pending"
      let sorts ← checkClosedStep .local (fun _ _ _ _ => true) state.sorts instruction
      return { state with sorts := sorts }
  | ⟨.guard _, [condition], [], []⟩ | ⟨.require _, [condition], [], []⟩ =>
      match state.pending with
      | .observe _ _ => .error "construction-pending"
      | _ =>
          if state.sorts[condition]? = some (.data .boolean) then .ok state
          else .error "construction-guard"
  | ⟨.loop _ _, count :: initial, results, [⟨regionInputs, body, yielded⟩]⟩ =>
      if regionInputs != .data .index :: results then .error "construction-loop-region-inputs" else
      match state.pending, initial.idxOf? state.current with
      | .none, some position =>
          let fresh := state.sorts.length
          if state.sorts[count]? = some (.data .index) ∧
              initial.map (state.sorts[·]?) = results.map some ∧
              initial.count state.current = 1 ∧
              (initial.eraseIdx position).all (fun operand => isLocalValue state.sorts[operand]?) ∧
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

/-- The complete rule for one exported validator. Inputs are local values followed by
one host transcript of the selected suite; the selected query sites are
distinct and each is challenged at exactly one exported operation; nothing
remains pending, the last returned value is the final transcript state and the
other returned values are local values matching the declared outputs. -/
def checkFiatShamir (context : Context) (participant : Participant) : Except String Unit :=
  match participant.inputs.getLast? with
  | some (.transcript suite) =>
      if suite = context.suite ∧ participant.inputs.dropLast.all (fun sort => isLocalValue (some sort)) then
        match checkFrom context ⟨participant.inputs, participant.inputs.length - 1, .none, [], [], []⟩
            participant.instructions with
        | .ok final =>
            if (context.draws.map Prod.fst).Nodup ∧
                context.draws.all (fun draw => final.seen.contains draw.1) then
              if final.pending = .none ∧ participant.returned.getLast? = some final.current ∧
                  participant.returned.map (final.sorts[·]?) = participant.outputs.map some ∧
                  participant.returned.dropLast.all (fun index => isLocalValue final.sorts[index]?) then
                .ok ()
              else .error "construction-final"
            else .error "construction-draws"
        | .error error => .error error
      else .error "construction-inputs"
  | _ => .error "construction-inputs"


/-- A plain frame carries local values and the enclosing induction references.
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
          results.all (fun sort => isLocalValue (some sort)) then
        .ok { state with sorts := state.sorts ++ results }
      else .error "construction-plain-calculation"
  | ⟨.call _, operands, results, []⟩ =>
      if operands.all (fun operand => isLocalValue state.sorts[operand]?) ∧
          results.all (fun sort => isLocalValue (some sort)) then
        .ok { state with sorts := state.sorts ++ results }
      else .error "construction-plain-call"
  | instruction@⟨.mathBranch, _, _, _⟩ => do
      let sorts ← checkClosedStep .math (fun _ _ _ _ => true) state.sorts instruction
      return { state with sorts := sorts }
  | instruction@⟨.localBranch, _, _, _⟩ => do
      let sorts ← checkClosedStep .local (fun _ _ _ _ => true) state.sorts instruction
      return { state with sorts := sorts }
  | ⟨.guard _, [condition], [], []⟩ | ⟨.require _, [condition], [], []⟩ =>
      if state.sorts[condition]? = some (.data .boolean) then .ok state
      else .error "construction-plain-guard"
  | ⟨.localService port request template coordinates, operands, results, []⟩ =>
      if !request.valid then .error "construction-plain-local-service-request" else
      if localServiceValid context self state.sorts state.inductions port request template
          coordinates operands results then
        .ok { state with sorts := state.sorts ++ results }
      else .error "construction-plain-local-service"
  | ⟨.loop _ _, count :: initial, results, [⟨regionInputs, body, yielded⟩]⟩ =>
      if regionInputs != .data .index :: results then .error "construction-loop-region-inputs" else
      let fresh := state.sorts.length
      if state.sorts[count]? = some (.data .index) ∧
          initial.map (state.sorts[·]?) = results.map some ∧
          results.all (fun sort => isLocalValue (some sort)) ∧ yielded.length = results.length then
        match checkPlainFrom context self peer
            ⟨state.sorts ++ .data .index :: results, state.inductions ++ [fresh]⟩ body with
        | .ok final =>
            if yielded.map (final.sorts[·]?) = results.map some then
              .ok { state with sorts := state.sorts ++ results }
            else .error "construction-plain-loop-yield"
        | .error error => .error error
      else .error "construction-plain-loop"
  | ⟨.challenge .., _, _, _⟩ | ⟨.indexChallenge .., _, _, _⟩
  | ⟨.blockChallenge .., _, _, _⟩ => .error "construction-plain-challenge"
  | ⟨.observe .., _, _, _⟩ => .error "construction-plain-transcript"
  | _ => .error "construction-plain-shape"
end

def checkPlain (context : Context) (self peer : Nat) (participant : Participant) : Except String Unit := do
  if !participant.inputs.all (fun sort => isLocalValue (some sort)) then
    throw "construction-plain-inputs"
  let final ← checkPlainFrom context self peer ⟨participant.inputs, []⟩ participant.instructions
  if participant.returned.map (final.sorts[·]?) = participant.outputs.map some ∧
      participant.outputs.all (fun sort => isLocalValue (some sort)) then return ()
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
