module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Construction.Scalar

@[expose] public section

/-! Meanings of exported constructed programs.

Values are structured data (scalars, indices and field vectors), transcript
histories and occurrence coordinates. Calculations are evaluated with the
structured evaluator's meaning and helper calls with a closed table of checked
helpers, looked up by name and invoked at their checked signatures.

`ideal` interprets a program with the ideal transcript model: a transcript
capability holds its absorbed history, an observation appends the model
occurrence of its template with the observed payload, and a challenge applies
the challenge function to the history ending with its occurrence. `spec` reads
the same program back as the interactive validator it replaced: each challenge
becomes the selected query on the service handle, and observing a message the
validator sends is the delivery of that message to the producer. Both are
written in continuation style, so a loop's iterations, a body's continuation and
a program's suffix compose without returning intermediate environments.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source
open Zkc.Source.Common.Native (ScalarValue)

variable {F G : Type}

section Interactive
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (context : Context) (handle : Nat)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- Iterate a loop body over the given induction values. -/
def iterate {I : PIR.Signature} {A : Type}
    (body : List (Value F G) → (List (Value F G) → PIR.Process I A) → PIR.Process I A)
    (env : List (Value F G)) (yielded : List Nat) :
    List Nat → List (Value F G) → (List (Value F G) → PIR.Process I A) → PIR.Process I A
  | [], carried, next => next carried
  | index :: rest, carried, next =>
      body (env ++ .index index :: carried) fun final =>
        match read final yielded with
        | some carried' => iterate body env yielded rest carried' next
        | none => .halt .refused

mutual
/-- The interactive validator an exported program replaced, in continuation
style. Receives come from the producer; each challenge becomes the selected
query on `handle`; an observed message sent by the validator is its delivery to
the producer. Transcript values are computed as inert histories. -/
def specK {A : Type} : List Instruction → List (Value F G) →
    (List (Value F G) → PIR.Process (Actions F G) A) → PIR.Process (Actions F G) A
  | [], env, next => next env
  | instruction :: rest, env, next =>
      specStep instruction env fun env' => specK rest env' next

def specStep {A : Type} : Instruction → List (Value F G) →
    (List (Value F G) → PIR.Process (Actions F G) A) → PIR.Process (Actions F G) A
  | ⟨.receive site _ _ ty, [], _, _⟩, env, next =>
      match scalarType ty with
      | some common =>
          .call (.receive common site context.producer) fun value =>
            match Zkc.Construction.Payload.ofValue common value with
            | some payload => next (env ++ [.data payload])
            | none => .halt .refused
      | none => .halt .refused
  | ⟨.indicesEmpty, [], _, _⟩, env, next => next (env ++ [.indices []])
  | ⟨.indicesAppend, [coordinates, index], _, _⟩, env, next =>
      next (env ++ [.indices (indicesAt env coordinates ++ (indexAt env index).toList)])
  | ⟨.observe _ template, [state, value, _], _, _⟩, env, next =>
      let history := (transcriptAt env state).getD []
      match template.origin context, dataAt env value with
      | some origin, some payload =>
          let env' := env ++ [.transcript (history ++ [.message origin payload])]
          if template.sentBy (context.role context.validator) then
            sendPayload ((template.messageSite?).getD "") context.producer payload (next env')
          else next env'
      | _, _ => next (env ++ [.transcript history])
  | ⟨.challenge _ field template, [state, _], _, _⟩, env, next =>
      let history := (transcriptAt env state).getD []
      match template.origin context, template.querySite? with
      | some origin, some site =>
          .call (.query site field (.cons handle .nil)) fun answer =>
            next (env ++ [.data (.field field answer), .transcript (history ++ [.challenge origin])])
      | _, _ => .halt .refused
  | ⟨.calculate calculation, operands, _, _⟩, env, next =>
      match read env operands with
      | some arguments =>
          match Zkc.Construction.calculate calculation arguments with
          | .returned results => next (env ++ results)
          | .stopped reason => .halt reason
      | none => .halt .refused
  | ⟨.call name, operands, declared, _⟩, env, next =>
      match read env operands with
      | some arguments =>
          match callHelper table name arguments with
          | .returned results =>
              if results.length = declared.length then next (env ++ results) else .halt .refused
          | .stopped reason => .halt reason
      | none => .halt .refused
  | ⟨.guard _, [condition], _, _⟩, env, next =>
      match env[condition]? with
      | some (.data (.boolean true)) => next env
      | some (.data (.boolean false)) => .halt .reject
      | _ => .halt .refused
  | ⟨.loop _ maximum yielded, count :: initial, _, body⟩, env, next =>
      match indexAt env count, read env initial with
      | some bound, some carried =>
          if bound ≤ maximum then
            iterate (fun start continuation => specK body start continuation) env yielded
              (List.range bound) carried fun final => next (env ++ final)
          else .halt .refused
      | _, _ => .halt .refused
  | _, _, _ => .halt .refused
end

end Interactive

section Ideal
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- Iterate a loop body over the given induction values, threading the proof. -/
def iterateM {R : Type}
    (body : List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G))
    (env : List (Value F G)) (yielded : List Nat) :
    List Nat → List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G)
  | [], carried, proof, next => next carried proof
  | index :: rest, carried, proof, next =>
      body (env ++ .index index :: carried) proof fun final unread =>
        match read final yielded with
        | some carried' => iterateM body env yielded rest carried' unread next
        | none => pure (.stopped .refused, unread)

mutual
/-- The ideal meaning of an exported constructed program, in continuation
style: a transcript capability holds its absorbed history, observation appends
the model occurrence of its template with the observed payload, and a challenge
applies `challenge` to the history ending with its occurrence. Receives read the
proof in order. A stop returns the unread proof at that point. -/
def idealK {R : Type} : List Instruction → List (Value F G) → Proof F G →
    (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G)
  | [], env, proof, next => next env proof
  | instruction :: rest, env, proof, next =>
      idealStep instruction env proof fun env' unread => idealK rest env' unread next

def idealStep {R : Type} : Instruction → List (Value F G) → Proof F G →
    (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G)
  | ⟨.receive _ _ _ ty, [], _, _⟩, env, proof, next =>
      match scalarType ty, proof with
      | some common, payload :: rest =>
          if payload.ty = common then next (env ++ [.data payload]) rest
          else pure (.stopped .refused, proof)
      | _, _ => pure (.stopped .refused, proof)
  | ⟨.indicesEmpty, [], _, _⟩, env, proof, next => next (env ++ [.indices []]) proof
  | ⟨.indicesAppend, [coordinates, index], _, _⟩, env, proof, next =>
      next (env ++ [.indices (indicesAt env coordinates ++ (indexAt env index).toList)]) proof
  | ⟨.observe _ template, [state, value, _], _, _⟩, env, proof, next =>
      match transcriptAt env state, template.origin context, dataAt env value with
      | some history, some origin, some payload =>
          next (env ++ [.transcript (history ++ [.message origin payload])]) proof
      | _, _, _ => pure (.stopped .refused, proof)
  | ⟨.challenge _ field template, [state, _], _, _⟩, env, proof, next =>
      match transcriptAt env state, template.origin context with
      | some history, some origin => do
          let answer ← challenge (history ++ [.challenge origin])
          next (env ++ [.data (.field field answer), .transcript (history ++ [.challenge origin])]) proof
      | _, _ => pure (.stopped .refused, proof)
  | ⟨.calculate calculation, operands, _, _⟩, env, proof, next =>
      match read env operands with
      | some arguments =>
          match Zkc.Construction.calculate calculation arguments with
          | .returned results => next (env ++ results) proof
          | .stopped reason => pure (.stopped reason, proof)
      | none => pure (.stopped .refused, proof)
  | ⟨.call name, operands, declared, _⟩, env, proof, next =>
      match read env operands with
      | some arguments =>
          match callHelper table name arguments with
          | .returned results =>
              if results.length = declared.length then next (env ++ results) proof
              else pure (.stopped .refused, proof)
          | .stopped reason => pure (.stopped reason, proof)
      | none => pure (.stopped .refused, proof)
  | ⟨.guard _, [condition], _, _⟩, env, proof, next =>
      match env[condition]? with
      | some (.data (.boolean true)) => next env proof
      | some (.data (.boolean false)) => pure (.stopped .reject, proof)
      | _ => pure (.stopped .refused, proof)
  | ⟨.loop _ maximum yielded, count :: initial, _, body⟩, env, proof, next =>
      match indexAt env count, read env initial with
      | some bound, some carried =>
          if bound ≤ maximum then
            iterateM (fun start unread continuation => idealK body start unread continuation) env yielded
              (List.range bound) carried proof fun final unread => next (env ++ final) unread
          else pure (.stopped .refused, proof)
      | _, _ => pure (.stopped .refused, proof)
  | _, _, proof, _ => pure (.stopped .refused, proof)
end

end Ideal

section Programs
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]

def ideal (context : Context) (challenge : History F G → m F)
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (returned : List Nat)
    (instructions : List Instruction) (env : List (Value F G)) (proof : Proof F G) :
    m (PIR.Outcome (List (Value F G)) × Proof F G) :=
  idealK context challenge table instructions env proof fun final unread =>
    pure (finish returned final, unread)

def spec (context : Context) (handle : Nat)
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (returned : List Nat)
    (instructions : List Instruction) (env : List (Value F G)) :
    PIR.Process (Actions F G) (List (Value F G)) :=
  specK context handle table instructions env fun final =>
    match read final returned with
    | some values => .done values
    | none => .halt .refused

end Programs

end Zkc.Construction
