module

public import Zkc.Source.Constructed

@[expose] public section

/-! Direct instruction semantics for the constructed export carrier.

The evaluator reads flat operands, invokes primitive meanings, and threads
complete replies without constructing a RawProgram or a typed Program. Its
lowering theorem makes the bridge-introduced pack/project/guard translation a
proved obligation. Native extraction and primitive implementation remain outside
this model theorem.
-/

namespace Zkc.Source.Constructed

variable {I : PIR.Signature}

def denoteInstructions (meaning : Meaning I) (outputs : List String) (returned : List Nat) :
    List Instruction → {Γ : List Ty} →
      Environment (Values meaning.Value) Γ → PIR.Proc I (Values meaning.Value outputs)
  | [], Γ, env =>
    match decodeOperands Γ (outputs.map scalar) returned with
    | .ok arguments => .done (unpack outputs (Operands.eval env arguments))
    | .error _ => .halt .refused
  | .apply op indices :: rest, Γ, env =>
    match decodeOperands Γ (op.arguments.map scalar) indices with
    | .ok arguments => (meaning.primitive op (unpack op.arguments (Operands.eval env arguments))).bind
        fun reply => denoteInstructions meaning outputs returned rest (env.push reply)
    | .error _ => .halt .refused
  | .project types index tuple :: rest, Γ, env =>
    if h : index < types.length then
      match decodeVariable Γ types tuple with
      | .ok value => denoteInstructions meaning outputs returned rest
          (env.push (.cons (tupleAt (env value) ⟨index, h⟩) .nil))
      | .error _ => .halt .refused
    else .halt .refused
  | .guard index _ :: rest, Γ, env =>
    match decodeVariable Γ ["i1"] index with
    | .ok value =>
      if meaning.condition (match env value with | .cons condition .nil => condition) then
        denoteInstructions meaning outputs returned rest env
      else .halt .reject
    | .error _ => .halt .refused
  | .stop reason _ :: rest, _, _ =>
    if rest.isEmpty && returned.isEmpty then .halt reason else .halt .refused

theorem lower_denotation (meaning : Meaning I) (outputs : List String) (returned : List Nat)
    (instructions : List Instruction) (raw : RawProgram Ty Op)
    (lowered : lower outputs returned instructions = .ok raw) {Γ : List Ty}
    (env : Environment (Values meaning.Value) Γ) :
    denoteInstructions meaning outputs returned instructions env =
      raw.denote meaning.interpretation outputs env := by
  induction instructions generalizing Γ raw with
  | nil =>
    cases lowered
    cases lookup : decodeOperands Γ (outputs.map scalar) returned with
    | error e => simp [denoteInstructions, RawProgram.denote, lookup]; rfl
    | ok arguments =>
      simp [denoteInstructions, RawProgram.denote, lookup, Meaning.interpretation,
        PIR.Proc.bind, decodeVariable, Var.decode, Environment.push]
  | cons instruction rest ih =>
    cases instruction with
    | apply op indices =>
      cases tail : lower outputs returned rest with
      | error e => simp [lower, tail] at lowered; cases lowered
      | ok next =>
        simp [lower, tail] at lowered
        cases lowered
        cases lookup : decodeOperands Γ (op.arguments.map scalar) indices with
        | error e => simp [denoteInstructions, RawProgram.denote, lookup]; rfl
        | ok arguments =>
          simp only [denoteInstructions, lookup, RawProgram.denote, Meaning.interpretation]
          congr 1
          funext reply
          exact ih next tail (env.push reply)
    | project types index tuple =>
      by_cases range : index < types.length
      · cases tail : lower outputs returned rest with
        | error e => simp [lower, range, tail] at lowered; cases lowered
        | ok next =>
          simp [lower, range, tail] at lowered
          cases lowered
          cases lookup : decodeVariable Γ types tuple with
          | error e =>
              simp [denoteInstructions, range, lookup, RawProgram.denote, decodeOperands]
              rfl
          | ok value =>
              simp only [denoteInstructions, range, ↓reduceDIte, lookup]
              simp only [RawProgram.denote, language, decodeOperands, lookup,
                Meaning.interpretation]
              exact ih next tail _
      · simp [lower, range] at lowered
    | guard index attributes =>
      cases tail : lower outputs returned rest with
      | error e => simp [lower, tail] at lowered; cases lowered
      | ok next =>
        simp [lower, tail] at lowered
        cases lowered
        cases lookup : decodeVariable Γ ["i1"] index with
        | error e => simp [denoteInstructions, RawProgram.denote, lookup]; rfl
        | ok value =>
          simp only [denoteInstructions, lookup, RawProgram.denote, Meaning.interpretation]
          rw [ih next tail env]
          congr 1
          cases env value with
          | cons condition remaining => cases remaining; rfl
    | stop reason attributes =>
      by_cases valid : (rest.isEmpty && returned.isEmpty) = true
      · simp [lower, valid] at lowered
        cases lowered
        simp [denoteInstructions, valid, RawProgram.denote]
        rfl
      · simp [lower, valid] at lowered

def Snapshot.execute (snapshot : Snapshot) (meaning : Meaning I)
    (inputs : Values (Values meaning.Value) (snapshot.inputs.map scalar)) :
    PIR.Proc I (Values meaning.Value snapshot.outputs) :=
  denoteInstructions meaning snapshot.outputs snapshot.returned snapshot.instructions inputs.get

/-- The complete selected source carrier, before lowering or typed elaboration,
has the imported body's denotation under any fixed primitive meaning. -/
theorem Snapshot.check_execute {snapshot : Snapshot} {imported : Imported snapshot}
    (checked : snapshot.check = .ok imported) (meaning : Meaning I)
    (inputs : Values (Values meaning.Value) (snapshot.inputs.map scalar)) :
    snapshot.execute meaning inputs = imported.denote meaning inputs := by
  exact (lower_denotation meaning snapshot.outputs snapshot.returned snapshot.instructions
    imported.program.erase (Snapshot.check_exact checked) inputs.get).trans
      (imported.program.denote_erase meaning.interpretation inputs.get)

end Zkc.Source.Constructed
