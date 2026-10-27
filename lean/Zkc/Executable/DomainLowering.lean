module

public import Zkc.Executable.Code
public import Zkc.Executable.Observations
public import Zkc.Construction.Uniform.DomainHandler

@[expose] public section

/-! Metered Code execution through the authoritative constructed Process.

The state is nominal throughout execution. In particular transcript suites,
dynamic occurrence coordinates and histories are not reconstructed from the
scalar readback after each step. The initial scalar history remains opaque and
the selected origin map is applied by the handler before the oracle is called.
Code owns instruction charges, helper charges and loop/yield/return charges;
all nonloop constructed work is delegated to `Construction.Domain.step` with
the actual program. No constructed instruction interpreter is defined here.
-/
set_option autoImplicit false

namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source
open Zkc.Construction.Uniform

variable {F G : Type}

abbrev Environment (F G : Type) := Domain.Environment (Structured.uniformCarriers F G)

/-- Helper work is priced at the existing scalar native ABI. Failure to read
that ABI refuses explicitly; no aggregate or wrong sort is replaced by a
default argument. -/
def arguments (values : Environment F G) : Option (List (Value F G)) :=
  values.mapM DomainAdapter.readbackData

section Metered
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (program : Structured.Program) (context : Context)
  (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

/-- The yield is charged after the body and before reading its returned
references, matching the executable loop's failure ordering. -/
def meteredIterate {R : Type}
    (body : Environment F G → Proof F G → Nat →
      (Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
        m (PIR.Outcome R × Proof F G))
    (outer : Environment F G) (yielded : List Nat) (declared : List ValueSort) :
    List Nat → Environment F G → Proof F G → Nat →
      (Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
        m (PIR.Outcome R × Proof F G)
  | [], carried, proof, used, next => next carried proof used
  | index :: rest, carried, proof, used, next =>
      body (outer ++ .data (.index index) :: carried) proof used fun final unread used' =>
        if used' + 1 ≤ budget then
          match Domain.read final yielded with
          | some carried' =>
              if Domain.sortsMatch declared carried' then
                meteredIterate body outer yielded declared rest carried' unread (used' + 1) next
              else pure (.stopped .refused, unread)
          | none => pure (.stopped .refused, unread)
        else pure (.stopped .exhausted, unread)

mutual
def meteredK {R : Type} : List Code → Environment F G → Proof F G → Nat →
    (Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
      m (PIR.Outcome R × Proof F G)
  | [], env, proof, used, next => next env proof used
  | code :: rest, env, proof, used, next =>
      meteredStep code env proof used fun final unread used' => meteredK rest final unread used' next

def meteredStep {R : Type} : Code → Environment F G → Proof F G → Nat →
    (Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
      m (PIR.Outcome R × Proof F G)
  | .charge count, env, proof, used, next =>
      if used + count ≤ budget then next env proof (used + count)
      else pure (.stopped .exhausted, proof)
  | .step instruction charged, env, proof, used, next =>
      if used + charged ≤ budget then
        DomainAdapter.runK key initial challenge
          (Domain.step (Structured.ringModel F G) program context instruction env) proof
          fun final unread => next final unread (used + charged)
      else pure (.stopped .exhausted, proof)
  | .helper instruction, env, proof, used, next =>
      if used + 1 ≤ budget then
        match instruction.operation, Domain.read env instruction.operands with
        | .call name, some values =>
            match arguments values with
            | some scalar =>
                if used + 1 + cost name scalar ≤ budget then
                  DomainAdapter.runK key initial challenge
                    (Domain.step (Structured.ringModel F G) program context instruction env) proof
                    fun final unread => next final unread (used + 1 + cost name scalar)
                else pure (.stopped .exhausted, proof)
            | none => pure (.stopped .refused, proof)
        | _, _ => pure (.stopped .refused, proof)
      else pure (.stopped .exhausted, proof)
  | .loop _ maximum yielded operands declared body, env, proof, used, next =>
      match operands with
      | count :: refs =>
          match env[count]?, Domain.read env refs with
          | some (.data (.index bound)), some carried =>
              if bound ≤ maximum ∧ Domain.sortsMatch declared carried then
                if used + 1 ≤ budget then
                  meteredIterate budget (fun start unread used' continuation =>
                    meteredK body start unread used' continuation) env yielded declared
                    (List.range bound) carried proof (used + 1) fun final unread used' =>
                      if Domain.sortsMatch declared final then next (env ++ final) unread used'
                      else pure (.stopped .refused, unread)
                else pure (.stopped .exhausted, proof)
              else pure (.stopped .refused, proof)
          | _, _ => pure (.stopped .refused, proof)
      | [] => pure (.stopped .refused, proof)
end

/-- The final return is charged before reading its references. Returned sorts
are checked by the selected participant boundary, below. -/
def metered (lowered : Lowered) (env : Environment F G) (proof : Proof F G) :
    m (PIR.Outcome (Environment F G) × Proof F G) :=
  meteredK program context key initial challenge cost budget lowered.code env proof 0
    fun final unread used => pure
      (if used + 1 ≤ budget then
        match Domain.read final lowered.returned with
        | some returned => .returned returned
        | none => .stopped .refused
      else .stopped .exhausted, unread)

/-- An admitted participant's actual input/output schema remains checked even
when Code's internal schedule differs from the exported instruction order. -/
def validate (artifact : Participant) (lowered : Lowered)
    (env : Environment F G) (proof : Proof F G) :
    m (PIR.Outcome (List (Value F G)) × Proof F G) :=
  if Domain.sortsMatch artifact.inputs env then do
    let result ← metered program context key initial challenge cost budget lowered env proof
    pure (match result.1 with
      | .stopped reason => .stopped reason
      | .returned values =>
          if Domain.sortsMatch artifact.outputs values then
            DomainAdapter.readbackOutcome context.suite key initial (.returned values)
          else .stopped .refused, result.2)
  else pure (.stopped .refused, proof)

end Metered
end Zkc.Executable.DomainVM
