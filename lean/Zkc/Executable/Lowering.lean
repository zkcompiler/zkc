module

public import Zkc.Construction.Semantics
public import Zkc.Executable.Reading
public import Zkc.Executable.Decoding

@[expose] public section

/-! Compatibility metering for consumers awaiting migration to DomainVM.
The canonical Code runner and its Process laws live in DomainLowering,
DomainSoundness and DomainCompleteness. Structural reading, scope admission
and byte decoding are owned by independent leaves. -/
set_option autoImplicit false
namespace Zkc.Executable
open Zkc.Construction Zkc.Source

section Metered
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

/-- Iterate a metered loop body over the given induction values: each iteration
then charges one instruction to yield its carried values. -/
def meteredIterate {R : Type}
    (body : List (Value F G) → Proof F G → Nat →
      (List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
        m (PIR.Outcome R × Proof F G))
    (env : List (Value F G)) (yielded : List Nat) :
    List Nat → List (Value F G) → Proof F G → Nat →
      (List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
        m (PIR.Outcome R × Proof F G)
  | [], carried, proof, used, next => next carried proof used
  | index :: rest, carried, proof, used, next =>
      body (env ++ .index index :: carried) proof used fun final unread used' =>
        if used' + 1 ≤ budget then
          match read final yielded with
          | some carried' => meteredIterate body env yielded rest carried' unread (used' + 1) next
          | none => pure (.stopped .refused, unread)
        else pure (.stopped .exhausted, unread)

mutual
/-- The ideal meaning of a reading under an instruction budget, in continuation
style: `used` counts the instructions charged so far. -/
def meteredK {R : Type} : List Code → List (Value F G) → Proof F G → Nat →
    (List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
      m (PIR.Outcome R × Proof F G)
  | [], env, proof, used, next => next env proof used
  | code :: rest, env, proof, used, next =>
      meteredStep code env proof used fun env' unread used' => meteredK rest env' unread used' next

def meteredStep {R : Type} : Code → List (Value F G) → Proof F G → Nat →
    (List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
      m (PIR.Outcome R × Proof F G)
  | .charge count, env, proof, used, next =>
      if used + count ≤ budget then next env proof (used + count)
      else pure (.stopped .exhausted, proof)
  | .step instruction charged, env, proof, used, next =>
      if used + charged ≤ budget then
        idealStep context challenge table instruction env proof fun env' unread =>
          next env' unread (used + charged)
      else pure (.stopped .exhausted, proof)
  | .helper instruction, env, proof, used, next =>
      if used + 1 ≤ budget then
        match instruction.operation, read env instruction.operands with
        | .call helper, some arguments =>
            if used + 1 + cost helper arguments ≤ budget then
              idealStep context challenge table instruction env proof fun env' unread =>
                next env' unread (used + 1 + cost helper arguments)
            else pure (.stopped .exhausted, proof)
        | _, _ => pure (.stopped .refused, proof)
      else pure (.stopped .exhausted, proof)
  | .loop _ maximum yielded operands _ body, env, proof, used, next =>
      match operands with
      | count :: initial =>
          match indexAt env count, read env initial with
          | some bound, some carried =>
              if bound ≤ maximum then
                if used + 1 ≤ budget then
                  meteredIterate budget (fun start unread used' continuation =>
                      meteredK body start unread used' continuation) env yielded
                    (List.range bound) carried proof (used + 1) fun final unread used' =>
                      next (env ++ final) unread used'
                else pure (.stopped .exhausted, proof)
              else pure (.stopped .refused, proof)
          | _, _ => pure (.stopped .refused, proof)
      | [] => pure (.stopped .refused, proof)
end

/-- The metered meaning of a reading: its instructions, then the final return,
which charges one instruction. -/
def metered (lowered : Lowered) (env : List (Value F G)) (proof : Proof F G) :
    m (PIR.Outcome (List (Value F G)) × Proof F G) :=
  meteredK context challenge table cost budget lowered.code env proof 0 fun final unread used =>
    pure (if used + 1 ≤ budget then finish lowered.returned final else .stopped .exhausted, unread)

end Metered

end Zkc.Executable
