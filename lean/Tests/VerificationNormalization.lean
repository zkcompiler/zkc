module

public import Tests.SourceValidation
public import Zkc.Source.Verification
public import Zkc.Source.ContractAutomation

@[expose] public section
namespace VerificationNormalizationTests
open Zkc.Source Zkc.Verification SourceValidationTests

/-- Library/reference and authored source are independently admitted. -/
def target : Imported (RawProgram.elaborate (language := language) [()] ()) expanded where
  program := (expanded.elaborate (language := language) [()] ()).toOption.get (by decide +kernel)
  admitted := rfl

def actual : Imported (RawProgram.elaborate (language := language) [()] ()) original where
  program := (original.elaborate (language := language) [()] ()).toOption.get (by decide +kernel)
  admitted := rfl

def contract (model : Environment meaning.Value [()] → PIR.Proc interface Nat) : Prop :=
  ∀ env, model env = target.program.denote meaning env

theorem certified : Certificate actual (fun p env => p.denote meaning env) contract :=
  normalizer.certificate actual target contract (fun _ => rfl) (by decide +kernel)

/-- A new consumer composes with normalization without knowing helper syntax. -/
def queryPreserved : Property (Environment meaning.Value [()] → PIR.Proc interface Nat) where
  assumptions _ := True
  conclusion model := ∀ input, model (inputValues input).get = .call (input + 2) .done

theorem queryConsumer : Consumer contract queryPreserved := by
  constructor
  intro model conforms _ input
  rw [conforms]
  change (if input + 1 + 1 != 0 then PIR.Proc.call (input + 1 + 1) PIR.Proc.done
    else PIR.Proc.halt .reject) = _
  simp [Nat.add_assoc]

example : queryPreserved.conclusion (fun env => actual.program.denote meaning env) :=
  certified.verify queryConsumer trivial

/-- Pure algebra may vary inside a fixed effect; effect order cannot. -/
example {F : Type} [CommRing F] (a b c x : F) :
    (PIR.Proc.call (I := interface) 7 fun _ => PIR.Proc.done (a + x * (b + x * c))) =
      PIR.Proc.call (I := interface) 7 (fun _ => PIR.Proc.done (a + x * b + x * x * c)) := by
  zkc_contract

example {G : Type} [AddCommGroup G] (a b : G) :
    (PIR.Proc.call (I := interface) 7 fun _ => PIR.Proc.done (a + b)) =
      PIR.Proc.call (I := interface) 7 (fun _ => PIR.Proc.done (b + a)) := by
  zkc_contract

/- Refusal controls must fail as proofs, not time out or add assumptions. -/
set_option linter.unreachableTactic false in
example : True := by
  fail_if_success have : (PIR.Proc.call (I := interface) 1 PIR.Proc.done) =
      PIR.Proc.call (I := interface) 2 PIR.Proc.done := by zkc_contract
  fail_if_success have : normalizer.check [()] () original staleOperand = true := by decide +kernel
  trivial

end VerificationNormalizationTests
