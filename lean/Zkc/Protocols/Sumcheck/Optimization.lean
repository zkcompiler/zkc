import Zkc.Protocols.Sumcheck.Security
import Zkc.Compiler.Arithmetic.Horner

/-! A checked verifier-evaluation plan and complete security transport.

The child source takes the actual message coefficients and delivered challenge.
Its independently supplied candidate computes two multiplications and two adds.
The parent source executes that checked plan on each round; the fixed polynomial,
message checks, challenge timing and terminal operands are retained.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Optimization

open PIR Zkc.Source Zkc.Compiler
open AlgebraicRounds (Message)

abbrev noEffects : Signature := ⟨Empty, fun op => nomatch op⟩
def noHandler : Handler noEffects Unit Empty := fun op => nomatch op

abbrev arguments : List Zkc.Source.Arithmetic.Ty := [.scalar, .scalar, .scalar, .scalar]

def evaluationSource : Program Zkc.Source.Arithmetic.language arguments .scalar :=
  .letOp .quadratic
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil)))) (.ret .here)

/-- Independent serialized candidate: `a + (b + c*r)*r`. -/
def candidate : RawProgram Zkc.Source.Arithmetic.Ty Zkc.Source.Arithmetic.Op :=
  .letOp .multiply [2, 3]
    (.letOp .add [2, 0]
      (.letOp .multiply [0, 5]
        (.letOp .add [3, 0] (.ret 0))))

variable {F : Type}

section Semiring
variable [Semiring F]

abbrev localMeaning : Interpretation Zkc.Source.Arithmetic.language noEffects :=
  Zkc.Source.Arithmetic.interpretation (fun x : F => .done x)

/-- The plan actually consumed below is the checker result. No fallback plan
or unchecked interpretation is selected when candidate validation fails. -/
def checked : CheckedTransformation
    (Refinement.exact (Arithmetic.Horner.model (fun x : F => .done x) noHandler) arguments .scalar)
    evaluationSource candidate :=
  (checkTransformation (Arithmetic.Horner.rule (fun x : F => .done x) noHandler arguments .scalar)
    evaluationSource () candidate).get (by rfl)

theorem checked_plan : (checked (F := F)).plan = lower (Arithmetic.Horner.rewrite evaluationSource) := rfl

def inputs (message : Message F) (r : F) : Values (Zkc.Source.Arithmetic.Value F) arguments :=
  .cons message.constant (.cons message.linear (.cons message.quadratic (.cons r .nil)))

theorem evaluation_execution (message : Message F) (r : F) :
    (checked (F := F)).plan.run localMeaning noHandler (inputs message r).get () =
      ⟨.returned (message.evaluate r), (), []⟩ := by
  rw [checked_plan, lower_correct, Arithmetic.Horner.denote_rewrite]
  rfl

def evaluate (message : Message F) (r : F) : Outcome F :=
  ((checked (F := F)).plan.run localMeaning noHandler (inputs message r).get ()).outcome

theorem evaluate_exact (message : Message F) (r : F) :
    evaluate message r = .returned (message.evaluate r) := by
  exact congrArg PIR.Execution.outcome (evaluation_execution message r)

end Semiring

section Commutative
variable [CommSemiring F] [DecidableEq F] {n : Nat}

def operation (op : Source.Op) (args : Values (Source.Value F n) (Source.arguments op)) :
    Proc (AlgebraicRounds.interface F) (Source.Value F n (Source.result op)) :=
  match op with
  | .advance => match args with
    | .cons message (.cons r (.cons accumulator .nil)) =>
        match evaluate message r with
        | .stopped why => .halt why
        | .returned value => .done ⟨value, accumulator.challenges ++ [r]⟩
  | .receive => Source.meaning.operation .receive args
  | .draw => Source.meaning.operation .draw args
  | .check => Source.meaning.operation .check args
  | .reject => Source.meaning.operation .reject args
  | .terminal => Source.meaning.operation .terminal args

abbrev meaning : Interpretation Source.language (AlgebraicRounds.interface F) where
  Value := Source.Value F n
  condition := id
  operation := operation

theorem operation_exact : operation (F := F) (n := n) =
    (Source.meaning (F := F) (n := n)).operation := by
  funext op args
  cases op with
  | advance =>
      cases args with
      | cons message args =>
          cases args with
          | cons r args =>
              cases args with
              | cons accumulator args =>
                  cases args
                  change (match evaluate message r with
                    | .stopped why => Proc.halt why
                    | .returned value => Proc.done (⟨value, accumulator.challenges ++ [r]⟩ : Source.Accumulator F)) = _
                  rw [evaluate_exact]
                  rfl
  | receive | draw | check | reject | terminal => rfl

/-- Complete source execution is preserved for any handler and any construction,
not only for honestly generated messages or accepting inputs. -/
theorem denotation_exact {Γ ty} (source : Program Source.language Γ ty)
    (env : Environment (Source.Value F n) Γ) :
    source.denote meaning env = source.denote Source.meaning env := by
  unfold meaning
  rw [operation_exact (n := n)]

def run {S : Type} (send : S → Message F × S) (react : S → F → S)
    (p : Zkc.Polynomial.Quadratic F n) (claim : F) (prover : S) (coins : List F) :
    PIR.Execution (S × List F) (AlgebraicRounds.Construction.Event F) Bool :=
  ((Source.program n).denote (meaning.translate AlgebraicRounds.Construction.fresh)
    (Values.cons (ty := Source.Ty.accumulator) ⟨claim, []⟩
      (Values.cons (ty := Source.Ty.polynomial) p .nil)).get).run
    (AlgebraicRounds.Fresh.handler send react Execution.draw) (prover, coins)

theorem run_exact {S : Type} (send : S → Message F × S) (react : S → F → S)
    (p : Zkc.Polynomial.Quadratic F n) (claim : F) (prover : S) (coins : List F) :
    run send react p claim prover coins = Execution.run send react p claim prover coins := by
  simp only [run, Execution.run, Program.denote_translate, denotation_exact (n := n)]

end Commutative

section Probability
variable [Field F] [Fintype F] [DecidableEq F] {n : Nat}

/-- Acceptance of the source that actually executes the checked child plan. -/
def acceptance {S : Type} (send : S → Message F × S) (react : S → F → S)
    (p : Zkc.Polynomial.Quadratic F n) (claim : F) (prover : S) : ℚ :=
  Zkc.Probability.UniformTape.average n (fun coins =>
    if (run send react p claim prover (tapeList n coins)).outcome = .returned true then 1 else 0)

theorem acceptance_exact {S : Type} (send : S → Message F × S) (react : S → F → S)
    (p : Zkc.Polynomial.Quadratic F n) (claim : F) (prover : S) :
    acceptance send react p claim prover = Security.sourceAcceptance send react p claim prover := by
  simp only [acceptance, Security.sourceAcceptance, run_exact]

/-- The verifier changes; the adversary map is the identity on all supplied
prover callbacks and states. Whole-execution equality supplies event equality. -/
theorem soundness {S : Type} (send : S → Message F × S) (react : S → F → S)
    (p : Zkc.Polynomial.Quadratic F n) (claim : F) (prover : S) (falseClaim : claim ≠ p.booleanSum) :
    acceptance send react p claim prover ≤ (2 * (n : ℚ)) / Fintype.card F := by
  rw [acceptance_exact]
  exact Security.source_soundness send react p claim prover falseClaim

theorem perfect_completeness (p : Zkc.Polynomial.Quadratic F n) :
    acceptance Security.honestSend Security.honestReact p p.booleanSum ⟨n, p⟩ = 1 := by
  rw [acceptance_exact, Security.source_perfect_completeness]

end Probability
end Zkc.Protocols.Sumcheck.Optimization
