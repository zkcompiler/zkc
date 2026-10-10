import Zkc.Protocols.Sumcheck.Endpoints.Prover
import Zkc.Protocols.Sumcheck.Endpoints.Verifier
import Zkc.Protocols.Sumcheck.Framed

/-! Local-to-global composition under the supplied synchronous delivery driver.

Every prover action and pure verifier step executes its bound local source.
The driver delivers each received message and each actual challenge to the next
local step. Complete execution equals the global source, including terminal
acceptance, failed providers, ordered events and residual prover/provider state.
No general endpoint-projection or asynchronous-progress theorem is asserted.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Endpoints.Composition

open PIR Zkc.Source Zkc.Polynomial
open AlgebraicRounds (Message)

variable {F S Q : Type} {n : Nat}

section Semiring
variable [CommSemiring F] [DecidableEq F]

def operation (op : Source.Op) (args : Values (Source.Value F n) (Source.arguments op)) :
    Proc (AlgebraicRounds.interface F) (Source.Value F n (Source.result op)) := match op with
  | .receive => Source.meaning.operation .receive args
  | .draw => Source.meaning.operation .draw args
  | .reject => Source.meaning.operation .reject args
  | .check => match args with
    | .cons message (.cons accumulator .nil) => .done (Verifier.boundCheck (n := n) message accumulator)
  | .advance => match args with
    | .cons message (.cons r (.cons accumulator .nil)) =>
        .done (Verifier.boundAdvance (n := n) message r accumulator)
  | .terminal => match args with
    | .cons p (.cons accumulator .nil) => .done (Verifier.boundTerminal p accumulator)

abbrev meaning : Interpretation Source.language (AlgebraicRounds.interface F) where
  Value := Source.Value F n
  condition := id
  operation := operation

theorem operation_exact : operation (F := F) (n := n) =
    (Source.meaning (F := F) (n := n)).operation := by
  funext op args
  cases op with
  | receive | draw | reject => rfl
  | check =>
      cases args with
      | cons message args =>
          cases args with
          | cons accumulator args => cases args; rfl
  | advance =>
      cases args with
      | cons message args =>
          cases args with
          | cons r args =>
              cases args with
              | cons accumulator args => cases args; rfl
  | terminal =>
      cases args with
      | cons p args =>
          cases args with
          | cons accumulator args => cases args; rfl

theorem denotation_exact {Γ ty} (program : Program Source.language Γ ty)
    (env : Environment (Source.Value F n) Γ) :
    program.denote meaning env = program.denote Source.meaning env := by
  unfold meaning
  rw [operation_exact (n := n)]

def runFresh (send : S → Message F × S) (react : S → F → S)
    (p : Quadratic F n) (claim : F) (prover : S) (coins : List F) :
    PIR.Execution (S × List F) (AlgebraicRounds.Construction.Event F) Bool :=
  ((Source.program n).denote (meaning.translate AlgebraicRounds.Construction.fresh)
    (Values.cons (ty := Source.Ty.accumulator) ⟨claim, []⟩
      (Values.cons (ty := Source.Ty.polynomial) p .nil)).get).run
    (AlgebraicRounds.Fresh.handler (Prover.boundSend send react) (Prover.boundReact send react)
      Execution.draw) (prover, coins)

theorem fresh_exact (send : S → Message F × S) (react : S → F → S)
    (p : Quadratic F n) (claim : F) (prover : S) (coins : List F) :
    runFresh send react p claim prover coins = Execution.run send react p claim prover coins := by
  simp only [runFresh, Execution.run, Program.denote_translate, denotation_exact (n := n),
    Prover.boundSend_exact, Prover.boundReact_exact]

def runFramed (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : AlgebraicRounds.Construction.Query F Q) (p : Quadratic F n) (claim : F)
    (prover : S) (provider : Q) :
    PIR.Execution (AlgebraicRounds.Framed.State F S Q) (AlgebraicRounds.Construction.Event F) Bool :=
  ((Source.program n).denote (meaning.translate AlgebraicRounds.Construction.framed)
    (Values.cons (ty := Source.Ty.accumulator) ⟨claim, []⟩
      (Values.cons (ty := Source.Ty.polynomial) p .nil)).get).run
    (AlgebraicRounds.Framed.handler (Prover.boundSend send react) (Prover.boundReact send react) query)
    (Framed.initial domain p claim prover provider)

theorem framed_exact (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : AlgebraicRounds.Construction.Query F Q) (p : Quadratic F n) (claim : F)
    (prover : S) (provider : Q) :
    runFramed domain send react query p claim prover provider =
      Framed.run domain send react query p claim prover provider := by
  simp only [runFramed, Framed.run, Program.denote_translate, denotation_exact (n := n),
    Prover.boundSend_exact, Prover.boundReact_exact]

end Semiring

section Probability
variable [Field F] [Fintype F] [DecidableEq F]

def acceptance (send : S → Message F × S) (react : S → F → S)
    (p : Quadratic F n) (claim : F) (prover : S) : ℚ :=
  Zkc.Probability.UniformTape.average n (fun coins =>
    if (runFresh send react p claim prover (tapeList n coins)).outcome = .returned true then 1 else 0)

theorem acceptance_exact (send : S → Message F × S) (react : S → F → S)
    (p : Quadratic F n) (claim : F) (prover : S) :
    acceptance send react p claim prover = Security.sourceAcceptance send react p claim prover := by
  simp only [acceptance, Security.sourceAcceptance, fresh_exact]

theorem soundness (send : S → Message F × S) (react : S → F → S)
    (p : Quadratic F n) (claim : F) (prover : S) (falseClaim : claim ≠ p.booleanSum) :
    acceptance send react p claim prover ≤ (2 * (n : ℚ)) / Fintype.card F := by
  rw [acceptance_exact]
  exact Security.source_soundness send react p claim prover falseClaim

theorem perfect_completeness (p : Quadratic F n) :
    acceptance Security.honestSend Security.honestReact p p.booleanSum ⟨n, p⟩ = 1 := by
  rw [acceptance_exact, Security.source_perfect_completeness]

end Probability
end Zkc.Protocols.Sumcheck.Endpoints.Composition
