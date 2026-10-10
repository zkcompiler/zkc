import Zkc.Protocols.Sumcheck.Source
import Zkc.Semantics.Preparation

/-! Prepared round evaluation in the actual structured Sumcheck source.

The cached value determines the next claim. The key contains the complete
message and delivered point; challenge generation remains an external effect.
The construction is a parameter, so Fresh and framed executions use one law.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Preparation

open PIR Zkc.Source
open AlgebraicRounds (Message)

abbrev Key (F : Type) := Message F × F

variable {F : Type} {I : Signature} {n : Nat} [CommSemiring F] [DecidableEq F]

def provider (price : Key F → Nat) : Zkc.Modules.Preparation.Provider (Key F) F :=
  fun key => (key.1.evaluate key.2, price key)

def operation (construction : OperationInterpretation (AlgebraicRounds.interface F) I)
    (op : Source.Op) (args : Values (Source.Value F n) (Source.arguments op)) :
    Proc (PIR.Preparation.signature (Key F) F I) (Source.Value F n (Source.result op)) :=
  match op with
  | .advance => match args with
    | .cons message (.cons r (.cons accumulator .nil)) =>
        .call (.prepare (message, r)) fun value =>
          .done ⟨value, accumulator.challenges ++ [r]⟩
  | .receive => ((Source.meaning.operation .receive args).interpret construction).interpret
      PIR.Preparation.externalCalls
  | .draw => ((Source.meaning.operation .draw args).interpret construction).interpret
      PIR.Preparation.externalCalls
  | .check => ((Source.meaning.operation .check args).interpret construction).interpret
      PIR.Preparation.externalCalls
  | .reject => ((Source.meaning.operation .reject args).interpret construction).interpret
      PIR.Preparation.externalCalls
  | .terminal => ((Source.meaning.operation .terminal args).interpret construction).interpret
      PIR.Preparation.externalCalls

abbrev meaning (construction : OperationInterpretation (AlgebraicRounds.interface F) I) :
    Interpretation Source.language (PIR.Preparation.signature (Key F) F I) where
  Value := Source.Value F n
  condition := id
  operation := operation construction

theorem resolved_operation (price : Key F → Nat)
    (construction : OperationInterpretation (AlgebraicRounds.interface F) I) :
    ((meaning (n := n) construction).translate (PIR.Preparation.resolve (provider price))).operation =
      (Source.meaning.translate construction).operation := by
  funext op args
  cases op <;> cases args
  case advance.cons message rest =>
    cases rest with
    | cons r rest =>
        cases rest with
        | cons accumulator rest => cases rest; rfl
  case check.cons message rest =>
    cases rest with
    | cons accumulator rest => cases rest; rfl
  case terminal.cons polynomial rest =>
    cases rest with
    | cons accumulator rest => cases rest; rfl
  all_goals
    simp only [meaning, Interpretation.translate, operation, Source.meaning]
    rw [Proc.interpret_comp, Proc.interpret_comp]
    have same : (fun op : I.Op =>
        (PIR.Preparation.externalCalls (K := Key F) (V := F) op).interpret
          (PIR.Preparation.resolve (provider price))) = (fun op => Proc.call op Proc.done) := by
      funext op
      rfl
    simp only [same, Proc.interpret_identity]

theorem resolved_source (price : Key F → Nat)
    (construction : OperationInterpretation (AlgebraicRounds.interface F) I)
    {Γ ty} (source : Program Source.language Γ ty) (env : Environment (Source.Value F n) Γ) :
    (source.denote (meaning construction) env).interpret (PIR.Preparation.resolve (provider price)) =
      source.denote (Source.meaning.translate construction) env := by
  rw [← Program.denote_translate]
  change source.denote
    ⟨Source.Value F n, id,
      ((meaning construction).translate (PIR.Preparation.resolve (provider price))).operation⟩ env = _
  rw [resolved_operation]

/-- Full outcome, protocol state and ordered events reach the original source.
The theorem applies to any typed source in this vocabulary and every valid cache. -/
theorem execution {S E : Type} (price : Key F → Nat)
    (prices : Zkc.Modules.Preparation.Prices (Key F) F) (mode : Zkc.Modules.Preparation.Mode)
    (construction : OperationInterpretation (AlgebraicRounds.interface F) I)
    (external : Handler I S E) {Γ ty} (source : Program Source.language Γ ty)
    (env : Environment (Source.Value F n) Γ) (cache : Zkc.Modules.Preparation.Cache (Key F) F)
    (state : S) (valid : Zkc.Modules.Preparation.Valid (provider price) cache) :
    Related (PIR.Preparation.Represents (provider price)) (fun event => [event]) PIR.Preparation.view
      ((source.denote (Source.meaning.translate construction) env).run external state)
      ((source.denote (meaning construction) env).run
        (PIR.Preparation.handler (provider price) prices mode external) (cache, state)) := by
  have law := PIR.Preparation.resolved_execution (provider price) prices mode external
    (source.denote (meaning construction) env) cache state valid
  rw [resolved_source] at law
  exact law

end Zkc.Protocols.Sumcheck.Preparation
