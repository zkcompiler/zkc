module

public import Zkc.Source.Structured.ProtocolReturnSpecification
public import Zkc.Source.Structured.OracleProtocol

@[expose] public section

/-! The linked return rule derives both masks from the actual declaration.
A returned local value must not leak through a foreign output port. -/
set_option autoImplicit false
namespace Tests.ProtocolReturnSpecification
open Zkc.Source Zkc.Source.Structured

def signature : ProtocolSignature :=
  { name := "swap-and-restrict", roles := ["left", "right"],
    inputs := [.index, .index], outputs := [.index, .index],
    inputScopes := [[0], [0]], outputScopes := [[0], [1]] }

def body : Region protocolDialect signature.inputs signature.outputs :=
  .ret (.cons (.there .here) (.cons .here .nil))

def definition : CheckedProtocol :=
  { toProtocolSignature := signature, raw := body.erase, body := body, formed := body.elaborate_erase }

theorem linked : ProtocolDeclarationsLinked [] [] [definition] := by decide

variable {model : DomainModel} {I : PIR.Signature}
  (algebra : ProtocolAlgebra model.Value I)
  {M : Type → Type} [Monad M] [LawfulMonad M] {S E : Type}
  (handler : PIR.MonadHandler M I S E) (invariant : S → Prop)

theorem installed (first second : Nat) :
    PIR.Process.ReturnsUnder handler invariant
      (invokeProtocol ([definition].foldl algebra.extend []) signature {} 0
        (.cons (some first) (.cons (some second) .nil)))
      (.cons (some second) (.cons none .nil)) := by
  apply algebra.invokeReturns linked definition (by simp)
    (expected := .cons (some second) (.cons (some first) .nil))
  exact Region.ReturnsSatisfying.ret rfl

/-- Refusing to erase a foreign output is a semantic violation, even though
both ports have the same index type. This checks the actual process equation. -/
theorem no_foreign_output (first second : Nat) :
    invokeProtocol ([definition].foldl algebra.extend []) signature {} 0
      (.cons (some first) (.cons (some second) .nil)) ≠
      .done (.cons (some second) (.cons (some first) .nil)) := by
  erw [algebra.invokeBody linked definition (by simp)]
  intro wrong
  cases wrong

#print axioms installed
#print axioms no_foreign_output
end Tests.ProtocolReturnSpecification
