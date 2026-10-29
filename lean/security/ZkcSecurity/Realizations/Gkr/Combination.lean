module

public import ZkcSecurity.Families.Gkr.Combination
public import ZkcExamples.Structured.GkrVerifierProcess

public section
noncomputable section

namespace ZkcSecurity.Realizations.Gkr.Combination
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Construction
open ZkcSecurity.Families.Gkr
open ZkcExamples.Structured
open Zkc.Source.Structured

variable {F G : Type} [Field F] [DecidableEq F] {width : Nat}

structure Invocation (F : Type) (width : Nat) where
  add : Zkc.Protocols.Gkr.Wiring F width
  mul : Zkc.Protocols.Gkr.Wiring F width
  state : GkrVerifier.State F
  left : List F
  right : List F
  claim : F
  first : F
  coefficients : List F

@[expose] def gateClaim (below : Table F width) (runtime : Invocation F width) : Prop :=
  runtime.claim = GkrVerifier.wiringValue
    (extension (width + width + width) runtime.add
      (coordinates (width + width + width) (runtime.state.2.1 ++ runtime.left ++ runtime.right)))
    (extension (width + width + width) runtime.mul
      (coordinates (width + width + width) (runtime.state.2.1 ++ runtime.left ++ runtime.right)))
    (extension width below (coordinates width runtime.left))
    (extension width below (coordinates width runtime.right))

end ZkcSecurity.Realizations.Gkr.Combination
