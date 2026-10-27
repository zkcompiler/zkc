module

public import Zkc.Obligations.ClaimRelation
public import Zkc.Protocols.Gkr.Circuit

public section

/-! Independent circuit and evaluation claims. The circuit
is a fixed logical reference; none of these definitions adds a verifier input.
The concrete four-factor attachment belongs to the realization module.
-/

namespace ZkcSecurity.Families.Gkr
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr
open Zkc.Obligations

variable {F : Type} [CommRing F] {width : Nat}

structure Circuit (F : Type) [CommRing F] (width : Nat) where
  inputs : Table F width
  add : Nat → Wiring F width
  mul : Nat → Wiring F width

namespace Circuit

@[expose] def wires (circuit : Circuit F width) (remaining index : Nat) : Table F width :=
  values circuit.add circuit.mul circuit.inputs remaining index

end Circuit

structure Evaluation (F : Type) (width : Nat) where
  point : Fin width → F
  claim : F

@[expose] def evaluationRelation (table : Table F width) : ClaimRelation (Evaluation F width) Unit :=
  .exact fun evaluation _ => evaluation.claim = extension width table evaluation.point

end ZkcSecurity.Families.Gkr
