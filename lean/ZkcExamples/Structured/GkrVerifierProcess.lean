module

public import Zkc.Construction.FiatShamir
public import Zkc.Source.Structured.ProtocolContext
public import Zkc.Protocols.Gkr.Circuit
public import Zkc.Polynomial.Multilinear.Line

@[expose] public section

/-! The plain GKR verifier process over the common participant actions.

This is the verifier of the GKR library (`libraries/gkr/lib.zkc`) for an
admitted statement, written with the library's qualified action sites: the
output-point challenges and their deliveries, then for each layer two
applications of the degree-two Sumcheck rounds (three received coefficients,
the round check, a challenge and its delivery per round), the constant and the
remaining coefficients of the line polynomial, the wiring check, the line
challenge and its delivery, and finally the input check. Mathematical helper
computations appear through their values: extensions of the statement's tables
at the points the verifier holds, the coefficient sum `q(1)`, the power sum
`q(t)` and the line point. Replies and service behavior are unrestricted.
-/

set_option autoImplicit false

namespace ZkcExamples.Structured.GkrVerifier
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr

/-- The scalar field of the library's Entry. -/
abbrev scalar : Common.Native.Ty := .field "bls12-381.fr"

/-! ## Qualified sites -/

abbrev outputSite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_6f7574707574"

abbrev outputDeliverySite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_6f75747075745f64656c6976657279_0"

/-- The contexts of the two `Rounds` applications of a layer. -/
abbrev leftContext (ctx : ProtocolContext) : ProtocolContext := ctx.enter "label_6c656674" [0, 1]
abbrev rightContext (ctx : ProtocolContext) : ProtocolContext := ctx.enter "label_7269676874" [0, 1]

abbrev roundSite (ctx : ProtocolContext) (position : String) : String :=
  qualifyProtocolSite ctx.applicationPrefix ("label_726f756e64_" ++ position)

abbrev challengeSite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_6368616c6c656e6765"

abbrev deliverySite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_64656c6976657279_0"

abbrev lineConstantSite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_6c696e655f636f6e7374616e74_0"

abbrev lineCoefficientSite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_6c696e655f636f656666696369656e74_0"

abbrev lineChallengeSite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_6c696e655f6368616c6c656e6765"

abbrev lineDeliverySite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_6c696e655f64656c6976657279_0"

variable {F G : Type} [CommRing F] [DecidableEq F]

/-! ## Values the verifier's helpers compute

The coefficient sum `q(1)`, the power sum `q(t)` (`powerSum`) and the line
point (`linePoints`) are the values of the library's helpers. -/

/-- The wiring check of a layer: `add (q(0) + q(1)) + mul q(0) q(1)`. -/
def wiringValue (addValue mulValue first total : F) : F :=
  addValue * (first + total) + mulValue * first * total

/-! ## The process -/

/-- The delivery of an output-point challenge. -/
def outputDelivery (ctx : ProtocolContext) (point : List F) (r : F) :
    PIR.Proc (Actions F G) (List F) :=
  .call (.send (ty := scalar) (outputDeliverySite ctx) (ctx.roles 0) r) fun _ =>
  .done (point ++ [r])

/-- One output-point challenge and its delivery. -/
def outputRound (ctx : ProtocolContext) (handle : Nat) (point : List F) :
    PIR.Proc (Actions F G) (List F) :=
  .call (.query (outputSite ctx) "bls12-381.fr" (.cons handle .nil)) (outputDelivery ctx point)

/-- A round challenge's delivery and the claim `g(r) = c0 + r (c1 + r c2)`. -/
def roundChallenge (ctx : ProtocolContext) (state : List F × F) (c0 c1 c2 r : F) :
    PIR.Proc (Actions F G) (List F × F) :=
  .call (.send (ty := scalar) (deliverySite ctx) (ctx.roles 0) r) fun _ =>
  .done (state.1 ++ [r], c0 + r * (c1 + r * c2))

/-- The round check `g(0) + g(1) = 2 c0 + c1 + c2` against the current claim,
then the round challenge. -/
def roundCheck (ctx : ProtocolContext) (handle : Nat) (state : List F × F) (c0 c1 c2 : F) :
    PIR.Proc (Actions F G) (List F × F) :=
  if state.2 = c0 + c0 + c1 + c2 then
    .call (.query (challengeSite ctx) "bls12-381.fr" (.cons handle .nil))
      (roundChallenge ctx state c0 c1 c2)
  else .halt .reject

def roundSecond (ctx : ProtocolContext) (handle : Nat) (state : List F × F) (c0 c1 : F) :
    PIR.Proc (Actions F G) (List F × F) :=
  .call (.receive scalar (roundSite ctx "2") (ctx.roles 0)) (roundCheck ctx handle state c0 c1)

def roundFirst (ctx : ProtocolContext) (handle : Nat) (state : List F × F) (c0 : F) :
    PIR.Proc (Actions F G) (List F × F) :=
  .call (.receive scalar (roundSite ctx "1") (ctx.roles 0)) (roundSecond ctx handle state c0)

/-- One degree-two Sumcheck round: the coefficients `(c0, c1, c2)` of the round
polynomial, the round check, the challenge `r`, its delivery and the claim
`g(r)`. -/
def round (ctx : ProtocolContext) (handle : Nat) (state : List F × F) :
    PIR.Proc (Actions F G) (List F × F) :=
  .call (.receive scalar (roundSite ctx "0") (ctx.roles 0)) (roundFirst ctx handle state)

/-- One `Rounds` application: `count` rounds from the empty point. -/
def rounds (ctx : ProtocolContext) (handle count : Nat) (claim : F) :
    PIR.Proc (Actions F G) (List F × F) :=
  PIR.repeatN count (round ctx handle) ([], claim)

/-- One further coefficient of the line polynomial. -/
def lineCoefficient (ctx : ProtocolContext) (coefficients : List F) :
    PIR.Proc (Actions F G) (List F) :=
  .call (.receive scalar (lineCoefficientSite ctx) (ctx.roles 0)) fun coefficient =>
  .done (coefficients ++ [coefficient])

/-- The verifier's state between layers: the layer index, its point and claim. -/
abbrev State (F : Type) := Nat × List F × F

/-- The line challenge's delivery and the next layer's point and claim. -/
def lineDelivery (ctx : ProtocolContext) (state : State F) (left right coefficients : List F) (t : F) :
    PIR.Proc (Actions F G) (State F) :=
  .call (.send (ty := scalar) (lineDeliverySite ctx) (ctx.roles 0) t) fun _ =>
  .done (state.1 + 1, linePoints left right t, powerSum coefficients t)

/-- The wiring check of a layer after its rounds and coefficients, then the line
challenge. -/
def lineCheck (ctx : ProtocolContext) (handle width : Nat) (add mul : Wiring F width)
    (state : State F) (left right : List F) (claim first : F) (coefficients : List F) :
    PIR.Proc (Actions F G) (State F) :=
  if claim = wiringValue
      (extension (width + width + width) add
        (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
      (extension (width + width + width) mul
        (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
      first coefficients.sum then
    .call (.query (lineChallengeSite ctx) "bls12-381.fr" (.cons handle .nil))
      (lineDelivery ctx state left right coefficients)
  else .halt .reject

/-- The remaining coefficients of the line polynomial and the wiring check. -/
def layerAfterConstant (ctx : ProtocolContext) (handle width : Nat) (add mul : Nat → Wiring F width)
    (state : State F) (left right : List F × F) (first : F) : PIR.Proc (Actions F G) (State F) :=
  (PIR.repeatN width (lineCoefficient ctx) [first]).bind
    (lineCheck ctx handle width (add state.1) (mul state.1) state left.1 right.1 right.2 first)

/-- The line polynomial's constant term, then the rest of the layer. -/
def layerAfterRight (ctx : ProtocolContext) (handle width : Nat) (add mul : Nat → Wiring F width)
    (state : State F) (left right : List F × F) : PIR.Proc (Actions F G) (State F) :=
  .call (.receive scalar (lineConstantSite ctx) (ctx.roles 0))
    (layerAfterConstant ctx handle width add mul state left right)

/-- The second `Rounds` application, then the rest of the layer. -/
def layerAfterLeft (ctx : ProtocolContext) (handle width : Nat) (add mul : Nat → Wiring F width)
    (state : State F) (left : List F × F) : PIR.Proc (Actions F G) (State F) :=
  (rounds (rightContext ctx) handle width left.2).bind
    (layerAfterRight ctx handle width add mul state left)

/-- One layer: both `Rounds` applications, the line polynomial's coefficients,
the wiring check and the line challenge. -/
def layerStep (ctx : ProtocolContext) (handle width : Nat) (add mul : Nat → Wiring F width)
    (state : State F) : PIR.Proc (Actions F G) (State F) :=
  (rounds (leftContext ctx) handle width state.2.2).bind
    (layerAfterLeft ctx handle width add mul state)

/-- The decision on the inputs at the final point. -/
def decision (width : Nat) (inputs : Table F width) (state : State F) : Option Bool :=
  some (decide (extension width inputs (coordinates width state.2.1) = state.2.2))

/-- The layers from the output claim, then the input check. -/
def afterOutputs (ctx : ProtocolContext) (handle layers width : Nat) (outputs inputs : Table F width)
    (add mul : Nat → Wiring F width) (point : List F) : PIR.Proc (Actions F G) (Option Bool) :=
  (PIR.repeatN layers (layerStep ctx handle width add mul)
      (0, point, extension width outputs (coordinates width point))).bind fun final =>
  .done (decision width inputs final)

/-- The plain GKR verifier of an admitted statement: claimed outputs and the
inputs as tables, the wiring at each layer, the number of layers and the width. -/
def verifier (ctx : ProtocolContext) (handle layers width : Nat) (outputs inputs : Table F width)
    (add mul : Nat → Wiring F width) : PIR.Proc (Actions F G) (Option Bool) :=
  (PIR.repeatN width (outputRound ctx handle) []).bind
    (afterOutputs ctx handle layers width outputs inputs add mul)

end ZkcExamples.Structured.GkrVerifier
