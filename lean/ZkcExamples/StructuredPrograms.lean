module

public import Zkc.Source.Region
public import Zkc.Source.Finite

@[expose] public section

/-! Effectful endpoint examples for the independent mathematical region model.

These are authored typed regions, not imported native programs. The equalities
below preserve every possible reply, guard, send and stop. They establish neither
native correspondence nor cryptographic security. Natural-number arithmetic is
deliberately only a small interpretation with which to stress the foundation.
-/

set_option autoImplicit false

namespace ZkcExamples.StructuredPrograms
open Zkc.Source PIR

inductive Ty where
  | number | boolean | vector
  deriving DecidableEq

abbrev Value : Ty → Type
  | .number => Nat
  | .boolean => Bool
  | .vector => List Nat

inductive Action where
  | receive (channel : Nat)
  | send (channel payload : Nat)
  deriving DecidableEq, Repr

abbrev interface : Signature where
  Op := Action
  Reply
    | .receive _ => Nat
    | .send _ _ => Unit

/-- Callback inputs and outputs are operation parameters, not protocol profiles. -/
inductive Operation where
  | add | multiply | equal
  | receive (channel : Nat)
  | send (channel : Nat)
  | require (reason : Stop)
  | admitVector (reason : Stop)
  | scope (inputs outputs : List Ty)
  | branch (inputs outputs : List Ty)
  | zipFold (state captures : List Ty)

abbrev arguments : Operation → List Ty
  | .add | .multiply | .equal => [.number, .number]
  | .receive _ => []
  | .send _ => [.number]
  | .require _ => [.boolean]
  | .admitVector _ => [.boolean, .vector]
  | .scope inputs _ => inputs
  | .branch inputs _ => .boolean :: inputs
  | .zipFold state captures => [.vector, .vector, .boolean, .boolean] ++ state ++ captures

abbrev results : Operation → List Ty
  | .add | .multiply | .receive _ => [.number]
  | .equal => [.boolean]
  | .send _ | .require _ | .admitVector _ => []
  | .scope _ outputs | .branch _ outputs => outputs
  | .zipFold state _ => state

abbrev regions : Operation → List (List Ty × List Ty)
  | .scope inputs outputs => [(inputs, outputs)]
  | .branch inputs outputs => [(inputs, outputs), (inputs, outputs)]
  | .zipFold state captures => [(state ++ (.number :: .number :: captures), state)]
  | _ => []

abbrev dialect : Dialect := ⟨Ty, Operation, arguments, results, regions⟩

/-- Strict zip retains left-to-right admission even when either list is empty. -/
def zipDomain (xs ys : List Nat) (left right : Bool) : Finite.Domain (Nat × Nat) :=
  .zip (.check left .refused (.elements xs)) (.check right .exhausted (.elements ys))

abbrev meaning : RegionMeaning dialect interface where
  Value := Value
  operation
    | .add, .cons x (.cons y .nil), .nil => .done (.cons (x + y) .nil)
    | .multiply, .cons x (.cons y .nil), .nil => .done (.cons (x * y) .nil)
    | .equal, .cons x (.cons y .nil), .nil => .done (.cons (x == y) .nil)
    | .receive channel, .nil, .nil => .call (.receive channel) fun x => .done (.cons x .nil)
    | .send channel, .cons x .nil, .nil => .call (.send channel x) fun _ => .done .nil
    | .require reason, .cons passed .nil, .nil =>
        if passed then .done .nil else .halt reason
    | .admitVector reason, .cons passed (.cons xs .nil), .nil =>
        Finite.admitThen (Finite.Domain.check passed reason (.elements xs)).admit
          fun _ => .done .nil
    | .scope _ _, inputs, .cons body .nil => body inputs
    | .branch _ _, .cons condition inputs, .cons yes (.cons no .nil) =>
        if condition then yes inputs else no inputs
    | .zipFold state _, .cons xs (.cons ys (.cons left (.cons right inputs))),
        .cons body .nil =>
        let parts := Values.split state inputs
        Finite.execute (zipDomain xs ys left right)
          (fun carried item => body
            (Values.append carried (.cons item.1 (.cons item.2 parts.2)))) parts.1

-- Positional notation is local; comments below name each ordered input context.
local notation "v0" => Var.here
local notation "v1" => Var.there Var.here
local notation "v2" => Var.there (Var.there Var.here)
local notation "v3" => Var.there (Var.there (Var.there Var.here))
local notation "v4" => Var.there (Var.there (Var.there (Var.there Var.here)))
local notation "v5" => Var.there (Var.there (Var.there (Var.there (Var.there Var.here))))
local notation "v6" => Var.there (Var.there (Var.there (Var.there (Var.there (Var.there Var.here)))))
local notation "v7" => Var.there (Var.there (Var.there (Var.there (Var.there (Var.there (Var.there Var.here))))))
local notation "v8" => Var.there (Var.there (Var.there (Var.there (Var.there (Var.there (Var.there (Var.there Var.here)))))))

local macro "vals[" xs:term,* "]" : term => do
  let mut result ← `(Values.nil)
  for x in xs.getElems.reverse do
    result ← `(Values.cons $x $result)
  return result

abbrev Numbers (count : Nat) := List.replicate count Ty.number

/-- Inputs: accumulator, left item, right item, explicitly captured scale.
Each item receives an independent claimed product before sending its new state. -/
def openingStepWith (commuted : Bool) : Region dialect (Numbers 4) [.number] :=
  .letOp (.receive 1) vals[] .nil <|
  .letOp .multiply (if commuted then vals[v3, v2] else vals[v2, v3]) .nil <|
  .letOp .equal vals[v0, v1] .nil <|
  .letOp (.require .reject) vals[v0] .nil <|
  .letOp .multiply vals[v1, v6] .nil <|
  .letOp .add vals[v0, v4] .nil <|
  .letOp (.send 2) vals[v0] .nil <|
  .ret vals[v0]

abbrev openingStep := openingStepWith false

/-- The extra closed scope exercises callback nesting below the finite loop. -/
def capturedStep (body : Region dialect (Numbers 4) [.number]) :
    Region dialect (Numbers 4) [.number] :=
  .letOp (.scope (Numbers 4) [.number]) vals[v0, v1, v2, v3]
    (.cons body .nil) (.ret vals[v0])

abbrev OpeningInputs : List Ty :=
  [.vector, .vector, .boolean, .boolean, .number, .number]

/-- Inputs: vectors, admission flags, seed, scale. Results: total, retained scale. -/
def openingFold (body : Region dialect (Numbers 4) [.number]) :
    Region dialect OpeningInputs [.number, .number] :=
  .letOp (.zipFold [.number] [.number]) vals[v0, v1, v2, v3, v4, v5]
    (.cons (capturedStep body) .nil) (.ret vals[v0, v6])

/-- Receive the total independently of both vectors and every per-item reply.
Binding two results retains their order and the caller's original seed. -/
def openingWith (body : Region dialect (Numbers 4) [.number]) :
    Region dialect OpeningInputs [.number, .number] :=
  .letOp (.receive 0) vals[] .nil <|
  .bind ((openingFold body).rename (fun ref => .there ref)) <|
  .letOp .equal vals[v0, v2] .nil <|
  .letOp (.require .reject) vals[v0] .nil <|
  .letOp (.send 3) vals[v1] .nil <|
  .ret vals[v1, v8]

abbrev opening := openingWith openingStep

def openingInputs (xs ys : List Nat) (left right : Bool) (seed scale : Nat) :
    Values Value OpeningInputs := vals[xs, ys, left, right, seed, scale]

def openingStepReference (scale state x y : Nat) : Proc interface (Values Value [.number]) :=
  .call (.receive 1) fun reply =>
    if x * y == reply then
      .call (.send 2 (x * y * scale + state)) fun _ =>
        .done vals[x * y * scale + state]
    else .halt .reject

def openingReference (xs ys : List Nat) (left right : Bool) (seed scale : Nat) :
    Proc interface (Values Value [.number, .number]) :=
  .call (.receive 0) fun claimed =>
    (Finite.execute (zipDomain xs ys left right)
      (fun state item => openingStepReference scale (state.get .here) item.1 item.2)
      vals[seed]).bind fun total =>
        if total.get .here == claimed then
          .call (.send 3 (total.get .here)) fun _ => .done vals[total.get .here, seed]
        else .halt .reject

abbrev VerifierInputs : List Ty :=
  [.number, .number, .number, .boolean, .vector, .boolean]
abbrev VerificationInputs : List Ty := Numbers 5

/-- Inputs: base, key, challenge, commitment, response. The equation only
resembles a protocol check; natural-number arithmetic has no security claim. -/
def verifyEquation : Region dialect VerificationInputs [.number, .number] :=
  .letOp .multiply vals[v4, v0] .nil <|
  .letOp .multiply vals[v3, v2] .nil <|
  .letOp .add vals[v5, v0] .nil <|
  .letOp .equal vals[v2, v0] .nil <|
  .letOp (.require .reject) vals[v0] .nil <|
  .letOp (.send 13) vals[v8] .nil <|
  .ret vals[v7, v8]

/-- Explicit captures cross both scope and branch boundaries. -/
def guardedVerification : Region dialect (.boolean :: VerificationInputs) [.number, .number] :=
  .letOp (.branch VerificationInputs [.number, .number]) vals[v0, v1, v2, v3, v4, v5]
    (.cons verifyEquation (.cons (.stop .abort) .nil)) (.ret vals[v0, v1])

/-- A discarded, zero-result admission precedes all receives. The final bind
uses two callback results in reverse order while retaining the input challenge. -/
def verifier : Region dialect VerifierInputs (Numbers 3) :=
  .letOp (.admitVector .refused) vals[v5, v4] .nil <|
  .letOp (.receive 10) vals[] .nil <|
  .letOp (.send 11) vals[v3] .nil <|
  .letOp (.receive 12) vals[] .nil <|
  .bind
    (.letOp (.scope (.boolean :: VerificationInputs) [.number, .number])
      vals[v5, v2, v3, v4, v1, v0] (.cons guardedVerification .nil) (.ret vals[v0, v1])) <|
  .letOp (.send 14) vals[v0] .nil <|
  .ret vals[v1, v0, v6]

def verifierInputs (base key challenge : Nat) (enabled : Bool) (audit : List Nat)
    (admitted : Bool) : Values Value VerifierInputs :=
  vals[base, key, challenge, enabled, audit, admitted]

def verifierReference (base key challenge : Nat) (enabled : Bool) (audit : List Nat)
    (admitted : Bool) : Proc interface (Values Value (Numbers 3)) :=
  Finite.admitThen (Finite.Domain.check admitted .refused (.elements audit)).admit fun _ =>
    .call (.receive 10) fun commitment =>
      .call (.send 11 challenge) fun _ =>
        .call (.receive 12) fun response =>
          if enabled then
            if response * base == commitment + challenge * key then
              .call (.send 13 response) fun _ =>
                .call (.send 14 commitment) fun _ => .done vals[response, commitment, challenge]
            else .halt .reject
          else .halt .abort

theorem openingStep_correspondence (env : Environment Value (Numbers 4)) :
    openingStep.denote meaning env =
      openingStepReference (env v3) (env v0) (env v1) (env v2) := by
  apply Proc.call_congr
  intro reply
  change (if env v1 * env v2 == reply then Proc.done (vals[] : Values Value [])
    else Proc.halt .reject).bind _ = _
  split <;> rfl

theorem capturedStep_correspondence (env : Environment Value (Numbers 4)) :
    (capturedStep openingStep).denote meaning env =
      openingStepReference (env v3) (env v0) (env v1) (env v2) := by
  have suffix : (fun (values : Values Value [.number]) =>
      (Proc.done (Operands.eval (env.prepend values) vals[v0]) :
        Proc interface (Values Value [.number]))) = Proc.done := by
    funext values
    cases values with
    | cons value rest => cases rest; rfl
  change (openingStep.denote meaning
    (vals[env v0, env v1, env v2, env v3] : Values Value (Numbers 4)).get).bind
      (fun values => .done (Operands.eval (env.prepend values) vals[v0])) = _
  rw [suffix, Proc.bind_done]
  exact openingStep_correspondence _

theorem openingFold_correspondence (env : Environment Value OpeningInputs) :
    (openingFold openingStep).denote meaning env =
      (Finite.execute (zipDomain (env v0) (env v1) (env v2) (env v3))
        (fun state item => openingStepReference (env v5) (state.get .here) item.1 item.2)
        vals[env v4]).bind fun total => .done vals[total.get .here, env v5] := by
  change (Finite.execute (zipDomain (env v0) (env v1) (env v2) (env v3))
    (fun (state : Values Value [.number]) (item : Nat × Nat) =>
      (capturedStep openingStep).denote meaning
        (Values.append state (vals[item.1, item.2, env v5] : Values Value (Numbers 3))).get)
    vals[env v4]).bind _ = _
  have step : (fun (state : Values Value [.number]) (item : Nat × Nat) =>
      (capturedStep openingStep).denote meaning
        (Values.append state vals[item.1, item.2, env v5]).get) =
      (fun state item => openingStepReference (env v5) (state.get .here) item.1 item.2) := by
    funext state item
    cases state with
    | cons value rest => cases rest; exact capturedStep_correspondence _
  rw [step]
  congr 1
  funext values
  cases values with
  | cons value rest => cases rest; rfl

/-- Equality of complete open processes, universally quantified over input
vectors, admission flags, captures and every independent external reply. -/
theorem opening_correspondence (xs ys : List Nat) (left right : Bool) (seed scale : Nat) :
    opening.denote meaning (openingInputs xs ys left right seed scale).get =
      openingReference xs ys left right seed scale := by
  apply Proc.call_congr
  intro claimed
  change (((openingFold openingStep).rename (fun ref => .there ref)).denote meaning
    (Environment.push (ty := Ty.number) (openingInputs xs ys left right seed scale).get claimed)).bind _ = _
  rw [Region.denote_rename, openingFold_correspondence, Proc.bind_assoc]
  congr 1
  funext total
  change (if total.get .here == claimed then Proc.done (vals[] : Values Value [])
    else Proc.halt .reject).bind _ = _
  split <;> rfl

theorem capturedStep_congr {left right : Region dialect (Numbers 4) [.number]}
    (same : Region.Equivalent meaning left right) :
    Region.Equivalent meaning (capturedStep left) (capturedStep right) := by
  apply Region.operation_congr
  · exact Regions.cons_congr meaning same rfl
  · intro env; rfl

/-- Generic congruence transports replacement through two captured callbacks. -/
theorem openingFold_congr {left right : Region dialect (Numbers 4) [.number]}
    (same : Region.Equivalent meaning left right) :
    Region.Equivalent meaning (openingFold left) (openingFold right) := by
  apply Region.operation_congr
  · exact Regions.cons_congr meaning (capturedStep_congr same) rfl
  · intro env; rfl

theorem openingWith_congr {left right : Region dialect (Numbers 4) [.number]}
    (same : Region.Equivalent meaning left right) :
    Region.Equivalent meaning (openingWith left) (openingWith right) := by
  apply Region.operation_congr
  · rfl
  · apply Region.bind_congr
    · intro env
      rw [Region.denote_rename, Region.denote_rename]
      exact openingFold_congr same _
    · intro env; rfl

theorem openingStep_commuted :
    Region.Equivalent meaning openingStep (openingStepWith true) := by
  intro env
  rw [openingStep_correspondence]
  apply Proc.call_congr
  intro reply
  change _ = (if env v2 * env v1 == reply then Proc.done (vals[] : Values Value [])
    else Proc.halt .reject).bind _
  rw [Proc.bind_ite]
  change (if env v1 * env v2 == reply then
      Proc.call (I := interface) (.send 2 (env v1 * env v2 * env v3 + env v0))
        (fun _ => .done (vals[env v1 * env v2 * env v3 + env v0] : Values Value [.number]))
      else Proc.halt .reject) =
    (if env v2 * env v1 == reply then
      Proc.call (I := interface) (.send 2 (env v2 * env v1 * env v3 + env v0))
        (fun _ => .done vals[env v2 * env v1 * env v3 + env v0])
      else Proc.halt .reject)
  rw [Nat.mul_comm (env v2) (env v1)]

/-- Concrete arithmetic replacement under nested captures and a multi-result
binding, lifted solely by generic contextual laws. Receives stay independent. -/
theorem opening_contextual_replacement :
    Region.Equivalent meaning opening (openingWith (openingStepWith true)) :=
  openingWith_congr openingStep_commuted

theorem verifier_correspondence (base key challenge : Nat) (enabled : Bool)
    (audit : List Nat) (admitted : Bool) :
    verifier.denote meaning (verifierInputs base key challenge enabled audit admitted).get =
      verifierReference base key challenge enabled audit admitted := by
  cases admitted with
  | false => rfl
  | true =>
      apply Proc.call_congr
      intro commitment
      apply Proc.call_congr
      intro acknowledgement
      apply Proc.call_congr
      intro response
      cases enabled with
      | false => rfl
      | true =>
          change ((((if response * base == commitment + challenge * key then
            Proc.done (vals[] : Values Value []) else Proc.halt .reject).bind _).bind _).bind _).bind _ = _
          split <;> rfl

end ZkcExamples.StructuredPrograms
