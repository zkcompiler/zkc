import Zkc.Source.RegionDerivation

/-! Two protocol-shaped clients of the same source-indexed derivation rules.
The arithmetic is deliberately small; these are structural proofs, not Schnorr
or Sumcheck security results and not claims about maintained imported programs.
-/
set_option autoImplicit false
namespace Tests.RegionDerivation
open Zkc.Source PIR

local macro "vals[" xs:term,* "]" : term => do
  let mut result ← `(Values.nil)
  for x in xs.getElems.reverse do
    result ← `(Values.cons $x $result)
  return result

inductive Ty where
  | scalar | boolean
  deriving DecidableEq

abbrev Value : Ty → Type
  | .scalar => Nat
  | .boolean => Bool

inductive Action where
  | receive (site : Nat)
  | draw
  | send (value : Nat)
  | mark (value : Nat)
  deriving DecidableEq, Repr

abbrev interface : Signature where
  Op := Action
  Reply
    | .receive _ | .draw => Nat
    | .send _ | .mark _ => Unit

inductive Op where
  | receive (site : Nat)
  | draw | send | check | guard | update
  | choose (selected : Bool)
  | repeat (count : Nat)

abbrev dialect : Dialect where
  Ty := Ty
  Op := Op
  arguments
    | .receive _ | .draw => []
    | .send | .choose _ | .repeat _ => [.scalar]
    | .check | .guard | .update => [.scalar, .scalar, .scalar]
  results
    | .send | .guard => []
    | .check => [.boolean]
    | _ => [.scalar]
  regions
    | .choose _ => [([.scalar], [.scalar]), ([.scalar], [.scalar])]
    | .repeat _ => [([.scalar], [.scalar])]
    | _ => []

abbrev Scalars := Values Value [Ty.scalar]

private theorem singleton_cases {ty : Ty} {property : Values Value [ty] → Prop}
    (step : ∀ value, property vals[value]) : ∀ values, property values := by
  intro values
  cases values with
  | cons value rest => cases rest; exact step value

def source : RegionMeaning dialect interface where
  Value := Value
  operation
    | .receive site, .nil, .nil => .call (.receive site) fun n => .done vals[n]
    | .draw, .nil, .nil => .call .draw fun n => .done vals[n]
    | .send, .cons n .nil, .nil => .call (.send n) fun _ => .done .nil
    | .check, .cons commitment (.cons challenge (.cons response .nil)), .nil =>
        .done vals[response == commitment + challenge]
    | .guard, .cons claim (.cons low (.cons high .nil)), .nil =>
        if low + high == claim then .done .nil else .halt .reject
    | .update, .cons low (.cons high (.cons challenge .nil)), .nil =>
        .done vals[low + challenge * high]
    | .choose selected, args, .cons yes (.cons no .nil) =>
        if selected then yes args else no args
    | .repeat count, args, .cons body .nil => repeatN count body args

/-- A draw expands to ordered before/after effects and may stop after sampling.
This is an interpretation, with no assertion of uniform returned challenges. -/
def lower : OperationInterpretation interface interface
  | .draw => .call (.mark 0) fun _ => .call .draw fun challenge =>
      .call (.mark (challenge + 1)) fun _ =>
        if challenge == 0 then .halt .exhausted else .done challenge
  | action => .call action .done

def receive (site : Nat) : Proc interface Scalars :=
  .call (.receive site) fun n => .done vals[n]

def draw : Proc interface Scalars :=
  (lower .draw).bind fun n => .done vals[n]

def send (n : Nat) : Proc interface (Values Value []) :=
  .call (.send n) fun _ => .done .nil

def check (commitment challenge response : Nat) : Proc interface (Values Value [Ty.boolean]) :=
  .done vals[response == commitment + challenge]

def guard (claim low high : Nat) : Proc interface (Values Value []) :=
  if low + high == claim then .done .nil else .halt .reject

def update (low high challenge : Nat) : Proc interface Scalars :=
  .done vals[low + challenge * high]

def choose (selected : Bool) (yes no : Scalars → Proc interface Scalars)
    (args : Scalars) : Proc interface Scalars :=
  if selected then yes args else no args

/-- The only induction needed for the repeat operation's semantic law.
The callback can be effectful, input-dependent, and stopping. -/
theorem interpret_repeat {A : Type} (count : Nat) (body : A → Proc interface A) (a : A) :
    (repeatN count body a).interpret lower =
      repeatN count (fun x => (body x).interpret lower) a := by
  induction count generalizing a with
  | zero => rfl
  | succ count ih =>
      simp only [repeatN, Proc.interpret_bind]
      congr 1
      funext value
      exact ih value

def translation : source.Translation lower where
  operation
    | .receive site, .nil, .nil => receive site
    | .draw, .nil, .nil => draw
    | .send, .cons n .nil, .nil => send n
    | .check, .cons c (.cons x (.cons r .nil)), .nil => check c x r
    | .guard, .cons c (.cons l (.cons h .nil)), .nil => guard c l h
    | .update, .cons l (.cons h (.cons x .nil)), .nil => update l h x
    | .choose selected, args, .cons yes (.cons no .nil) => choose selected yes no args
    | .repeat count, args, .cons body .nil => repeatN count body args
  commutes := by
    intro op args bodies
    cases op with
    | receive site => cases args; cases bodies; rfl
    | draw => cases args; cases bodies; rfl
    | send =>
        cases args with
        | cons n tail => cases tail; cases bodies; rfl
    | check =>
        cases args with
        | cons c tail => cases tail with
          | cons x tail => cases tail with
            | cons r tail => cases tail; cases bodies; rfl
    | guard =>
        cases args with
        | cons c tail => cases tail with
          | cons l tail => cases tail with
            | cons h tail =>
                cases tail; cases bodies
                change guard c l h = (guard c l h).interpret lower
                unfold guard
                split <;> rfl
    | update =>
        cases args with
        | cons l tail => cases tail with
          | cons h tail => cases tail with
            | cons x tail => cases tail; cases bodies; rfl
    | choose selected =>
        cases bodies with
        | cons yes tail => cases tail with
          | cons no tail => cases tail; cases selected <;> rfl
    | «repeat» count =>
        cases bodies with
        | cons body tail => cases tail; exact (interpret_repeat count body args).symm

abbrev Derives {Γ out : List Ty} := @Region.Derivation dialect interface interface source lower Γ out

def empty : Environment Value [] := fun reference => nomatch reference

/-- Exact callback controls, shared by both choices of the Schnorr-shaped client. -/
def controls : Regions dialect [([Ty.scalar], [Ty.scalar]), ([Ty.scalar], [Ty.scalar])] :=
  .cons (.ret vals[.here]) (.cons (.stop .abort) .nil)

def controlProcesses : Values (RegionFunction Value interface)
    [([Ty.scalar], [Ty.scalar]), ([Ty.scalar], [Ty.scalar])] :=
  vals[fun args => .done vals[args.get .here], fun _ => .halt .abort]

theorem controls_derive : Regions.Derivation source lower controls controlProcesses :=
  .cons (fun _ => .ret _ _) (.cons (fun _ => .stop _ _) .nil)

/-- Receive/draw/send/receive/check, with a lexical bind and two closed callbacks.
The received commitment and response are independent reply variables. -/
def schnorr (selected : Bool) : Region dialect [] [Ty.boolean] :=
  .bind
    (.letOp (.receive 0) .nil .nil (.ret vals[.here]))
    (.letOp (.choose selected) vals[.here] controls
      (.letOp .draw .nil .nil
        (.letOp .send vals[.here] .nil
          (.letOp (.receive 1) .nil .nil
            (.letOp .check vals[.there (.there .here), .there .here, .here] .nil
              (.ret vals[.here]))))))

def schnorrProcess (selected : Bool) : Proc interface (Values Value [Ty.boolean]) :=
  ((receive 0).bind fun commitment => .done vals[commitment.get .here]).bind fun commitment =>
    (choose selected (fun args => .done vals[args.get .here]) (fun _ => .halt .abort)
      vals[commitment.get .here]).bind fun kept =>
      draw.bind fun challenge =>
        (send (challenge.get .here)).bind fun _ =>
          (receive 1).bind fun response =>
            (check (kept.get .here) (challenge.get .here) (response.get .here)).bind fun result =>
              .done vals[result.get .here]

theorem schnorr_derive (selected : Bool) :
    Derives (schnorr selected) empty (schnorrProcess selected) := by
  unfold schnorr schnorrProcess
  apply Region.Derivation.bind
  · refine Region.Derivation.letOp (meaning := source) (operations := lower)
      (.receive 0) .nil .nil ?_ (by apply singleton_cases; intro result; exact .ret _ _)
    exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
  · apply singleton_cases; intro commitment
    refine Region.Derivation.letOp (meaning := source) (operations := lower)
      (.choose selected) _ controls_derive ?_ ?_
    · exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
    · apply singleton_cases; intro kept
      refine Region.Derivation.letOp (meaning := source) (operations := lower) .draw .nil .nil ?_ ?_
      · exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
      · apply singleton_cases; intro challenge
        refine Region.Derivation.letOp (meaning := source) (operations := lower) .send _ .nil ?_ ?_
        · exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
        · intro ack
          cases ack
          refine Region.Derivation.letOp (meaning := source) (operations := lower)
            (.receive 1) .nil .nil ?_ ?_
          · exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
          · apply singleton_cases; intro response
            refine Region.Derivation.letOp (meaning := source) (operations := lower)
              .check _ .nil ?_ (by apply singleton_cases; intro result; exact .ret _ _)
            exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl

/-- The round keeps both receives separate, checks the old claim, then updates
from the actual challenge. The repeat operation supplies the next round's claim. -/
def round : Region dialect [Ty.scalar] [Ty.scalar] :=
  .letOp (.receive 2) .nil .nil
    (.letOp (.receive 3) .nil .nil
      (.letOp .guard vals[.there (.there .here), .there .here, .here] .nil
        (.letOp .draw .nil .nil
          (.letOp .update vals[.there (.there .here), .there .here, .here] .nil
            (.ret vals[.here])))))

def roundProcess (claim : Scalars) : Proc interface Scalars :=
  (receive 2).bind fun low =>
    (receive 3).bind fun high =>
      (guard (claim.get .here) (low.get .here) (high.get .here)).bind fun _ =>
        draw.bind fun challenge =>
          (update (low.get .here) (high.get .here) (challenge.get .here)).bind fun result =>
            .done vals[result.get .here]

theorem round_derive (claim : Scalars) : Derives round claim.get (roundProcess claim) := by
  unfold round roundProcess
  refine Region.Derivation.letOp (meaning := source) (operations := lower) (.receive 2) .nil .nil ?_ ?_
  · exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
  · apply singleton_cases; intro low
    refine Region.Derivation.letOp (meaning := source) (operations := lower) (.receive 3) .nil .nil ?_ ?_
    · exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
    · apply singleton_cases; intro high
      refine Region.Derivation.letOp (meaning := source) (operations := lower) .guard _ .nil ?_ ?_
      · exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
      · intro checked
        cases checked
        refine Region.Derivation.letOp (meaning := source) (operations := lower) .draw .nil .nil ?_ ?_
        · exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl
        · apply singleton_cases; intro challenge
          refine Region.Derivation.letOp (meaning := source) (operations := lower)
            .update _ .nil ?_ (by apply singleton_cases; intro result; exact .ret _ _)
          exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl

def sumcheck (count : Nat) : Region dialect [Ty.scalar] [Ty.scalar] :=
  .letOp (.repeat count) vals[.here] (.cons round .nil) (.ret vals[.here])

def sumcheckProcess (count claim : Nat) : Proc interface Scalars :=
  (repeatN count roundProcess vals[claim]).bind fun result => .done vals[result.get .here]

theorem sumcheck_derive (count claim : Nat) :
    Derives (sumcheck count) (vals[claim] : Scalars).get (sumcheckProcess count claim) := by
  unfold sumcheck sumcheckProcess
  refine Region.Derivation.letOp (meaning := source) (operations := lower)
    (.repeat count) _ (.cons round_derive .nil) ?_ (by apply singleton_cases; intro result; exact .ret _ _)
  exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl

theorem schnorr_equation (selected : Bool) :
    ((schnorr selected).denote source empty).interpret lower = schnorrProcess selected :=
  (schnorr_derive selected).sound

theorem sumcheck_equation (count claim : Nat) :
    ((sumcheck count).denote source (vals[claim] : Scalars).get).interpret lower =
      sumcheckProcess count claim := (sumcheck_derive count claim).sound

/-- Identical operations and operands receive different local normal forms.
The original source still contains both operations; no rewritten Region exists. -/
def twoUpdates : Region dialect [Ty.scalar, Ty.scalar, Ty.scalar] [Ty.scalar, Ty.scalar] :=
  .letOp .update vals[.here, .there .here, .there (.there .here)] .nil
    (.letOp .update vals[.there .here, .there (.there .here), .there (.there (.there .here))] .nil
      (.ret vals[.there .here, .here]))

def twoUpdateProcesses (a b x : Nat) : Proc interface (Values Value [Ty.scalar, Ty.scalar]) :=
  (Proc.done (vals[b * x + a] : Scalars)).bind fun first =>
    (Proc.done (vals[a + x * b] : Scalars)).bind fun second =>
      .done vals[first.get .here, second.get .here]

theorem occurrence_local_rewrites (a b x : Nat) :
    Derives twoUpdates (vals[a, b, x] : Values Value [Ty.scalar, Ty.scalar, Ty.scalar]).get
      (twoUpdateProcesses a b x) := by
  unfold twoUpdates twoUpdateProcesses
  refine Region.Derivation.letOp (meaning := source) (operations := lower) .update _ .nil ?_ ?_
  · apply RegionMeaning.OperationLaw.ofTranslation translation
    change (Proc.done (vals[a + x * b] : Scalars) : Proc interface Scalars) = .done vals[b * x + a]
    rw [Nat.mul_comm x b, Nat.add_comm a (b * x)]
  · apply singleton_cases; intro first
    refine Region.Derivation.letOp (meaning := source) (operations := lower)
      .update _ .nil ?_ (by apply singleton_cases; intro result; exact .ret _ _)
    exact RegionMeaning.OperationLaw.ofTranslation translation _ _ _ rfl

/-- An input fact is a visible hypothesis of an occurrence-specific law.
No global interpretation is required to turn every guard into success. -/
theorem guard_local_law (claim low high : Nat) (valid : low + high = claim) :
    source.OperationLaw lower .guard vals[claim, low, high] .nil (.done .nil) := by
  apply RegionMeaning.OperationLaw.ofTranslation translation
  change guard claim low high = .done .nil
  simp only [guard, valid, beq_self_eq_true, ite_true]

end Tests.RegionDerivation
