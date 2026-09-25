import Zkc.Semantics.Execution

/-! Interaction legality and uniform interface-call bounds for finite executions.

`Conforms` follows every interface-typed reply, including dishonest values;
`Reaches` records only returned replies. `Within` is a separately established
bound uniform over those replies. Well-founded `Proc` execution alone does not
give such a bound. Interface calls do not count a handler's internal arithmetic,
allocation, native instructions, or cryptographic oracle queries automatically.
Role ownership describes the interface schedule; locality of an actual endpoint
is a separate obligation, as is the correctness of an honest strategy.
-/

set_option autoImplicit false
namespace PIR

/-- Interface legality; it does not assert honest arithmetic or cryptographic validity. -/
structure Interaction (I : Signature) where
  Role : Type
  Phase : Type
  owner : I.Op → Role
  enabled : Phase → I.Op → Prop
  advance : (phase : Phase) → (o : I.Op) → I.Reply o → Phase

variable {I : Signature} {A : Type}

/-- All interface-typed replies are considered, including dishonest payloads. -/
def Conforms (P : Interaction I) : Proc I A → P.Phase → Prop
  | .done _, _ => True
  | .halt _, _ => True
  | .call o k, phase => P.enabled phase o ∧
      ∀ reply, Conforms P (k reply) (P.advance phase o reply)

/-- A finite returned-response history; terminal failure does not fabricate a reply. -/
inductive Reaches (P : Interaction I) : Proc I A → P.Phase → Proc I A → P.Phase → Prop where
  | refl (p : Proc I A) (phase : P.Phase) : Reaches P p phase p phase
  | step (o : I.Op) (k : I.Reply o → Proc I A) (phase : P.Phase)
      (reply : I.Reply o) (tail : Proc I A) (last : P.Phase)
      (rest : Reaches P (k reply) (P.advance phase o reply) tail last) :
      Reaches P (.call o k) phase tail last

theorem conformance_preserved (P : Interaction I)
    (p q : Proc I A) (start finish : P.Phase)
    (path : Reaches P p start q finish) (formed : Conforms P p start) :
    Conforms P q finish := by
  induction path with
  | refl => exact formed
  | step o k phase reply tail last rest ih => exact ih (formed.2 reply)

theorem reached_call_permitted (P : Interaction I)
    (p : Proc I A) (start finish : P.Phase) (o : I.Op) (k : I.Reply o → Proc I A)
    (path : Reaches P p start (.call o k) finish) (formed : Conforms P p start) :
    P.enabled finish o := (conformance_preserved P _ _ _ _ path formed).1

/-- Public bound on calls, uniform over every possible reply at this instance. -/
def Within : Nat → Proc I A → Prop
  | _, .done _ => True
  | _, .halt _ => True
  | 0, .call _ _ => False
  | n+1, .call _ k => ∀ reply, Within n (k reply)

/-- Public bounded iteration is elaboration, not unrestricted recursive execution. -/
def repeatN (n : Nat) (step : A → Proc I A) (a : A) : Proc I A :=
  match n with
  | 0 => .done a
  | n+1 => (step a).bind (fun b => repeatN n step b)

/-- Strategies operate on the selected view and their own retained memory.
    Hidden provider state is not an extra argument to this interface. -/
abbrev LocalStrategy (View Memory Move : Type) := View → Memory → Move × Memory

/-- Honest behavior is an additional predicate, never the admissible-strategy set. -/
structure HonestRole (P : Interaction I) (start : P.Phase)
    (honest : Proc I A → Prop) where
  body : Proc I A
  conforms : Conforms P body start
  correct : honest body

/-- Missing required bindings are distinct from a value, including zero. -/
def requireInput {V : Type} (input : Option V) : Outcome V :=
  match input with
  | none => .stopped .refused
  | some v => .returned v

end PIR
