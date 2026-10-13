module

public import Zkc.Source.RawSemantics

@[expose] public section

/-! A typed verifier composing two opening checks with a scalar relation.

The commitment provider supplies only an opening predicate. This module proves
source execution and the bad-opening decomposition; it assumes no binding or
extractability property. A cryptographic consumer must discharge that event in
the same setup/adversary experiment.
-/

namespace Zkc.Protocols.OpeningSum
open PIR Zkc.Source

structure Opening (F Proof : Type) where
  value : F
  proof : Proof

structure Statement (F Commitment : Type) where
  commitment : Commitment
  first : F
  second : F
  claim : F

abbrev Check (F Commitment Proof : Type) := Commitment → F → Opening F Proof → Bool

def interface (F Commitment Proof : Type) : Signature where
  Op := Commitment × F
  Reply _ := Opening F Proof

inductive Ty where | scalar | commitment | opening | boolean
  deriving DecidableEq, Repr

inductive Op where | receive | verify | sumCheck
  deriving DecidableEq, Repr

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .receive => [.commitment, .scalar]
    | .verify => [.commitment, .scalar, .opening]
    | .sumCheck => [.scalar, .opening, .opening]
  result
    | .receive => .opening
    | .verify | .sumCheck => .boolean
  condition := .boolean

abbrev Value (F Commitment Proof : Type) : Ty → Type
  | .scalar => F
  | .commitment => Commitment
  | .opening => Opening F Proof
  | .boolean => Bool

variable {F Commitment Proof : Type} [Add F] [DecidableEq F]

def meaning (check : Check F Commitment Proof) :
    Interpretation language (interface F Commitment Proof) where
  Value := Value F Commitment Proof
  condition := id
  operation
    | .receive, .cons commitment (.cons point .nil) => .call (commitment, point) .done
    | .verify, .cons commitment (.cons point (.cons opening .nil)) =>
        .done (check commitment point opening)
    | .sumCheck, .cons claim (.cons left (.cons right .nil)) =>
        .done (decide (claim = left.value + right.value))

def inputs : List Ty := [.commitment, .scalar, .scalar, .scalar]

/-- De Bruijn positions make the exact checked carrier reviewable. Both receives
and the final arithmetic comparison are in source syntax, not a theorem premise. -/
def raw : RawProgram Ty Op :=
  .letOp .receive [0, 1]
    (.letOp .verify [1, 2, 0]
      (.branch 0
        (.letOp .receive [2, 4]
          (.letOp .verify [3, 5, 0]
            (.branch 0 (.letOp .sumCheck [7, 3, 1] (.ret 0)) (.stop .reject))))
        (.stop .reject)))

def program : Program language inputs .boolean :=
  (raw.elaborate (language := language) inputs .boolean).toOption.get (by decide +kernel)

def environment (statement : Statement F Commitment) : Environment (Value F Commitment Proof) inputs :=
  (Values.cons (ty := Ty.commitment) statement.commitment
    (.cons statement.first (.cons statement.second (.cons statement.claim .nil)))).get

def reference (check : Check F Commitment Proof) (statement : Statement F Commitment) :
    Proc (interface F Commitment Proof) Bool :=
  .call (statement.commitment, statement.first) fun left =>
    if check statement.commitment statement.first left then
      .call (statement.commitment, statement.second) fun right =>
        if check statement.commitment statement.second right then
          .done (decide (statement.claim = left.value + right.value))
        else .halt .reject
    else .halt .reject

theorem program_denote (check : Check F Commitment Proof) (statement : Statement F Commitment) :
    program.denote (meaning check) (environment statement) = reference check statement := by
  rfl

/-- Any implementation proved to have this complete process can reuse consumers.
The contract preserves guards, request order, stops and provider continuations. -/
def VerifierContract (check : Check F Commitment Proof)
    (verifier : Statement F Commitment → Proc (interface F Commitment Proof) Bool) : Prop :=
  ∀ statement, verifier statement = reference check statement

theorem source_contract (check : Check F Commitment Proof) :
    VerifierContract check (fun statement => program.denote (meaning check) (environment statement)) :=
  program_denote check

def replay (left right : Opening F Proof) : Handler (interface F Commitment Proof) Nat (Commitment × F) :=
  fun request position => ⟨.returned (if position = 0 then left else right), position + 1, [request]⟩

def Accepted (check : Check F Commitment Proof) (statement : Statement F Commitment)
    (left right : Opening F Proof) : Prop :=
  check statement.commitment statement.first left = true ∧
  check statement.commitment statement.second right = true ∧
  statement.claim = left.value + right.value

theorem contract_accepted {check : Check F Commitment Proof}
    {verifier : Statement F Commitment → Proc (interface F Commitment Proof) Bool}
    (contract : VerifierContract check verifier) (statement : Statement F Commitment)
    (left right : Opening F Proof) :
    ((verifier statement).run (replay left right) 0).outcome = .returned true ↔
      Accepted check statement left right := by
  rw [contract statement]
  by_cases first : check statement.commitment statement.first left = true
  all_goals by_cases second : check statement.commitment statement.second right = true
  all_goals simp [reference, Proc.run, replay, Execution.follow, Accepted, first, second]

/-- Only reached, accepted openings count; a rejected first opening cannot expose
the second opening. No independence assumption is used. -/
def BadOpening (check : Check F Commitment Proof) (evaluation : F → F)
    (statement : Statement F Commitment) (left right : Opening F Proof) : Prop :=
  check statement.commitment statement.first left = true ∧
    (left.value ≠ evaluation statement.first ∨
      (check statement.commitment statement.second right = true ∧
        right.value ≠ evaluation statement.second))

theorem accepted_false_implies_bad (check : Check F Commitment Proof) (evaluation : F → F)
    (statement : Statement F Commitment) (left right : Opening F Proof)
    (accepted : Accepted check statement left right)
    (falseClaim : statement.claim ≠ evaluation statement.first + evaluation statement.second) :
    BadOpening check evaluation statement left right := by
  refine ⟨accepted.1, ?_⟩
  by_cases first : left.value = evaluation statement.first
  · right
    refine ⟨accepted.2.1, ?_⟩
    intro second
    exact falseClaim (by simpa only [first, second] using accepted.2.2)
  · exact Or.inl first

end Zkc.Protocols.OpeningSum
