module

public import ZkcFormal.Written.Blind

@[expose] public section
set_option autoImplicit false

/-!
What a contract of a call says.

A protocol that applies another is judged by fees without opening the callee, from a contract
of the callee: what the callee is given, what it returns, what one run of it costs, and what
each of its sites needs of the allowance. The contract and what it is for it to hold are
definitions of the judgment by fees (`Fees.judgment`) and of nothing else: a statement that a
contract holds reads no generator of proofs and no reading of a program into another form, so a
library's protocol can publish it as a challenge.

Two numbers stay apart. **The fee** is what one run of the callee is charged at most: a sum
along a run, with the larger arm of a choice. **The need** of a site is what an occurrence of
that site may be charged: a bound of one fee. A callee with two arms that each draw once at a
quarter has a fee of a quarter and needs a quarter at each of its two sites.

`Contract.call` is the rule of a call: at an application, a contract that holds judges the
caller, for every rest that is judged from what the fee leaves.
-/

namespace ZkcFormal.Written
open Zkc.Core
open scoped NNRat

variable {V : Vocabulary} {M : Model V}

/-- **A contract of a call**: of the role `role` in the protocol `callee`. A type of ghost
values, which a statement about the callee may speak of and the program does not hold; a
precondition over the ghost and the inputs; a postcondition over the ghost, the inputs and the
results; the fee; and what each site of the callee, below the start of a run of it, needs of
the allowance. -/
structure Contract (M : Model V) (p : Typed V) {h : ProtocolHeader V}
    (callee : Member p.headers.protocols h) (role : Role) where
  Ghost : Type
  pre : Ghost → HList (RV M role) h.ins → Prop
  post : Ghost → HList (RV M role) h.ins → HList (RV M role) h.outs → Prop
  fee : ℚ≥0
  need : Site → ℚ≥0

variable {p : Typed V} {h : ProtocolHeader V} {callee : Member p.headers.protocols h} {role : Role}

/-- An allowance covers a contract at a start when it gives every occurrence below the start
what the contract needs at the occurrence's site. -/
def Contract.Covers (c : Contract M p callee role) (allowance : Occurrence → ℚ≥0)
    (start : List Frame) : Prop :=
  ∀ at_ site, Occurrence.siteBelow start at_ = some site → c.need site ≤ allowance at_

/-- **What it is for a contract to hold.** At every start and under every allowance that covers
the contract there, on inputs and a ghost that meet the precondition, from every budget that
holds the fee: the role's process in the callee is judged by fees to end, if it returns, in the
postcondition with at least the budget less the fee left. -/
def Contract.Holds (c : Contract M p callee role) (draws : LawDraws M) : Prop :=
  ∀ (allowance : Occurrence → ℚ≥0) (start : List Frame), c.Covers allowance start →
    ∀ ghost ins, c.pre ghost ins → ∀ budget, c.fee ≤ budget →
      (roleMeaning M p callee role start ins).interpret (Fees.judgment draws allowance)
        (fun outs left => c.post ghost ins outs ∧ budget - c.fee ≤ left) (fun _ _ => True) budget

/-- **The rule of a call.** At an application, where the callee's process is renamed to the
caller's roles and its results are handed on, a contract that holds judges the caller: the rest
is judged, on results that meet the postcondition, from every budget of at least the budget less
the fee. A stop of the callee is a stop of the caller, which a judgment of soundness accepts. -/
theorem Contract.call (c : Contract M p callee role) {draws : LawDraws M} (holds : c.Holds draws)
    (allowance : Occurrence → ℚ≥0) (start : List Frame) (covers : c.Covers allowance start)
    (ρ : Role → Role) {C D : Type} (leave : HList (RV M role) h.outs → C)
    (rest : C → Process (RSig M) Stop D) (done : D → ℚ≥0 → Prop) (halt : Stop → ℚ≥0 → Prop)
    (halts : ∀ stop left, halt stop left) (ghost : c.Ghost) (ins : HList (RV M role) h.ins)
    (pre : c.pre ghost ins) (budget : ℚ≥0) (fee : c.fee ≤ budget)
    (next : ∀ outs left, c.post ghost ins outs → budget - c.fee ≤ left →
      (rest (leave outs)).interpret (Fees.judgment draws allowance) done halt left) :
    (((mapR M ρ (roleMeaning M p callee role start ins)).map leave).bind rest).interpret
      (Fees.judgment draws allowance) done halt budget := by
  rw [Process.interpret_applied_blind ρ _ (Fees.judgment_blind ρ draws allowance)]
  exact Process.interpret_mono (Fees.judgment_monotone draws allowance)
    (fun outs left ⟨post, kept⟩ => next outs left post kept) (fun stop left _ => halts stop left)
    _ budget (holds allowance start covers ghost ins pre budget fee)

end ZkcFormal.Written
