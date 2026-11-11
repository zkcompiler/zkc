module

import Zkc.Protocol.Logic.WeakestPrecondition
import Zkc.Tools.Protocol.Readings

@[expose] section

/-! WP boundary controls: histories, decoding, stops, infinite cost and empty loops.
These are interpretation checks, not cryptographic probability bounds. -/
namespace TestsSecurity.WeakestPrecondition
open Zkc.Transcript Zkc.Obligations ZkcSecurity.FiatShamir
open Std.WP ZkcSecurity.Obligations.WeakestPrecondition

inductive Operation where
  | receive | send | query | refuse
  deriving DecidableEq

def decode : Bool → Option Nat
  | true => some 7
  | false => none

def absorb : Interface ⟨Operation, fun _ => Nat⟩ Nat Nat (fun _ => Bool)
  | .receive => .receive id some
  | .send => .send 4 7
  | .query => .query 5 decode
  | .refuse => .refuse

def noEscape : EscapeJudgment Nat (fun _ => Bool) := fun _ _ bad => ∀ answer, ¬ bad answer

attribute [local construction_simp] absorb

theorem antitone : noEscape.Antitone := by
  intro _ _ lower upper contained disjoint answer inside
  exact disjoint answer (contained answer inside)

-- Message-dependent control, then a challenge after a send.
def exchange : PIR.Process ⟨Operation, fun _ => Nat⟩ Nat := do
  let message ← PIR.Process.call .receive .done
  if message = 0 then .halt .reject else do
    let _ ← PIR.Process.call .send .done
    let value ← PIR.Process.call .query .done
    pure value

set_option experimental.vcgen true in
example : ChargedTriple absorb noEscape antitone exchange (fun _ => ⟨True⟩)
    (fun result _ => ⟨result = 7⟩) estack⟨fun _ _ => ⟨True⟩⟩ := by
  let := chargedMonad absorb noEscape antitone
  unfold exchange
  construct_region
  intro message value recovered
  split
  · trivial
  · rintro answer ⟨reply, decoded, wrong⟩
    cases answer <;> simp only [decode, reduceCtorEq, Option.some.injEq] at decoded
    exact wrong decoded.symm

-- Prices are assessed at the reached history, after the sent event.
def priced (history : List Nat) (_ : Nat) : ENNReal := history.length

def sentQuery : PIR.Process ⟨Operation, fun _ => Nat⟩ Nat := do
  let _ ← PIR.Process.call .send .done
  let value ← PIR.Process.call .query .done
  pure value

set_option experimental.vcgen true in
example : CostTriple absorb priced sentQuery
    (fun history credit => ⟨((history.length + 1 : Nat) : ENNReal) ≤ credit⟩)
    (fun _ reached _ => ⟨reached.length ≥ 2⟩) estack⟨fun _ _ _ => ⟨True⟩⟩ := by
  let := costMonad absorb priced
  unfold sentQuery
  construct_region
  intro budget
  exact ⟨0, by simpa [priced] using budget, fun _ => by simp⟩

-- Undercharging the prefix is refused even when the reply is discarded.
example : ¬ Typed.ChargedCostBound absorb priced sentQuery [1] 1 := by
  change ¬ ∃ remaining : ENNReal, 2 + remaining ≤ 1 ∧ ∀ (_ : Nat), True
  intro bounded
  obtain ⟨remaining, paid, _⟩ := bounded
  have lower : (2 : ENNReal) ≤ 2 + remaining := le_self_add
  have impossible := lower.trans paid
  norm_num at impossible

-- No subtraction of infinity is hidden in composition.
example (process : PIR.Process ⟨Operation, fun _ => Nat⟩ Nat)
    (bounded : ∀ history, Typed.ChargedCostBound absorb priced process history ⊤)
    (history : List Nat) :
    costWP absorb priced process (fun _ _ remaining => (⊤ : ENNReal) ≤ remaining)
      estack⟨fun _ _ _ => True⟩ history ⊤ :=
  reserve absorb priced ⊤ process history ⊤ ⊤ (bounded history) (by simp)

example : ¬ ChargedTriple absorb noEscape antitone (.done 0) (fun _ => ⟨True⟩)
    (fun value _ => ⟨value = 7⟩) estack⟨fun _ _ => ⟨True⟩⟩ := by
  let := chargedMonad absorb noEscape antitone
  intro proof
  have impossible := proof.le_wp [] trivial
  change (0 : Nat) = 7 at impossible
  omega

-- Explicit stops remain visible when their postcondition excludes them.
example : ¬ ChargedTriple absorb noEscape antitone (.halt .abort : PIR.Process ⟨Operation, fun _ => Nat⟩ Nat)
    (fun _ => ⟨True⟩) (fun _ _ => ⟨True⟩) estack⟨fun _ _ => ⟨False⟩⟩ := by
  let := chargedMonad absorb noEscape antitone
  intro proof
  exact proof.le_wp [] trivial

-- Refused absorption is rejection, not successful execution: False exception
-- postconditions alone do not turn charged WP into honest completeness.
example : ChargedTriple absorb noEscape antitone (.call .refuse .done : PIR.Process ⟨Operation, fun _ => Nat⟩ Nat)
    (fun _ => ⟨True⟩) (fun _ _ => ⟨False⟩) estack⟨fun _ _ => ⟨False⟩⟩ := by
  let := chargedMonad absorb noEscape antitone
  exact ⟨fun _ _ => trivial⟩

-- Zero iterations establish the terminal assertion without using the body.
example (step : Nat → PIR.Process ⟨Operation, fun _ => Nat⟩ Nat) :
    ¬ ChargedTriple absorb noEscape antitone (PIR.repeatN 0 step 3)
      (fun _ => ⟨True⟩) (fun value _ => ⟨value = 4⟩) estack⟨fun _ _ => ⟨True⟩⟩ := by
  let := chargedMonad absorb noEscape antitone
  intro proof
  have impossible := proof.le_wp [] trivial
  change (3 : Nat) = 4 at impossible
  omega

/-! The explicit-absorption rules state a node obligation from an absorption equation, with an
author-chosen cut for a charged query and an author-chosen reservation for a cost query. -/

abbrev Signature : PIR.Signature := ⟨Operation, fun _ => Nat⟩

example (post : Nat → ProtocolProof.Assert Nat) (stopped : ProtocolProof.StopAssert Nat) :
    ChargedTriple absorb noEscape antitone (.call .receive .done : PIR.Process Signature Nat)
      (fun history => ⟨∀ message value, some message = some value →
        (post value (history ++ [message])).holds⟩) post stopped :=
  receive_spec absorb noEscape antitone .receive id some rfl post stopped

example (post : Nat → ProtocolProof.Assert Nat) (stopped : ProtocolProof.StopAssert Nat) :
    ChargedTriple absorb noEscape antitone (.call .send .done : PIR.Process Signature Nat)
      (fun history => post 7 (history ++ [4])) post stopped :=
  send_spec absorb noEscape antitone .send 4 7 rfl post stopped

-- The cut excludes the raw answer `false`, which does not decode.
example (post : Nat → ProtocolProof.Assert Nat) (stopped : ProtocolProof.StopAssert Nat) :
    ChargedTriple absorb noEscape antitone (.call .query .done : PIR.Process Signature Nat)
      (fun history => ⟨noEscape history 5 (fun raw => raw = false) ∧ ∀ raw value,
        decode raw = some value → ¬ raw = false → (post value (history ++ [5])).holds⟩)
      post stopped :=
  query_spec absorb noEscape antitone .query 5 decode rfl (fun raw => raw = false) post stopped

-- The generic query node: the judgment of the decoded replies whose continuation fails.
example (next : Nat → List Nat → Prop) (history : List Nat) :
    (absorb .query).ChargedNode noEscape next history ↔
      ∀ raw, ¬ ∃ value, decode raw = some value ∧ ¬ next value (history ++ [5]) := by
  rw [show absorb .query = .query 5 decode from rfl, chargedNode_query]
  rfl

example (post : Nat → ProtocolProof.CostAssert Nat) (stopped : ProtocolProof.CostStopAssert Nat) :
    CostTriple absorb priced (.call .receive .done : PIR.Process Signature Nat)
      (fun history cost => ⟨∀ message value, some message = some value →
        (post value (history ++ [message]) cost).holds⟩) post stopped :=
  receive_cost absorb priced .receive id some rfl post stopped

example (post : Nat → ProtocolProof.CostAssert Nat) (stopped : ProtocolProof.CostStopAssert Nat) :
    CostTriple absorb priced (.call .send .done : PIR.Process Signature Nat)
      (fun history cost => post 7 (history ++ [4]) cost) post stopped :=
  send_cost absorb priced .send 4 7 rfl post stopped

-- The query is priced at the reached history; the continuation keeps the reserved credit.
example (post : Nat → ProtocolProof.CostAssert Nat) (stopped : ProtocolProof.CostStopAssert Nat) :
    CostTriple absorb priced (.call .query .done : PIR.Process Signature Nat)
      (fun history cost => ⟨(history.length : ENNReal) + 1 ≤ cost ∧
        ∀ value, (post value (history ++ [5]) 1).holds⟩) post stopped :=
  query_cost absorb priced .query 5 decode rfl 1 post stopped

end TestsSecurity.WeakestPrecondition

end
