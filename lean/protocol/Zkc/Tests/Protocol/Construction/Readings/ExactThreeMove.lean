module

public import Zkc.Tools.Protocol.Readings

/-! A three-move verifier under the exact reading. The verifier receives a commitment, draws a
challenge, receives a response and decides. Under the exact judgment no reply is excluded, so the
derived triples hold on every run, for every reply: `transcript_decides` states the reached
history and the returned value of every returning run. -/

@[expose] public section
set_option experimental.vcgen true
open PIR Zkc.Source Zkc.Transcript Std.WP ProtocolProof
open ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition

namespace ProtocolProofExamples.ExactThreeMove

variable {A C Z : Type}

inductive Ev (A Z : Type) where
  | commit (value : A)
  | chal
  | resp (value : Z)

inductive VOp where
  | commit | draw | resp

abbrev VSig (A C Z : Type) : Signature :=
  ⟨VOp, fun | .commit => A | .draw => C | .resp => Z⟩

def event : A ⊕ Z → Ev A Z
  | .inl value => .commit value
  | .inr value => .resp value

/-- The commitment and the response are proof messages; the challenge is a query site. -/
def absorb : Interface (VSig A C Z) (Ev A Z) (A ⊕ Z) (fun _ => C) := fun op =>
  match op with
  | .commit => .receive event (fun e => match e with | .commit value => some value | _ => none)
  | .draw => .query Ev.chal (fun raw => some raw)
  | .resp => .receive event (fun e => match e with | .resp value => some value | _ => none)

inductive Ty where
  | commit | chal | resp | out
  deriving DecidableEq

inductive Op where
  | commit | draw | resp | decide

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .commit | .draw | .resp => []
    | .decide => [.commit, .chal, .resp]
  result
    | .commit => .commit
    | .draw => .chal
    | .resp => .resp
    | .decide => .out
  condition := .out

abbrev meaning (verify : A → C → Z → Bool) : Interpretation language (VSig A C Z) where
  Value
    | .commit => A
    | .chal => C
    | .resp => Z
    | .out => A × C × Z × Bool
  condition := fun out => out.2.2.2
  operation
    | .commit, .nil => .call .commit .done
    | .draw, .nil => .call .draw .done
    | .resp, .nil => .call .resp .done
    | .decide, .cons a (.cons c (.cons z .nil)) => .done (a, c, z, verify a c z)

/-- Receive the commitment, draw, receive the response, decide. -/
def verifier : Region (scalarDialect language) [] [.out] :=
  .letOp (.ordinary .commit) .nil .nil
    (.letOp (.ordinary .draw) .nil .nil
      (.letOp (.ordinary .resp) .nil .nil
        (.letOp (.ordinary .decide)
          (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil
          (.ret (.cons .here .nil)))))

/-- The exact reading of this interface. -/
noncomputable abbrev logic : WPMonad (Process (VSig A C Z)) (Assert (Ev A Z)) (StopAssert (Ev A Z)) :=
  chargedMonad absorb exactEscape exactEscape_antitone

attribute [local instance] logic
attribute [local construction_simp] absorb

variable (verify : A → C → Z → Bool)

@[spec] theorem commit_rule : (meaning verify).operation .commit .nil = .call .commit .done := rfl
@[spec] theorem draw_rule : (meaning verify).operation .draw .nil = .call .draw .done := rfl
@[spec] theorem resp_rule : (meaning verify).operation .resp .nil = .call .resp .done := rfl
@[spec] theorem decide_rule (a : A) (c : C) (z : Z) :
    (meaning verify).operation .decide (.cons a (.cons c (.cons z .nil))) =
      .done (a, c, z, verify a c z) := rfl


/-- Every accepting run, for every reply, returns a transcript that passes the check. The
returned decision is the check itself, so this exercises the construction of an exact triple
rather than a property of the protocol. -/
theorem accepted_check :
    ⦃fun _ => ⟨True⟩⦄
      verifier.denote (meaning verify).regionMeaning Values.nil.get
    ⦃fun out _ => ⟨(out.get .here).2.2.2 = true →
        verify (out.get .here).1 (out.get .here).2.1 (out.get .here).2.2.1 = true⟩;
      estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold verifier
  construct_region

/-- Every returning run, for every commitment, challenge and response, appends exactly three
events to the history: the commitment, the occurrence of the challenge site and the response. The
challenge event records only that the challenge was drawn, not its value; the run returns the
commitment, the challenge, the response and the decision of the check on them. -/
theorem transcript_decides (start : List (Ev A Z)) :
    ⦃fun history => ⟨history = start⟩⦄
      verifier.denote (meaning verify).regionMeaning Values.nil.get
    ⦃fun out history => ⟨∃ commitment challenge response,
        history = start ++ [.commit commitment, .chal, .resp response] ∧
        out.get .here = (commitment, challenge, response, verify commitment challenge response)⟩;
      estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold verifier
  construct_region
  -- One obligation remains: the reached history and the returned value, for every commitment,
  -- every challenge reply and every response.
  rintro rfl message commitment recovered raw challenge decoded message' response recovered'
  obtain rfl : raw = challenge := Option.some.inj decoded
  cases message with
  | inr _ => cases recovered
  | inl value =>
    cases message' with
    | inl _ => cases recovered'
    | inr value' =>
      obtain rfl : value = commitment := Option.some.inj recovered
      obtain rfl : value' = response := Option.some.inj recovered'
      exact ⟨value, raw, value', by simp [event], rfl⟩

/-- Adequacy: the exact triple is the charged reading at the exact judgment, and exact evidence
is charged evidence at every bounded judgment, whatever the charge. -/
theorem accepted_check_bounded [SampleableType C] (charge : List (Ev A Z) → Ev A Z → ENNReal) :
    absorb.Charged (boundedEscape charge)
      (fun _ out => (out.get .here).2.2.2 = true →
        verify (out.get .here).1 (out.get .here).2.1 (out.get .here).2.2.1 = true)
      (verifier.denote (meaning verify).regionMeaning Values.nil.get) [] :=
  bounded_of_exact absorb charge
    (charged_of_triple absorb exactEscape exactEscape_antitone (accepted_check verify) [] trivial)

#print axioms accepted_check
#print axioms transcript_decides
#print axioms accepted_check_bounded

end ProtocolProofExamples.ExactThreeMove
