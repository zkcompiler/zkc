module

public import Zkc.IR.Core.Laws
public import Zkc.Protocol.Logic.Transcript.Interactive

/-! The transcript interface of a side of a core protocol.

A side's process performs the effects `send`, `receive`, `draw`, `sample` and `read` at the
sites of its definitions. The interface classifies each of them for the readings and the
experiments of `Zkc.Protocol.Logic`:

- a `send` and a `read` absorb an event that records the site and the typed value;
- a `receive` reads the next proof message, a typed value, and absorbs the event that records
  it; a message of another type is refused;
- a `draw` is a query: it absorbs its occurrence, which records the site, the law and the
  law's inputs, and continues with the law's reading of a raw sample;
- a `sample` is a secret, treated as the policy `Secrets` says.

**Sample spaces.** A model gives no meaning to a sampling row. The experiments sample a raw
answer uniformly, so a reading needs, for every law, a sample space and the law's reading of a
sample (`Sampling`). A law that is uniform over its output has the output as its sample space
and reads every sample as itself.

**Secrets.** Under `Secrets.fresh` a `sample` is a query like a `draw`, with its own event. The
exact reading then speaks of every value of the secret. The interactive experiment answers the
secret with a fresh uniform sample, but its strategies see every earlier raw answer: a bound
proved over this interface holds against a prover that knows the secret, and no statement can
use that the secret is hidden. The Fiat–Shamir transform would answer the same query with the
transcript oracle at the public history, which every party can evaluate: over this interface it
describes a protocol whose secret is public. Under `Secrets.refused` a `sample` refuses. The
transform then stops at the first `sample`, and every reading accepts the stop: a side that
samples has no Fiat–Shamir transform, and its triples say nothing about what follows the
`sample`. A side that never samples, such as a verifier with public coins, reads the same under
both policies.

**Refusals.** A `receive` refuses a message of another type, under either policy. The interface
therefore does not admit every operation (`ZkcSecurity.Interactive.Total` fails), and an exact
triple with a false stop assertion does not show that every run of the interactive experiment
returns: a run stops `refused` when the strategy sends a value of the wrong type.
-/

@[expose] public section

set_option autoImplicit false

namespace Zkc.Core.Transcript

open Zkc.Source Zkc.Transcript

/-- A transcript event of a side: the site and the typed value of a `send`, of a received
message and of a `read`; the occurrence of a `draw` and of a `sample`, which records the law
and its inputs and not the reply. -/
inductive Event (Value : Ty → Type) where
  | sent (site : Site) (type : Ty) (value : Value type)
  | received (site : Site) (type : Ty) (value : Value type)
  | drawn (site : Site) (law : SamplingRow) (inputs : Values Value law.inputs)
  | sampled (site : Site) (law : SamplingRow) (inputs : Values Value law.inputs)
  | read (site : Site) (type : Ty) (position : Value type)

/-- The sample space of every sampling law of a model, which the experiments sample uniformly,
and the law's reading of a sample. A sample the law does not read stops the run. -/
class Sampling (model : Model) where
  Raw : (law : SamplingRow) → Values model.Value law.inputs → Type
  decode : (law : SamplingRow) → (inputs : Values model.Value law.inputs) → Raw law inputs →
    Option (model.Value law.output)

/-- How an interface treats `sample`, the effect of a secret. -/
inductive Secrets where
  /-- A query with its own event, answered by a fresh raw sample. -/
  | fresh
  /-- Refused: no value derived from a transcript stands for a secret. -/
  | refused

variable {model : Model}

/-- The raw answer of an occurrence: a sample of the law of a `draw` or a `sample`. No other
event is a query. -/
@[reducible] def Answer (model : Model) [Sampling model] : Event model.Value → Type
  | .drawn _ law inputs | .sampled _ law inputs => Sampling.Raw law inputs
  | .sent .. | .received .. | .read .. => PUnit

/-- Every raw answer is sampled uniformly when every sample space of the model is. -/
instance Answer.sampleable [Sampling model]
    [∀ (law : SamplingRow) (inputs : Values model.Value law.inputs),
      SampleableType (Sampling.Raw law inputs)] :
    ∀ event : Event model.Value, SampleableType (Answer model event)
  | .drawn _ law inputs => inferInstanceAs (SampleableType (Sampling.Raw law inputs))
  | .sampled _ law inputs => inferInstanceAs (SampleableType (Sampling.Raw law inputs))
  | .sent .. => inferInstanceAs (SampleableType PUnit)
  | .received .. => inferInstanceAs (SampleableType PUnit)
  | .read .. => inferInstanceAs (SampleableType PUnit)

/-- A proof message: a typed value. -/
abbrev Message (model : Model) : Type := Sigma model.Value

/-- The event of a message received at a site. -/
def received (site : Site) (message : Message model) : Event model.Value :=
  .received site message.1 message.2

open Classical in
/-- The value of a received event, at the type the receiver expects. -/
noncomputable def recovered (type : Ty) : Event model.Value → Option (model.Value type)
  | .received _ actual value => if same : actual = type then some (same ▸ value) else none
  | .sent .. | .drawn .. | .sampled .. | .read .. => none

/-- The transcript interface of a side. -/
noncomputable def interface [Sampling model] (secrets : Secrets) :
    Interface (Effects model) (Event model.Value) (Message model) (Answer model)
  | .send site type value => .send (.sent site type value) PUnit.unit
  | .receive site type => .receive (received site) (recovered type)
  | .draw site law inputs => .query (.drawn site law inputs) (Sampling.decode law inputs)
  | .sample site law inputs =>
      match secrets with
      | .fresh => .query (.sampled site law inputs) (Sampling.decode law inputs)
      | .refused => .refuse
  | .read site type position => .send (.read site type position) PUnit.unit

theorem received_mk (site : Site) (type : Ty) (value : model.Value type) :
    received site (⟨type, value⟩ : Message model) = .received site type value := rfl

theorem recovered_received (site : Site) (type : Ty) (value : model.Value type) :
    recovered type (received site (⟨type, value⟩ : Message model)) = some value := by
  simp only [recovered, received, dite_true]

/-- A property of every message that a receive recovers is a property of every value of the
expected type: the obligation of a receive names the received value alone. -/
theorem forall_recovered {site : Site} {type : Ty}
    (holds : Message model → model.Value type → Prop) :
    (∀ message value, recovered type (received site message) = some value →
        holds message value) ↔ ∀ value, holds ⟨type, value⟩ value := by
  constructor
  · intro every value
    exact every ⟨type, value⟩ value (recovered_received site type value)
  · rintro every ⟨actual, value⟩ result recovers
    simp only [recovered, received] at recovers
    split at recovers
    · rename_i same
      subst same
      cases recovers
      exact every value
    · cases recovers

end Zkc.Core.Transcript
