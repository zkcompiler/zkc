module

public import ZkcSecurity.FiatShamir.Typed
public import ZkcSecurity.FiatShamir.Laws

@[expose] public section

/-! Raw answers by the last event, and lifting uniform-sort certificates to
typed certificates.

**Raw answers by the last event.** In the history class the request is the last
event of its TranscriptQuery, so the oracle's raw answer type at a key is a
function of that event. `ByLast Raw key` is `Raw` of the key's last event, and
`Unit` at the empty key, which no query reaches; it is uniform when every
`Raw event` is (`ByLast.sampleable`). At a key `preceding ++ [event]` the answer
reads as a value of `Raw event` (`ByLast.read`), with the same uniform law
(`prEvent_read`). `Absorption.queryLast` is a query whose decoder takes that
value.

**Lifting.** A protocol's round-by-round analysis bounds a doomed query's escape
under the uniform law of the query's reply sort. A law interface
(`LawInterface`) presents a validator's operations to the transform with every
query decoded from the raw answer of its occurrence by a law record into its
reply sort (`LawInterface.absorb`). A uniform-sort certificate
(`UniformCertificate`) is a doomed set whose every member meets the
uniform-sort obligation (`UniformStep`): a doomed query's uniform reply leaves
the set with probability at most the error of its operation at its history. As
in the typed engine's charged certificates, the doomed set is indexed by the
absorbed history, so one operation at one occurrence can carry a different
error at each place it is reached, as the rounds of a loop whose occurrence has
no iteration coordinate do. It lifts to a charged certificate of the typed
engine, with the same doomed pairs, whenever every query's charge at a history
covers its law record's coefficient times its error there plus its slack
(`UniformCertificate.charged`).

Law-record decoders do not depend on the history before the occurrence: the
operands that a decoder reads are carried in the occurrence, the last event.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Typed
open OracleComp OracleSpec

section ByLast
variable {E : Type} (Raw : E → Type)

/-- `Raw` of the last event, and `Unit` without one. -/
def OfLast : Option E → Type
  | some event => Raw event
  | none => Unit

/-- The raw answer type of an oracle key: the raw type of its last event, and
`Unit` at the empty key, which no query reaches. -/
abbrev ByLast (key : List E) : Type := OfLast Raw key.getLast?

theorem byLast_append (preceding : List E) (event : E) :
    ByLast Raw (preceding ++ [event]) = Raw event := by
  simp [ByLast, OfLast]

/-- The answer at a key ending with an occurrence, read in the occurrence's raw
type. -/
def ByLast.read {preceding : List E} {event : E} : ByLast Raw (preceding ++ [event]) ≃ Raw event :=
  Equiv.cast (byLast_append Raw preceding event)

variable [∀ event, SampleableType (Raw event)]

instance OfLast.sampleable : ∀ last : Option E, SampleableType (OfLast Raw last)
  | some event => inferInstanceAs (SampleableType (Raw event))
  | none => inferInstanceAs (SampleableType Unit)

instance ByLast.sampleable (key : List E) : SampleableType (ByLast Raw key) :=
  OfLast.sampleable Raw key.getLast?

/-- Read in the occurrence's raw type, the uniform answer at a key is uniform. -/
theorem prEvent_read (preceding : List E) (event : E) (holds : Raw event → Prop) :
    Pr{let raw ← $ᵗ (ByLast Raw (preceding ++ [event]))}[holds (ByLast.read Raw raw)] =
      Pr{let raw ← $ᵗ (Raw event)}[holds raw] :=
  SampleableType.prEvent_uniformSample_equiv _ holds

variable {P Reply : Type}

/-- A query absorbed at `event` whose decoder reads the answer in the event's raw
type. -/
def Absorption.queryLast (event : E) (decode : List E → Raw event → Option Reply) :
    Absorption E P (ByLast Raw) Reply :=
  .query event fun preceding raw => decode preceding (ByLast.read Raw raw)

end ByLast

section Lifting
variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]

/-- How the transform treats one operation whose reply has type `Reply`, with
every query decoded from the raw answer of its occurrence by a law record into
the reply sort. -/
inductive LawAbsorption (E P : Type) (Raw : E → Type) [∀ event, SampleableType (Raw event)]
    (Reply : Type) where
  /-- Read the next proof message, absorb `event message` and continue with the
  reply `recover` reads from that event. -/
  | receive (event : P → E) (recover : E → Option Reply)
  /-- Absorb `event` and continue with `value`. -/
  | send (event : E) (value : Reply)
  /-- Absorb the occurrence `event`, ask the oracle and decode its raw answer by
  `law` into the reply sort, whose uniform law is `sort`. -/
  | query (event : E) (sort : SampleableType Reply) (law : @LawRecord (Raw event) Reply _ sort)
  /-- Refuse without consuming proof data. -/
  | refuse

/-- A law interface: the law absorption of every operation of `I`. -/
abbrev LawInterface (I : PIR.Signature) (E P : Type) (Raw : E → Type)
    [∀ event, SampleableType (Raw event)] :=
  (operation : I.Op) → LawAbsorption E P Raw (I.Reply operation)

/-- The transcript interface of a law interface: a query asks the oracle at its
occurrence and decodes the raw answer by its law record. -/
def LawInterface.absorb (laws : LawInterface I E P Raw) : Interface I E P (ByLast Raw) :=
  fun operation =>
    match laws operation with
    | .receive event recover => .receive event recover
    | .send event value => .send event value
    | .query event _ law => Absorption.queryLast Raw event fun _ raw => law.decode raw
    | .refuse => .refuse

/-- The uniform-sort local obligation of a doomed set indexed by the absorbed
history, at one residual reached after `history`: a doomed result does not
accept; after a receive whose event recovers a reply, and after a send, the
residual is doomed at the extended history; and a doomed query's uniform reply
of its sort leaves the doomed set at the extended history with probability at
most the error of its operation at that history. -/
def UniformStep (laws : LawInterface I E P Raw) (doomed : List E → PIR.Proc I A → Prop)
    (accepts : A → Prop) (error : List E → I.Op → ENNReal) (history : List E) :
    PIR.Proc I A → Prop
  | .done value => ¬ accepts value
  | .halt _ => True
  | .call operation next =>
      match laws operation with
      | .receive event recover => ∀ message value, recover (event message) = some value →
          doomed (history ++ [event message]) (next value)
      | .send event value => doomed (history ++ [event]) (next value)
      | .query event sort _ =>
          letI := sort
          Pr{let value ← $ᵗ (I.Reply operation)}[¬ doomed (history ++ [event]) (next value)] ≤
            error history operation
      | .refuse => True

/-- Round-by-round soundness with uniform replies of each query's sort: a set of
doomed pairs of an absorbed history and a residual, whose every member meets its
uniform-sort obligation. -/
structure UniformCertificate (laws : LawInterface I E P Raw) (accepts : A → Prop)
    (error : List E → I.Op → ENNReal) where
  doomed : List E → PIR.Proc I A → Prop
  step : ∀ history process, doomed history process →
    UniformStep laws doomed accepts error history process

variable (laws : LawInterface I E P Raw)

/-- The uniform-sort obligation lifts to the charged obligation of the typed
engine when every query's charge at a history covers its law record's
coefficient times its error at that history plus its slack. -/
theorem UniformStep.charged {doomed : List E → PIR.Proc I A → Prop} {accepts : A → Prop}
    {error : List E → I.Op → ENNReal} {charge : List E → E → ENNReal}
    (covers : ∀ history operation (event : E) (sort : SampleableType (I.Reply operation))
      (law : LawRecord (Raw event) (I.Reply operation)), laws operation = .query event sort law →
      law.factor * error history operation + law.slack ≤ charge history event)
    (history : List E) :
    ∀ process, UniformStep laws doomed accepts error history process →
      ChargedStep laws.absorb doomed accepts charge history process
  | .done _, step => step
  | .halt _, step => step
  | .call operation next, step => by
      rcases site : laws operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, sort, law⟩ | _
      · simp only [UniformStep, site] at step
        simp only [ChargedStep, LawInterface.absorb, site]
        exact step
      · simp only [UniformStep, site] at step
        simp only [ChargedStep, LawInterface.absorb, site]
        exact step
      · simp only [UniformStep, site] at step
        simp only [ChargedStep, LawInterface.absorb, site, Absorption.queryLast]
        rw [prEvent_read Raw history event fun raw =>
          ∃ value, law.decode raw = some value ∧ ¬ doomed (history ++ [event]) (next value)]
        exact (@LawRecord.escape_le _ _ _ sort law
          (fun value => ¬ doomed (history ++ [event]) (next value)) _ step).trans
          (covers history operation event sort law site)
      · simp only [ChargedStep, LawInterface.absorb, site]

/-- A uniform-sort certificate is a charged certificate of the typed engine over
the law interface's transcript interface, with the same doomed pairs, when every
query's charge at a history covers its law record's coefficient times its error
at that history plus its slack. -/
def UniformCertificate.charged {accepts : A → Prop} {error : List E → I.Op → ENNReal}
    (certificate : UniformCertificate laws accepts error) (charge : List E → E → ENNReal)
    (covers : ∀ history operation (event : E) (sort : SampleableType (I.Reply operation))
      (law : LawRecord (Raw event) (I.Reply operation)), laws operation = .query event sort law →
      law.factor * error history operation + law.slack ≤ charge history event) :
    ChargedCertificate laws.absorb accepts charge where
  doomed := certificate.doomed
  step history process member :=
    UniformStep.charged laws covers history process (certificate.step history process member)

end Lifting

end ZkcSecurity.FiatShamir.Typed
