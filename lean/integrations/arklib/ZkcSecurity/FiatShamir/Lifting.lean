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
the set with probability at most the error of its operation. It lifts to a
charged certificate of the typed engine whenever every query's charge covers
its law record's coefficient times its error plus its slack
(`UniformCertificate.charged`), and to a certificate with an error per
occurrence under the same condition with errors by event
(`UniformCertificate.certificate`).

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

/-- The uniform-sort local obligation of a doomed set at one residual: a doomed
result does not accept, doomed receives and sends stay doomed, and a doomed
query's uniform reply of its sort leaves the doomed set with probability at most
the error of its operation. -/
def UniformStep (laws : LawInterface I E P Raw) (doomed : PIR.Proc I A → Prop)
    (accepts : A → Prop) (error : I.Op → ENNReal) : PIR.Proc I A → Prop
  | .done value => ¬ accepts value
  | .halt _ => True
  | .call operation next =>
      match laws operation with
      | .receive _ _ => ∀ value, doomed (next value)
      | .send _ value => doomed (next value)
      | .query _ sort _ =>
          letI := sort
          Pr{let value ← $ᵗ (I.Reply operation)}[¬ doomed (next value)] ≤ error operation
      | .refuse => True

/-- Round-by-round soundness with uniform replies of each query's sort: a doomed
set whose every member meets its uniform-sort obligation. -/
structure UniformCertificate (laws : LawInterface I E P Raw) (accepts : A → Prop)
    (error : I.Op → ENNReal) where
  doomed : PIR.Proc I A → Prop
  step : ∀ process, doomed process → UniformStep laws doomed accepts error process

variable (laws : LawInterface I E P Raw)

/-- The uniform-sort obligation lifts to the charged obligation of the typed
engine when every query's charge covers its law record's coefficient times its
error plus its slack. -/
theorem UniformStep.charged {doomed : PIR.Proc I A → Prop} {accepts : A → Prop}
    {error : I.Op → ENNReal} {charge : List E → E → ENNReal}
    (covers : ∀ operation (event : E) (sort : SampleableType (I.Reply operation))
      (law : LawRecord (Raw event) (I.Reply operation)), laws operation = .query event sort law →
      ∀ preceding, law.factor * error operation + law.slack ≤ charge preceding event) :
    ∀ process, UniformStep laws doomed accepts error process →
      ChargedStep laws.absorb doomed accepts charge process
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
        intro preceding
        rw [prEvent_read Raw preceding event fun raw =>
          ∃ value, law.decode raw = some value ∧ ¬ doomed (next value)]
        exact (@LawRecord.escape_le _ _ _ sort law (fun value => ¬ doomed (next value)) _
          step).trans (covers operation event sort law site preceding)
      · simp only [ChargedStep, LawInterface.absorb, site]

/-- A uniform-sort certificate is a charged certificate of the typed engine over
the law interface's transcript interface, with the same doomed set, when every
query's charge covers its law record's coefficient times its error plus its
slack. -/
def UniformCertificate.charged {accepts : A → Prop} {error : I.Op → ENNReal}
    (certificate : UniformCertificate laws accepts error) (charge : List E → E → ENNReal)
    (covers : ∀ operation (event : E) (sort : SampleableType (I.Reply operation))
      (law : LawRecord (Raw event) (I.Reply operation)), laws operation = .query event sort law →
      ∀ preceding, law.factor * error operation + law.slack ≤ charge preceding event) :
    ChargedCertificate laws.absorb accepts charge where
  doomed := certificate.doomed
  step process member := UniformStep.charged laws covers process (certificate.step process member)

/-- A uniform-sort certificate is a certificate of the typed engine with an error
per occurrence, with the same doomed set, when every query's occurrence error
covers its law record's coefficient times its error plus its slack. -/
def UniformCertificate.certificate {accepts : A → Prop} {error : I.Op → ENNReal}
    (certificate : UniformCertificate laws accepts error) (eventError : E → ENNReal)
    (covers : ∀ operation (event : E) (sort : SampleableType (I.Reply operation))
      (law : LawRecord (Raw event) (I.Reply operation)), laws operation = .query event sort law →
      law.factor * error operation + law.slack ≤ eventError event) :
    Certificate laws.absorb accepts eventError where
  doomed := certificate.doomed
  step process member := ChargedStep.uncharged laws.absorb process
    ((certificate.charged laws (fun _ event => eventError event)
      fun operation event sort law site _ => covers operation event sort law site).step process
        member)

end Lifting

end ZkcSecurity.FiatShamir.Typed
