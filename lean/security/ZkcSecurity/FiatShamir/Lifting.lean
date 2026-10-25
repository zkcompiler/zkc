module

public import ZkcSecurity.FiatShamir.Typed
public import ZkcSecurity.FiatShamir.Laws

@[expose] public section

/-! Lifting uniform-sort certificates to typed certificates.

A protocol's round-by-round analysis bounds a doomed query's escape under the
uniform law of the query's reply sort. A law interface (`LawInterface`)
presents a validator's operations to the transform with every query decoded
from the raw answer of its occurrence by a law record into its reply sort
(`LawInterface.absorb`). A uniform-sort certificate (`UniformCertificate`) is a
doomed set whose every member meets the uniform-sort obligation
(`UniformStep`): a doomed query's uniform reply leaves the set with probability
at most the error of its operation at its history. As in the typed engine's
charged certificates, the doomed set is indexed by the absorbed history, so one
operation at one occurrence can carry a different error at each place it is
reached, as the rounds of a loop whose occurrence has no iteration coordinate
do. It lifts to a charged certificate of the typed engine, with the same doomed
pairs, whenever every query's charge at a history covers its law record's
coefficient times its error there plus its slack
(`UniformCertificate.charged`): the law record's domination `κ·ν + λ` of the
uniform law `ν` of the reply sort. Uniform laws of the reply sorts are the
current specialization of a record's ideal law.

For a doomed set and an error that ignore the history, whose receives keep every
reply doomed, the same lifting gives a per-event certificate
(`UniformEventStep.typed`, `UniformEventCertificate.typed`), each occurrence
charged its law record's coefficient times its operation's error plus its slack.

Law-record decoders read the raw answer of the occurrence alone: the operands
that a decoder reads are carried in the occurrence, the last event of the key.
The raw answers by the last event, `ByLast`, are in
`ZkcSecurity.FiatShamir.Interface`.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Typed
open OracleComp OracleSpec

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
def LawInterface.absorb (laws : LawInterface I E P Raw) : Interface I E P Raw :=
  fun operation =>
    match laws operation with
    | .receive event recover => .receive event recover
    | .send event value => .send event value
    | .query event _ law => .query event law.decode
    | .refuse => .refuse

/-- The uniform-sort local obligation of a doomed set indexed by the absorbed
history, at one residual reached after `history`: a doomed result does not
accept; after a receive whose event recovers a reply, and after a send, the
residual is doomed at the extended history; and a doomed query's uniform reply
of its sort leaves the doomed set at the extended history with probability at
most the error of its operation at that history. -/
def UniformStep (laws : LawInterface I E P Raw) (doomed : List E → PIR.Process I A → Prop)
    (accepts : A → Prop) (error : List E → I.Op → ENNReal) (history : List E) :
    PIR.Process I A → Prop
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
  doomed : List E → PIR.Process I A → Prop
  step : ∀ history process, doomed history process →
    UniformStep laws doomed accepts error history process

variable (laws : LawInterface I E P Raw)

/-- The uniform-sort obligation lifts to the charged obligation of the typed
engine when every query's charge at a history covers its law record's
coefficient times its error at that history plus its slack. -/
theorem UniformStep.charged {doomed : List E → PIR.Process I A → Prop} {accepts : A → Prop}
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
        simp only [ChargedStep, LawInterface.absorb, site]
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

/-- The uniform-sort local obligation of a doomed set that ignores the history: a
doomed result does not accept; every reply of a doomed receive and the reply of a
doomed send stay doomed; and a doomed query's uniform reply of its sort leaves
the doomed set with probability at most the error of its operation. -/
def UniformEventStep (laws : LawInterface I E P Raw) (doomed : PIR.Process I A → Prop)
    (accepts : A → Prop) (error : I.Op → ENNReal) : PIR.Process I A → Prop
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

/-- Round-by-round soundness with uniform replies of each query's sort and a doomed
set and errors that ignore the history. -/
structure UniformEventCertificate (laws : LawInterface I E P Raw) (accepts : A → Prop)
    (error : I.Op → ENNReal) where
  doomed : PIR.Process I A → Prop
  step : ∀ process, doomed process → UniformEventStep laws doomed accepts error process

/-- The uniform-sort obligation of a history-free doomed set lifts to the typed
per-event obligation when every query occurrence's error covers its law record's
coefficient times its operation's error plus its slack. -/
theorem UniformEventStep.typed {doomed : PIR.Process I A → Prop} {accepts : A → Prop}
    {error : I.Op → ENNReal} {eventError : E → ENNReal}
    (covers : ∀ operation (event : E) (sort : SampleableType (I.Reply operation))
      (law : LawRecord (Raw event) (I.Reply operation)), laws operation = .query event sort law →
      law.factor * error operation + law.slack ≤ eventError event) :
    ∀ process, UniformEventStep laws doomed accepts error process →
      Step laws.absorb doomed accepts eventError process
  | .done _, step => step
  | .halt _, step => step
  | .call operation next, step => by
      rcases site : laws operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, sort, law⟩ | _
      · simp only [UniformEventStep, site] at step
        simp only [Step, LawInterface.absorb, site]
        exact step
      · simp only [UniformEventStep, site] at step
        simp only [Step, LawInterface.absorb, site]
        exact step
      · simp only [UniformEventStep, site] at step
        simp only [Step, LawInterface.absorb, site]
        exact (@LawRecord.escape_le _ _ _ sort law (fun value => ¬ doomed (next value)) _ step).trans
          (covers operation event sort law site)
      · simp only [Step, LawInterface.absorb, site]

/-- A history-free uniform-sort certificate is a per-event certificate of the
typed engine over the law interface's transcript interface, with the same doomed
residuals. -/
def UniformEventCertificate.typed {accepts : A → Prop} {error : I.Op → ENNReal}
    (certificate : UniformEventCertificate laws accepts error) (eventError : E → ENNReal)
    (covers : ∀ operation (event : E) (sort : SampleableType (I.Reply operation))
      (law : LawRecord (Raw event) (I.Reply operation)), laws operation = .query event sort law →
      law.factor * error operation + law.slack ≤ eventError event) :
    Certificate laws.absorb accepts eventError where
  doomed := certificate.doomed
  step process member :=
    UniformEventStep.typed laws covers process (certificate.step process member)

end Lifting

end ZkcSecurity.FiatShamir.Typed
