module

public import ZkcSecurity.FiatShamir.Typed
public import ZkcSecurity.Commitment.Extractable
public import ZkcSecurity.Commitment.TableLog

@[expose] public section

/-! # Verifiers with committed tables

A verifier with committed oracle messages is a process over `committed J Shape Value`: the base
operations `J` of a typed transcript interface, the commitment of a table of a given shape, and
the read of one entry of a committed table (by its commitment's handle, counted from the first
commitment, and a position). Reads are the only way the verifier sees a committed table, so a
table's entries reach later computation only through authenticated reads.

The verifier has two readings.

* **Ideal** (`withTables`): a commitment receives the table in the clear through the base
  operation `Words.word`, and a read returns the entry of a received table. This is a process
  over `J` to which the typed Fiat–Shamir engine applies, with the absorbed history containing
  the tables.
* **Concrete** (`run`): the verifier runs against a joint oracle (`joint`) on transcript keys and
  hash calls. A commitment reads a root from the proof and absorbs it; a read takes the next
  opening of the proof and authenticates it against the root with hash calls (`liftHash`); a
  query asks the transcript oracle at the absorbed history and the query's occurrence. Base
  receives and sends absorb the ideal interface's events.

The joint oracle answers a transcript key `(history, occurrence)` in the raw type of the
occurrence alone, `R [occurrence]`, which is the raw type the typed certificate bounds with an
empty preceding history. Keys are pairs rather than histories ending with the occurrence; the two
encodings are in bijection on the histories that end with a query occurrence.

`replay` walks the verifier along absorbed concrete events, answering transcript queries from a
table of answers and every committed root from an extraction (`extracted`), and returns the
residual process with its tables. `Escapes` is the escape of a doomed residual at a transcript
query, read through `withTables`; `escapes_le` bounds it by the certificate's error.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec ZkcSecurity.FiatShamir

/-- Operations of a verifier with committed tables. -/
inductive CommittedOp (Op Shape : Type) where
  /-- An operation of the typed transcript interface. -/
  | base (operation : Op)
  /-- Receive the commitment of a table of shape `shape`. -/
  | commit (shape : Shape)
  /-- Read entry `position` of the table committed by commitment `handle`. -/
  | read (handle position : ℕ)

/-- The signature of a verifier over base operations `J` with committed tables of shapes `Shape`
and entries `Value`. A commitment replies nothing; a read replies the entry. -/
abbrev committed (J : PIR.Signature) (Shape Value : Type) : PIR.Signature where
  Op := CommittedOp J.Op Shape
  Reply
    | .base operation => J.Reply operation
    | .commit _ => Unit
    | .read _ _ => Value

/-- The base operations through which the ideal protocol receives a committed table in the
clear, with the conversions between their replies and tables. -/
structure Words (J : PIR.Signature) (Shape Value : Type) where
  word : Shape → J.Op
  toTable : (shape : Shape) → J.Reply (word shape) → Table Value
  ofTable : (shape : Shape) → Table Value → J.Reply (word shape)

/-- The entry `position` of the table with handle `handle`. -/
def lookup {Value : Type} (tables : List (Table Value)) (handle position : ℕ) : Option Value :=
  match tables[handle]? with
  | some table => table position
  | none => none

variable {J : PIR.Signature} {E P Shape Value Query Y A : Type} {R : List E → Type}

/-- The ideal reading: commitments receive their tables in the clear, reads return the entries of
received tables, and a read outside every received table rejects. -/
def withTables (words : Words J Shape Value) :
    List (Table Value) → PIR.Proc (committed J Shape Value) A → PIR.Proc J A
  | _, .done value => .done value
  | _, .halt stop => .halt stop
  | tables, .call (.base operation) next =>
      .call operation fun reply => withTables words tables (next reply)
  | tables, .call (.commit shape) next =>
      .call (words.word shape) fun received =>
        withTables words (tables ++ [words.toTable shape received]) (next ())
  | tables, .call (.read handle position) next =>
      match lookup tables handle position with
      | some value => withTables words tables (next value)
      | none => .halt .reject

/-- The table the ideal reading records for an extracted table: the extracted table passed
through the reply of the word operation. -/
def normalized (words : Words J Shape Value) (extracted : Shape → Y → Table Value) (shape : Shape)
    (root : Y) : Table Value :=
  words.toTable shape (words.ofTable shape (extracted shape root))

/-- Events absorbed by the concrete reading: the events of base operations, and the roots of
committed tables with their shapes. -/
inductive Absorbed (E Shape Y : Type) where
  | event (event : E)
  | root (shape : Shape) (root : Y)
  deriving DecidableEq

/-- The committed root an absorbed event carries, if any. -/
def Absorbed.committed {E Shape Y : Type} : Absorbed E Shape Y → Option (Shape × Y)
  | .root shape committedRoot => some (shape, committedRoot)
  | .event _ => none

/-- Proof messages of the concrete reading: messages of base receives and committed roots. -/
inductive Message (P Y : Type) where
  | plain (message : P)
  | root (root : Y)

/-- A concrete proof: its messages in order, then the openings in the order of the reads. -/
structure Proof (P Value Y : Type) where
  messages : List (Message P Y)
  openings : List (Opening Value Y)

/-- A transcript key: the absorbed history before a query and the query's occurrence. -/
abbrev TranscriptKey (E Shape Y : Type) := List (Absorbed E Shape Y) × E

/-- Keys of the joint oracle: transcript keys and hash calls. -/
abbrev JointKey (E Shape Y Query : Type) := TranscriptKey E Shape Y ⊕ Query

/-- Answers of the joint oracle: a transcript key is answered in the raw type of its occurrence
alone, a hash call by a hash value. -/
def JointRange {E : Type} (R : List E → Type) (Shape Y Query : Type) :
    JointKey E Shape Y Query → Type
  | .inl key => R [key.2]
  | .inr _ => Y

/-- The joint oracle on transcript keys and hash calls. -/
abbrev joint {E : Type} (R : List E → Type) (Shape Y Query : Type) :=
  OracleSpec.ofFn (JointRange R Shape Y Query)

instance jointSampleable {E : Type} (R : List E → Type) (Shape Y Query : Type)
    [∀ key, SampleableType (R key)] [SampleableType Y] :
    ∀ key, SampleableType (JointRange R Shape Y Query key)
  | .inl key => inferInstanceAs (SampleableType (R [key.2]))
  | .inr _ => inferInstanceAs (SampleableType Y)

section Hash

/-- Hash calls answered by the joint oracle. -/
def hashCall (R : List E → Type) (Shape : Type) :
    QueryImpl (Query →ₒ Y) (OracleComp (joint R Shape Y Query)) := fun query =>
  (liftM ((joint R Shape Y Query).query (.inr query)) : OracleComp (joint R Shape Y Query) Y)

/-- A hash computation run on the joint oracle. -/
def liftHash (R : List E → Type) (Shape : Type) {α : Type}
    (computation : OracleComp (Query →ₒ Y) α) : OracleComp (joint R Shape Y Query) α :=
  simulateQ (hashCall R Shape) computation

/-- The hash part of a joint answer table. -/
def hashAnswers (table : (key : JointKey E Shape Y Query) → JointRange R Shape Y Query key) :
    Query → Y := fun query => table (.inr query)

theorem evalWithAnswerFn_liftHash {α : Type}
    (table : (key : JointKey E Shape Y Query) → JointRange R Shape Y Query key)
    (computation : OracleComp (Query →ₒ Y) α) :
    evalWithAnswerFn (QueryImpl.ofFn table) (liftHash R Shape computation) =
      evalWithAnswerFn (QueryImpl.ofFn (hashAnswers table)) computation := by
  rw [liftHash, evalWithAnswerFn_simulateQ]
  rfl

theorem tableQueryLog_liftHash {α : Type}
    (table : (key : JointKey E Shape Y Query) → JointRange R Shape Y Query key) :
    ∀ computation : OracleComp (Query →ₒ Y) α,
      tableQueryLog (liftHash R Shape computation) table =
        (tableQueryLog computation (hashAnswers table)).map fun entry =>
          (⟨.inr entry.1, entry.2⟩ :
            (key : JointKey E Shape Y Query) × JointRange R Shape Y Query key) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftHash]
  | query_bind queried next ih =>
      simp only [liftHash, simulateQ_bind, simulateQ_spec_query, hashCall] at ih ⊢
      refine (tableQueryLog_query_bind (R := JointRange R Shape Y Query) (Sum.inr queried)
        (fun answer => simulateQ (hashCall R Shape) (next answer)) table).trans ?_
      rw [tableQueryLog_query_bind, List.map_cons]
      exact congrArg (List.cons _) (ih _)

end Hash

section Run
variable (absorb : Typed.Interface J E P R) (scheme : Extractable Shape Value Query Y)

/-- The concrete reading of a verifier with committed tables against the joint oracle, from the
absorbed `history` and the committed `roots`, reading `messages` and `openings`. -/
def run : PIR.Proc (committed J Shape Value) A → List (Absorbed E Shape Y) → List (Shape × Y) →
    List (Message P Y) → List (Opening Value Y) →
    OracleComp (joint R Shape Y Query) (PIR.Outcome A)
  | .done value, _, _, _, _ => pure (.returned value)
  | .halt stop, _, _, _, _ => pure (.stopped stop)
  | .call (.base operation) next, history, roots, messages, openings =>
      match absorb operation with
      | .receive event recover =>
          match messages with
          | .plain message :: rest =>
              match recover (event message) with
              | some value =>
                  run (next value) (history ++ [.event (event message)]) roots rest openings
              | none => pure (.stopped .refused)
          | _ => pure (.stopped .refused)
      | .send event value =>
          run (next value) (history ++ [.event event]) roots messages openings
      | .query event decode => do
          let raw ← liftM ((joint R Shape Y Query).query (.inl (history, event)))
          match decode [] raw with
          | some value => run (next value) (history ++ [.event event]) roots messages openings
          | none => pure (.stopped .exhausted)
      | .refuse => pure (.stopped .refused)
  | .call (.commit shape) next, history, roots, messages, openings =>
      match messages with
      | .root root :: rest =>
          run (next ()) (history ++ [.root shape root]) (roots ++ [(shape, root)]) rest openings
      | _ => pure (.stopped .refused)
  | .call (.read handle position) next, history, roots, messages, openings =>
      match roots[handle]?, openings with
      | some (shape, root), opening :: rest => do
          let accepted ← liftHash R Shape (scheme.authenticate shape root position opening)
          match accepted with
          | true => run (next opening.value) history roots messages rest
          | false => pure (.stopped .reject)
      | _, _ => pure (.stopped .refused)

end Run

section Replay
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y]
variable (absorb : Typed.Interface J E P R) (words : Words J Shape Value)

/-- Answer the reads at the head of a process from the tables. -/
def settle (tables : List (Table Value)) :
    PIR.Proc (committed J Shape Value) A → PIR.Proc (committed J Shape Value) A
  | .call (.read handle position) next =>
      match lookup tables handle position with
      | some value => settle tables (next value)
      | none => .halt .reject
  | process => process

/-- Walk a verifier along absorbed concrete events: receives recover their replies from their
events, queries are answered by decoding `answers` at their keys, commitments record the
normalized extraction of their roots, and reads are answered from the recorded tables. The
result is the residual after the events, with its reads at the head answered, and its tables;
`none` when the events are not a history the concrete reading could absorb. -/
def replay (extracted : Shape → Y → Table Value)
    (answers : (key : TranscriptKey E Shape Y) → R [key.2]) :
    PIR.Proc (committed J Shape Value) A → List (Table Value) → List (Absorbed E Shape Y) →
      List (Absorbed E Shape Y) →
      Option (PIR.Proc (committed J Shape Value) A × List (Table Value))
  | process, tables, _, [] => some (settle tables process, tables)
  | .done _, _, _, _ :: _ => none
  | .halt _, _, _, _ :: _ => none
  | .call (.read handle position) next, tables, history, observed :: rest =>
      match lookup tables handle position with
      | some value => replay extracted answers (next value) tables history (observed :: rest)
      | none => none
  | .call (.base operation) next, tables, history, observed :: rest =>
      match absorb operation with
      | .receive _ recover =>
          match observed with
          | .event received =>
              match recover received with
              | some value =>
                  replay extracted answers (next value) tables (history ++ [observed]) rest
              | none => none
          | .root _ _ => none
      | .send event value =>
          if observed = .event event then
            replay extracted answers (next value) tables (history ++ [observed]) rest
          else none
      | .query event decode =>
          if observed = .event event then
            match decode [] (answers (history, event)) with
            | some value =>
                replay extracted answers (next value) tables (history ++ [observed]) rest
            | none => none
          else none
      | .refuse => none
  | .call (.commit shape) next, tables, history, observed :: rest =>
      match observed with
      | .root committedShape root =>
          if committedShape = shape then
            replay extracted answers (next ()) (tables ++ [normalized words extracted shape root])
              (history ++ [observed]) rest
          else none
      | .event _ => none

end Replay

section Escape
variable (absorb : Typed.Interface J E P R) (words : Words J Shape Value)

/-- A residual at a transcript query, doomed in its ideal reading, whose query decodes `raw` to a
reply that leaves the doomed set. Only base queries can escape. -/
def Escapes (doomed : PIR.Proc J A → Prop) :
    PIR.Proc (committed J Shape Value) A → List (Table Value) → (event : E) → R [event] → Prop
  | .call (.base operation) next, tables, event, raw =>
      ∃ decode, absorb operation = .query event decode ∧
        doomed (withTables words tables (.call (.base operation) next)) ∧
        ∃ value, decode [] raw = some value ∧ ¬ doomed (withTables words tables (next value))
  | _, _, _, _ => False

variable [∀ key, SampleableType (R key)]

/-- A fixed residual escapes at a fresh raw answer with probability at most the error of the
occurrence. -/
theorem escapes_le {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error)
    (process : PIR.Proc (committed J Shape Value) A) (tables : List (Table Value)) (event : E) :
    Pr{let raw ← $ᵗ (R [event])}[Escapes absorb words certificate.doomed process tables event raw] ≤
      error event := by
  classical
  have impossible : (∀ raw, ¬ Escapes absorb words certificate.doomed process tables event raw) →
      Pr{let raw ← $ᵗ (R [event])}[
        Escapes absorb words certificate.doomed process tables event raw] ≤ error event :=
    fun never => (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le
  match process with
  | .done _ => exact impossible fun _ escapes => escapes
  | .halt _ => exact impossible fun _ escapes => escapes
  | .call (.commit _) _ => exact impossible fun _ escapes => escapes
  | .call (.read _ _) _ => exact impossible fun _ escapes => escapes
  | .call (.base operation) next =>
      by_cases relevant : ∃ decode, absorb operation = .query event decode ∧
          certificate.doomed (withTables words tables (.call (.base operation) next))
      · obtain ⟨decode, absorbed, doomed⟩ := relevant
        have step := certificate.step _ doomed
        simp only [withTables, Typed.Step, absorbed] at step
        refine (prEvent_mono _ _
          (fun raw => ∃ value, decode [] raw = some value ∧
            ¬ certificate.doomed (withTables words tables (next value)))
          (fun raw escapes => ?_)).trans (step [])
        obtain ⟨decode', absorbed', _, escaping⟩ := escapes
        rw [absorbed] at absorbed'
        obtain ⟨-, same⟩ := Typed.Absorption.query.inj absorbed'
        subst same
        exact escaping
      · exact impossible fun _ escapes => by
          obtain ⟨decode, absorbed, doomed, _⟩ := escapes
          exact relevant ⟨decode, absorbed, doomed⟩

end Escape

end ZkcSecurity.Commitment
