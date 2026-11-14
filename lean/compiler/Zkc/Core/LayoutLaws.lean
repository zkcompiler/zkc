module

public import Zkc.Core.Serialize

public section

/-! The laws of a wire layout: the reader returns what the writer was given, in order.

A `Layout` names rows of a package: one that opens a writer, one per message type that puts
a value on it, one that closes it into the proof, one that opens a reader on the proof, one
per message type that takes a value from it, and one that tests whether it is exhausted.
What the rows compute is the model's choice. This module states, for a model, what the
serialize step needs of them, and derives the one consequence that the step uses.

- `Layout.Written`, `Layout.Takes`: two relations that are defined from the rows alone.
  `Written writer messages final`: putting the messages in order takes the writer to
  `final`. `Takes reader messages final`: taking the messages in order succeeds, with the
  flag `true` and exactly these values, and leaves `final`. `Written` composes and `Takes`
  composes and splits along `++`.
- `Layout.Lawful`: the laws, a hypothesis about the model. A type of wire content with an
  associative append and an empty content that is its unit; an encoding of the values; the
  values that the layout can write (`Writable`); the content of a writer and the reader of a
  content. Each law is about one row: the writer that `start` opens is empty; `put` of a
  writable value appends its encoding; `read` of what `close` makes of a writer is the
  reader of the writer's content; `take` from the reader of the encoding of a writable
  value followed by a content gives `true`, the value and the reader of the content;
  `exhausted` of the reader of the empty content is `true`.
- `Layout.Lawful.round_trip`: from the laws, for messages whose types have the rows
  (`Layout.Carries`) and whose values are writable: what was written from the writer that
  `start` opens is taken, in order, from the reader of the closed writer, which is then
  exhausted.

The laws are assumed, not proved, of any layout here. They are stated in this form because
a canonical layout whose writer, reader and proof are one type of bytes has them with the
identity as the content of a writer and as the reader of a content.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- A message: a value with its type. -/
abbrev Message (model : Model) : Type := (type : Ty) × model.Value type

namespace Layout

variable {operations : List OperationSignature} (layout : Layout operations) (model : Model)

/-- The writer that the `start` row opens. -/
@[expose] def opened : model.Value layout.writer :=
  (model.pure (.of layout.start) layout.writerPopulated .nil).get .here

/-- The writer after a row puts a value on it. -/
@[expose] def putValue {type : Ty}
    (put : Var operations ⟨[layout.writer, type], [layout.writer], .pure⟩)
    (writer : model.Value layout.writer) (value : model.Value type) : model.Value layout.writer :=
  (model.pure (.of put) layout.writerPopulated (.cons writer (.cons value .nil))).get .here

/-- The proof that the `close` row makes of a writer. -/
@[expose] def closed (writer : model.Value layout.writer) : model.Value layout.proof :=
  (model.pure (.of layout.close) layout.proofPopulated (.cons writer .nil)).get .here

/-- The reader that the `read` row opens on a proof. -/
@[expose] def reading (proof : model.Value layout.proof) : model.Value layout.reader :=
  (model.pure (.of layout.read) layout.readerPopulated (.cons proof .nil)).get .here

/-- Whether the `exhausted` row finds a reader exhausted. -/
@[expose] def isExhausted (reader : model.Value layout.reader) : Bool :=
  (model.pure (.of layout.exhausted) rfl (.cons reader .nil)).get .here

/-- The layout has the rows that carry a message of a type: the flag, the value and the
reader that taking returns have values, and a row puts and a row takes a value of the
type. -/
@[expose] def Carries (type : Ty) : Prop :=
  Ty.allPopulated [.bool, type, layout.reader] = true ∧
    (∃ put, layout.put type = some put) ∧ ∃ take, layout.take type = some take

/-- Putting the messages in order takes a writer to another. -/
inductive Written : model.Value layout.writer → List (Message model) →
    model.Value layout.writer → Prop where
  | nil (writer : model.Value layout.writer) : Written writer [] writer
  | cons {type : Ty} {value : model.Value type} {writer final : model.Value layout.writer}
      {rest : List (Message model)}
      (put : Var operations ⟨[layout.writer, type], [layout.writer], .pure⟩)
      (row : layout.put type = some put) :
      Written (layout.putValue model put writer value) rest final →
        Written writer (⟨type, value⟩ :: rest) final

/-- Taking the messages in order succeeds with exactly these values and leaves a reader. -/
inductive Takes : model.Value layout.reader → List (Message model) →
    model.Value layout.reader → Prop where
  | nil (reader : model.Value layout.reader) : Takes reader [] reader
  | cons {type : Ty} {value : model.Value type} {reader middle final : model.Value layout.reader}
      {rest : List (Message model)}
      (take : Var operations ⟨[layout.reader], [.bool, type, layout.reader], .pure⟩)
      (populated : Ty.allPopulated [.bool, type, layout.reader] = true)
      (row : layout.take type = some take)
      (taken : model.pure (.of take) populated (.cons reader .nil) =
        .cons true (.cons value (.cons middle .nil))) :
      Takes middle rest final → Takes reader (⟨type, value⟩ :: rest) final

variable {layout model}

/-- What is written after what was written is written. -/
theorem Written.append {writer middle final : model.Value layout.writer}
    {first second : List (Message model)} (before : layout.Written model writer first middle)
    (after : layout.Written model middle second final) :
    layout.Written model writer (first ++ second) final := by
  induction before with
  | nil writer => exact after
  | cons put row _ ih => exact .cons put row (ih after)

/-- What is taken after what was taken is taken. -/
theorem Takes.append {reader middle final : model.Value layout.reader}
    {first second : List (Message model)} (before : layout.Takes model reader first middle)
    (after : layout.Takes model middle second final) :
    layout.Takes model reader (first ++ second) final := by
  induction before with
  | nil reader => exact after
  | cons take populated row taken _ ih => exact .cons take populated row taken (ih after)

/-- Taking no message leaves the reader as it is. -/
theorem Takes.nil_inv {reader final : model.Value layout.reader}
    (takes : layout.Takes model reader [] final) : final = reader := by
  cases takes
  rfl

/-- Taking messages is taking the first of them and then the others. -/
theorem Takes.split {reader final : model.Value layout.reader} :
    ∀ {first second : List (Message model)}, layout.Takes model reader (first ++ second) final →
      ∃ middle, layout.Takes model reader first middle ∧ layout.Takes model middle second final := by
  intro first
  induction first generalizing reader with
  | nil => exact fun takes => ⟨reader, .nil reader, takes⟩
  | cons message rest ih =>
      intro second takes
      cases takes with
      | cons take populated row taken later =>
          obtain ⟨middle, before, after⟩ := ih later
          exact ⟨middle, .cons take populated row taken before, after⟩

/-- The laws of a layout in a model: the reader returns what the writer was given. -/
structure Lawful (layout : Layout operations) (model : Model) where
  /-- The content of a writer, of a proof and of a reader. -/
  Wire : Type
  /-- The content of a writer on which nothing was put. -/
  empty : Wire
  /-- One content after another. -/
  append : Wire → Wire → Wire
  append_assoc : ∀ first second third, append (append first second) third =
    append first (append second third)
  empty_append : ∀ content, append empty content = content
  append_empty : ∀ content, append content empty = content
  /-- The content that a value of a type is written as. -/
  encode : (type : Ty) → model.Value type → Wire
  /-- The values that the layout can write. -/
  Writable : (type : Ty) → model.Value type → Prop
  /-- What was put on a writer. -/
  ofWriter : model.Value layout.writer → Wire
  /-- The reader that has a content left. -/
  toReader : Wire → model.Value layout.reader
  /-- The writer that `start` opens is empty. -/
  start_empty : ofWriter (layout.opened model) = empty
  /-- `put` of a writable value appends its encoding. -/
  put_appends : ∀ {type : Ty}
    (put : Var operations ⟨[layout.writer, type], [layout.writer], .pure⟩),
    layout.put type = some put → ∀ (value : model.Value type), Writable type value →
      ∀ writer, ofWriter (layout.putValue model put writer value) =
        append (ofWriter writer) (encode type value)
  /-- `read` of what `close` makes of a writer is the reader of the writer's content. -/
  close_read : ∀ writer, layout.reading model (layout.closed model writer) =
    toReader (ofWriter writer)
  /-- `take` from the reader of the encoding of a writable value and a content gives `true`,
  the value and the reader of the content. -/
  take_reads : ∀ {type : Ty}
    (take : Var operations ⟨[layout.reader], [.bool, type, layout.reader], .pure⟩)
    (populated : Ty.allPopulated [.bool, type, layout.reader] = true),
    layout.take type = some take → ∀ (value : model.Value type), Writable type value →
      ∀ rest, model.pure (.of take) populated (.cons (toReader (append (encode type value) rest)) .nil) =
        .cons true (.cons value (.cons (toReader rest) .nil))
  /-- `exhausted` of the reader of the empty content is `true`. -/
  exhausted_empty : layout.isExhausted model (toReader empty) = true

namespace Lawful

variable (laws : layout.Lawful model)

/-- A message that the layout carries: its type has the rows and its value is writable. -/
@[expose] def Sendable (type : Ty) (value : model.Value type) : Prop :=
  layout.Carries type ∧ laws.Writable type value

/-- The content that messages are written as, in order. -/
@[expose] def encodeAll : List (Message model) → laws.Wire
  | [] => laws.empty
  | message :: rest => laws.append (laws.encode message.1 message.2) (encodeAll rest)

/-- What was written is the encodings of the messages after what the writer had. -/
theorem written_content {writer final : model.Value layout.writer}
    {messages : List (Message model)} (written : layout.Written model writer messages final)
    (writable : ∀ message ∈ messages, laws.Writable message.1 message.2) :
    laws.ofWriter final = laws.append (laws.ofWriter writer) (laws.encodeAll messages) := by
  induction written with
  | nil writer => exact (laws.append_empty _).symm
  | cons put row _ ih =>
      rw [ih fun message member => writable message (List.mem_cons_of_mem _ member),
        laws.put_appends put row _ (writable _ List.mem_cons_self), laws.append_assoc]
      rfl

/-- The encodings of messages followed by a content are taken, in order, from its reader,
and leave the reader of the content. -/
theorem takes_content :
    ∀ (messages : List (Message model)),
      (∀ message ∈ messages, laws.Sendable message.1 message.2) →
      ∀ rest : laws.Wire,
        layout.Takes model (laws.toReader (laws.append (laws.encodeAll messages) rest)) messages
          (laws.toReader rest)
  | [], _, rest => by
      show layout.Takes model (laws.toReader (laws.append laws.empty rest)) [] _
      rw [laws.empty_append]
      exact .nil _
  | ⟨type, value⟩ :: messages, sendable, rest => by
      obtain ⟨⟨populated, _, take, row⟩, writable⟩ := sendable ⟨type, value⟩ List.mem_cons_self
      show layout.Takes model
        (laws.toReader (laws.append (laws.append (laws.encode type value) (laws.encodeAll messages))
          rest)) _ _
      rw [laws.append_assoc]
      exact .cons take populated row (laws.take_reads take populated row value writable _)
        (takes_content messages (fun message member =>
          sendable message (List.mem_cons_of_mem _ member)) rest)

/-- The round trip: what was written from the writer that `start` opens is taken, in order,
from the reader that `read` opens on what `close` makes of the final writer, and that
reader is then exhausted. -/
theorem round_trip {messages : List (Message model)} {writer : model.Value layout.writer}
    (sendable : ∀ message ∈ messages, laws.Sendable message.1 message.2)
    (written : layout.Written model (layout.opened model) messages writer) :
    ∃ reader, layout.Takes model (layout.reading model (layout.closed model writer)) messages
        reader ∧ layout.isExhausted model reader = true := by
  refine ⟨laws.toReader laws.empty, ?_, laws.exhausted_empty⟩
  have content := laws.written_content written fun message member => (sendable message member).2
  rw [laws.start_empty, laws.empty_append] at content
  rw [laws.close_read, content]
  have takes := laws.takes_content messages sendable laws.empty
  rw [laws.append_empty] at takes
  exact takes

end Lawful

end Layout

end Zkc.Core
