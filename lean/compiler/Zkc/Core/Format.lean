module

@[expose] public section

/-! Formats: one description of how a kind of value is written gives its writer, its reader,
its width and its laws.

A format of a type states the values it writes (its domain), writes a value as bytes, reads a
value from the front of bytes and gives the bytes after it, and states the width of its values
when they all have one. Its two laws (`Format.Lawful`):

- *round trip of a prefix:* for a value of the domain and any bytes after it, reading what the
  writer wrote followed by those bytes gives the value and those bytes;
- *canonical:* when reading bytes gives a value and the bytes after it, the value is of the
  domain and the bytes are what the writer writes for it, followed by the bytes after it.

So a writer is injective on its domain, no two values of the domain are written as bytes of
which one is a prefix of the other, and a reader accepts exactly the bytes that the writer
writes. A value outside the domain has no bytes that the laws speak of.

A format states also what a caller checks of a value before it writes it (`admits`). Every
value of the domain is admitted, and the check is the domain itself wherever the domain is
cheap to decide. Where it is not, the check is a part of it, and the reader decides the rest:
a value that is admitted and not of the domain is written as bytes that the reader, which
gives only values of the domain, does not read as that value.

The reader of a format is the mathematical one: a collection reads as many elements as its
count, of whatever width. A format has a second reader, under a limit on the number of elements
of collections that it builds (`readWithin`); it gives a value with what is left of the limit, a
refusal, or the limit. Whenever it answers, it gives what the reader gives (`Format.Agrees`).

The combinators, each with its laws proved once: a pair, a value of each format of a list (a
tuple), a repetition of a fixed count, a repetition after its count, a refinement, and a format
seen through a view of another type. The formats of numbers are in `Zkc.Core.FormatNumbers`.
-/

set_option autoImplicit false

namespace Zkc.Core

/-- A byte: a number below 256. -/
abbrev Byte : Type := Fin 256

/-- Bytes, in the order written. -/
abbrev Bytes : Type := List Byte

/-- The byte of a number: its residue modulo 256. -/
def Byte.ofNat (value : Nat) : Byte := ⟨value % 256, Nat.mod_lt _ (by decide)⟩

theorem Byte.ofNat_val (byte : Byte) : Byte.ofNat byte.val = byte :=
  Fin.ext (Nat.mod_eq_of_lt byte.isLt)

theorem Byte.val_ofNat (value : Nat) : (Byte.ofNat value).val = value % 256 := rfl

/-- What a reader under a limit gives: a value, the bytes after it and what is left of the
limit; a refusal; or the limit, when the bytes ask for more elements than it allows. -/
inductive Reading (α : Type) where
  | found (value : α) (rest : Bytes) (left : Nat)
  | refused
  | limit

namespace Reading

variable {α β : Type}

/-- A reading and then another, on the bytes after it and with what is left of the limit. -/
def andThen : Reading α → (α → Bytes → Nat → Reading β) → Reading β
  | .found value rest left, next => next value rest left
  | .refused, _ => .refused
  | .limit, _ => .limit

/-- The reading of a reader that builds no element of a collection. -/
def ofOption (limit : Nat) : Option (α × Bytes) → Reading α
  | some (value, rest) => .found value rest limit
  | none => .refused

/-- What a reading answers, when it does: a value and the bytes after it, or a refusal. The
limit is no answer. -/
def answer : Reading α → Option (Option (α × Bytes))
  | .found value rest _ => some (some (value, rest))
  | .refused => some none
  | .limit => none

theorem answer_ofOption (limit : Nat) (result : Option (α × Bytes)) :
    (ofOption limit result).answer = some result := by
  match result with
  | some (_, _) => rfl
  | none => rfl

end Reading

/-- A format of the values of a type. -/
structure Format (α : Type) where
  /-- Whether the format writes a value: the values it writes are its domain. -/
  domain : α → Bool
  /-- What a caller checks of a value before it writes it: every value of the domain passes. -/
  admits : α → Bool
  /-- The bytes of a value of the domain. -/
  write : α → Bytes
  /-- The value at the front of bytes and the bytes after it, when they start with the bytes of
  a value of the domain. -/
  read : Bytes → Option (α × Bytes)
  /-- The number of bytes of every value of the domain, when they all have one. -/
  width : Option Nat
  /-- The reader under a limit on the number of elements of collections that it builds. -/
  readWithin : Nat → Bytes → Reading α

namespace Format

variable {α β : Type}

/-- The laws of a format: the round trip of a prefix, that the reader accepts only what the
writer writes, and that a stated width is the width of every value of the domain. -/
structure Lawful (format : Format α) : Prop where
  round_trip : ∀ value, format.domain value = true → ∀ rest,
    format.read (format.write value ++ rest) = some (value, rest)
  canonical : ∀ bytes value rest, format.read bytes = some (value, rest) →
    format.domain value = true ∧ bytes = format.write value ++ rest
  width_written : ∀ width, format.width = some width → ∀ value, format.domain value = true →
    (format.write value).length = width
  admits_domain : ∀ value, format.domain value = true → format.admits value = true

/-- The reader under a limit agrees with the reader: whenever it answers, with a value or with
a refusal, the reader gives that answer. -/
def Agrees (format : Format α) : Prop :=
  ∀ limit bytes result, (format.readWithin limit bytes).answer = some result →
    format.read bytes = result

/-- A reader of a lawful format reads what the writer wrote, with nothing after it. -/
theorem Lawful.reads_written {format : Format α} (lawful : format.Lawful) {value : α}
    (inDomain : format.domain value = true) : format.read (format.write value) = some (value, []) := by
  have read := lawful.round_trip value inDomain []
  rwa [List.append_nil] at read

/-- No two values of the domain of a lawful format are written as bytes of which one is a prefix
of the other: values with the same bytes, whatever follows each, are one value, followed by the
same bytes. -/
theorem Lawful.prefix_free {format : Format α} (lawful : format.Lawful) {first second : α}
    (firstIn : format.domain first = true) (secondIn : format.domain second = true)
    {afterFirst afterSecond : Bytes}
    (same : format.write first ++ afterFirst = format.write second ++ afterSecond) :
    first = second ∧ afterFirst = afterSecond := by
  have readFirst := lawful.round_trip first firstIn afterFirst
  rw [same, lawful.round_trip second secondIn afterSecond] at readFirst
  cases readFirst
  exact ⟨rfl, rfl⟩

/-- The writer of a lawful format is injective on its domain. -/
theorem Lawful.write_injective {format : Format α} (lawful : format.Lawful) {first second : α}
    (firstIn : format.domain first = true) (secondIn : format.domain second = true)
    (same : format.write first = format.write second) : first = second :=
  (lawful.prefix_free firstIn secondIn (afterFirst := []) (afterSecond := [])
    (by rw [same])).1

/-! ## A pair -/

/-- A value of one format and then a value of another. -/
def pair (first : Format α) (second : Format β) : Format (α × β) where
  domain value := first.domain value.1 && second.domain value.2
  admits value := first.admits value.1 && second.admits value.2
  write value := first.write value.1 ++ second.write value.2
  read bytes :=
    match first.read bytes with
    | none => none
    | some (head, rest) =>
      match second.read rest with
      | none => none
      | some (tail, rest) => some ((head, tail), rest)
  width :=
    match first.width, second.width with
    | some head, some tail => some (head + tail)
    | _, _ => none
  readWithin limit bytes :=
    (first.readWithin limit bytes).andThen fun head rest left =>
      (second.readWithin left rest).andThen fun tail rest left => .found (head, tail) rest left

theorem pair_lawful {first : Format α} {second : Format β} (firstLawful : first.Lawful)
    (secondLawful : second.Lawful) : (first.pair second).Lawful where
  round_trip := by
    intro (head, tail) inDomain rest
    simp only [pair, Bool.and_eq_true] at inDomain ⊢
    rw [List.append_assoc, firstLawful.round_trip head inDomain.1]
    simp only
    rw [secondLawful.round_trip tail inDomain.2]
  canonical := by
    intro bytes (head, tail) rest read
    simp only [pair] at read ⊢
    cases readHead : first.read bytes with
    | none => simp [readHead] at read
    | some found =>
      obtain ⟨foundHead, afterHead⟩ := found
      simp only [readHead] at read
      cases readTail : second.read afterHead with
      | none => simp [readTail] at read
      | some found =>
        obtain ⟨foundTail, afterTail⟩ := found
        simp only [readTail, Option.some.injEq, Prod.mk.injEq] at read
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := read
        obtain ⟨headIn, rfl⟩ := firstLawful.canonical _ _ _ readHead
        obtain ⟨tailIn, rfl⟩ := secondLawful.canonical _ _ _ readTail
        exact ⟨by simp [headIn, tailIn], by rw [List.append_assoc]⟩
  width_written := by
    intro width stated (head, tail) inDomain
    simp only [pair, Bool.and_eq_true] at stated inDomain ⊢
    cases headWidth : first.width with
    | none => simp [headWidth] at stated
    | some headWidth' =>
      cases tailWidth : second.width with
      | none => simp [headWidth, tailWidth] at stated
      | some tailWidth' =>
        simp only [headWidth, tailWidth, Option.some.injEq] at stated
        rw [List.length_append, firstLawful.width_written _ headWidth head inDomain.1,
          secondLawful.width_written _ tailWidth tail inDomain.2, stated]
  admits_domain := by
    intro (head, tail) inDomain
    simp only [pair, Bool.and_eq_true] at inDomain ⊢
    exact ⟨firstLawful.admits_domain head inDomain.1, secondLawful.admits_domain tail inDomain.2⟩

theorem pair_agrees {first : Format α} {second : Format β} (firstAgrees : first.Agrees)
    (secondAgrees : second.Agrees) : (first.pair second).Agrees := by
  intro limit bytes result answered
  simp only [pair] at answered ⊢
  cases readHead : first.readWithin limit bytes with
  | limit => simp [readHead, Reading.andThen, Reading.answer] at answered
  | refused =>
    simp only [readHead, Reading.andThen, Reading.answer, Option.some.injEq] at answered
    rw [firstAgrees limit bytes none (by rw [readHead]; rfl)]
    exact answered
  | found head afterHead left =>
    rw [firstAgrees limit bytes (some (head, afterHead)) (by rw [readHead]; rfl)]
    simp only [readHead, Reading.andThen] at answered ⊢
    cases readTail : second.readWithin left afterHead with
    | limit => simp [readTail, Reading.answer] at answered
    | refused =>
      simp only [readTail, Reading.answer, Option.some.injEq] at answered
      rw [secondAgrees left afterHead none (by rw [readTail]; rfl)]
      exact answered
    | found tail afterTail left' =>
      rw [secondAgrees left afterHead (some (tail, afterTail)) (by rw [readTail]; rfl)]
      simp only [readTail, Reading.answer, Option.some.injEq] at answered
      exact answered

/-! ## A view -/

/-- A format seen through a view of another type: a value of the other type is written as the
value that the view reads from it, and a value read is the image of the value of the format. -/
def through (format : Format α) (image : α → β) (view : β → Option α) : Format β where
  domain value :=
    match view value with
    | some inner => format.domain inner
    | none => false
  admits value :=
    match view value with
    | some inner => format.admits inner
    | none => false
  write value :=
    match view value with
    | some inner => format.write inner
    | none => []
  read bytes :=
    match format.read bytes with
    | some (inner, rest) => some (image inner, rest)
    | none => none
  width := format.width
  readWithin limit bytes :=
    (format.readWithin limit bytes).andThen fun inner rest left => .found (image inner) rest left

/-- A view that reads back the value of every image, and whose values are images. -/
structure Views (image : α → β) (view : β → Option α) : Prop where
  view_image : ∀ inner, view (image inner) = some inner
  image_view : ∀ value inner, view value = some inner → image inner = value

theorem through_lawful {format : Format α} {image : α → β} {view : β → Option α}
    (lawful : format.Lawful) (views : Views image view) : (format.through image view).Lawful where
  round_trip := by
    intro value inDomain rest
    simp only [through] at inDomain ⊢
    cases viewed : view value with
    | none => simp [viewed] at inDomain
    | some inner =>
      simp only [viewed] at inDomain ⊢
      rw [lawful.round_trip inner inDomain]
      simp only
      rw [views.image_view value inner viewed]
  canonical := by
    intro bytes value rest read
    simp only [through] at read ⊢
    cases readInner : format.read bytes with
    | none => simp [readInner] at read
    | some found =>
      obtain ⟨inner, after⟩ := found
      simp only [readInner, Option.some.injEq, Prod.mk.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      obtain ⟨innerIn, rfl⟩ := lawful.canonical _ _ _ readInner
      simp only [views.view_image]
      exact ⟨innerIn, trivial⟩
  width_written := by
    intro width stated value inDomain
    simp only [through] at stated inDomain ⊢
    cases viewed : view value with
    | none => simp [viewed] at inDomain
    | some inner =>
      simp only [viewed] at inDomain ⊢
      exact lawful.width_written width stated inner inDomain
  admits_domain := by
    intro value inDomain
    simp only [through] at inDomain ⊢
    cases viewed : view value with
    | none => simp [viewed] at inDomain
    | some inner =>
      simp only [viewed] at inDomain ⊢
      exact lawful.admits_domain inner inDomain

theorem through_agrees {format : Format α} {image : α → β} {view : β → Option α}
    (agrees : format.Agrees) : (format.through image view).Agrees := by
  intro limit bytes result answered
  simp only [through] at answered ⊢
  cases readInner : format.readWithin limit bytes with
  | limit => simp [readInner, Reading.andThen, Reading.answer] at answered
  | refused =>
    simp only [readInner, Reading.andThen, Reading.answer, Option.some.injEq] at answered
    rw [agrees limit bytes none (by rw [readInner]; rfl)]
    exact answered
  | found inner after left =>
    rw [agrees limit bytes (some (inner, after)) (by rw [readInner]; rfl)]
    simp only [readInner, Reading.andThen, Reading.answer, Option.some.injEq] at answered
    exact answered

/-! ## A refinement -/

/-- The values of a format that a condition keeps: the reader refuses the others. -/
def refine (format : Format α) (keep : α → Bool) : Format α where
  domain value := format.domain value && keep value
  admits value := format.admits value && keep value
  write := format.write
  read bytes :=
    match format.read bytes with
    | some (value, rest) => if keep value then some (value, rest) else none
    | none => none
  width := format.width
  readWithin limit bytes :=
    (format.readWithin limit bytes).andThen fun value rest left =>
      if keep value then .found value rest left else .refused

theorem refine_lawful {format : Format α} (lawful : format.Lawful) (keep : α → Bool) :
    (format.refine keep).Lawful where
  round_trip := by
    intro value inDomain rest
    simp only [refine, Bool.and_eq_true] at inDomain ⊢
    rw [lawful.round_trip value inDomain.1]
    simp [inDomain.2]
  canonical := by
    intro bytes value rest read
    simp only [refine] at read ⊢
    cases readInner : format.read bytes with
    | none => simp [readInner] at read
    | some found =>
      obtain ⟨inner, after⟩ := found
      simp only [readInner] at read
      cases kept : keep inner with
      | false => simp [kept] at read
      | true =>
        simp only [kept, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at read
        obtain ⟨rfl, rfl⟩ := read
        obtain ⟨innerIn, rfl⟩ := lawful.canonical _ _ _ readInner
        exact ⟨by simp [innerIn, kept], rfl⟩
  width_written := by
    intro width stated value inDomain
    simp only [refine, Bool.and_eq_true] at stated inDomain ⊢
    exact lawful.width_written width stated value inDomain.1
  admits_domain := by
    intro value inDomain
    simp only [refine, Bool.and_eq_true] at inDomain ⊢
    exact ⟨lawful.admits_domain value inDomain.1, inDomain.2⟩

theorem refine_agrees {format : Format α} (agrees : format.Agrees) (keep : α → Bool) :
    (format.refine keep).Agrees := by
  intro limit bytes result answered
  simp only [refine] at answered ⊢
  cases readInner : format.readWithin limit bytes with
  | limit => simp [readInner, Reading.andThen, Reading.answer] at answered
  | refused =>
    simp only [readInner, Reading.andThen, Reading.answer, Option.some.injEq] at answered
    rw [agrees limit bytes none (by rw [readInner]; rfl)]
    exact answered
  | found inner after left =>
    rw [agrees limit bytes (some (inner, after)) (by rw [readInner]; rfl)]
    simp only [readInner, Reading.andThen] at answered ⊢
    cases kept : keep inner with
    | false => simpa [kept, Reading.answer] using answered
    | true => simpa [kept, Reading.answer] using answered

/-! ## A value of each format of a list -/

/-- No value, in no bytes. -/
def nothing : Format (List α) where
  domain values := values.isEmpty
  admits values := values.isEmpty
  write _ := []
  read bytes := some ([], bytes)
  width := some 0
  readWithin limit bytes := .found [] bytes limit

theorem nothing_lawful : (nothing : Format (List α)).Lawful where
  round_trip := by
    intro values inDomain rest
    simp only [nothing, List.isEmpty_iff] at inDomain ⊢
    rw [inDomain]
    rfl
  canonical := by
    intro bytes values rest read
    simp only [nothing, Option.some.injEq, Prod.mk.injEq] at read ⊢
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨rfl, rfl⟩
  width_written := by
    intro width stated values _
    simp only [nothing, Option.some.injEq] at stated ⊢
    rw [← stated]
    rfl
  admits_domain := fun _ inDomain => inDomain

theorem nothing_agrees : (nothing : Format (List α)).Agrees := by
  intro limit bytes result answered
  simp only [nothing, Reading.answer, Option.some.injEq] at answered ⊢
  exact answered

/-- The first value of a list and the values after it. -/
def uncons : List α → Option (α × List α)
  | [] => none
  | head :: tail => some (head, tail)

theorem views_cons : Views (fun (parts : α × List α) => parts.1 :: parts.2) uncons where
  view_image := fun _ => rfl
  image_view := by
    intro value inner viewed
    match value, viewed with
    | head :: tail, viewed =>
      cases viewed
      rfl

/-- A value of each format of a list, in order: a tuple. A list of other than as many values as
there are formats is not of the domain. -/
def each : List (Format α) → Format (List α)
  | [] => nothing
  | format :: rest => (format.pair (each rest)).through (fun parts => parts.1 :: parts.2) uncons

theorem each_lawful : ∀ {formats : List (Format α)}, (∀ format ∈ formats, format.Lawful) →
    (each formats).Lawful
  | [], _ => nothing_lawful
  | format :: _, lawful =>
    through_lawful
      (pair_lawful (lawful format (List.mem_cons_self ..))
        (each_lawful fun other member => lawful other (List.mem_cons_of_mem _ member)))
      views_cons

theorem each_agrees : ∀ {formats : List (Format α)}, (∀ format ∈ formats, format.Agrees) →
    (each formats).Agrees
  | [], _ => nothing_agrees
  | format :: _, agrees =>
    through_agrees
      (pair_agrees (agrees format (List.mem_cons_self ..))
        (each_agrees fun other member => agrees other (List.mem_cons_of_mem _ member)))

/-! ## A repetition -/

/-- `count` values in order, after those read so far, latest first. The recursion keeps what it
has read in an argument, so that a long repetition does not grow the stack. -/
def readMany (read : Bytes → Option (α × Bytes)) : Nat → List α → Bytes → Option (List α × Bytes)
  | 0, done, bytes => some (done.reverse, bytes)
  | count + 1, done, bytes =>
    match read bytes with
    | none => none
    | some (item, rest) => readMany read count (item :: done) rest

/-- `count` values in order under a limit: each value read takes one from the limit, and the
limit is reached when a value is still to be read and nothing is left of it. -/
def readManyWithin (readWithin : Nat → Bytes → Reading α) :
    Nat → List α → Nat → Bytes → Reading (List α)
  | 0, done, limit, bytes => .found done.reverse bytes limit
  | _ + 1, _, 0, _ => .limit
  | count + 1, done, limit + 1, bytes =>
    match readWithin limit bytes with
    | .found item rest left => readManyWithin readWithin count (item :: done) left rest
    | .refused => .refused
    | .limit => .limit

/-- The values read after those read so far are the values read from nothing, after them. -/
theorem readMany_done (read : Bytes → Option (α × Bytes)) :
    ∀ (count : Nat) (done : List α) (bytes : Bytes),
      readMany read count done bytes =
        (readMany read count [] bytes).map fun found => (done.reverse ++ found.1, found.2)
  | 0, done, bytes => by simp [readMany]
  | count + 1, done, bytes => by
    simp only [readMany]
    cases read bytes with
    | none => rfl
    | some found =>
      obtain ⟨item, rest⟩ := found
      simp only
      rw [readMany_done read count (item :: done) rest, readMany_done read count [item] rest]
      cases readMany read count [] rest with
      | none => rfl
      | some found => simp

/-- One more value than `count`: a value, and then `count` values. -/
theorem readMany_succ (read : Bytes → Option (α × Bytes)) (count : Nat) (bytes : Bytes) :
    readMany read (count + 1) [] bytes =
      match read bytes with
      | none => none
      | some (item, rest) =>
        (readMany read count [] rest).map fun found => (item :: found.1, found.2) := by
  simp only [readMany]
  cases read bytes with
  | none => rfl
  | some found =>
    obtain ⟨item, rest⟩ := found
    simp only
    rw [readMany_done read count [item] rest]
    cases readMany read count [] rest with
    | none => rfl
    | some found => simp

/-- The reader of a lawful format reads the values that its writer wrote one after another. -/
theorem readMany_written {format : Format α} (lawful : format.Lawful) :
    ∀ (values : List α), (values.all format.domain = true) → ∀ rest,
      readMany format.read values.length [] (values.flatMap format.write ++ rest) =
        some (values, rest)
  | [], _, rest => rfl
  | value :: values, inDomain, rest => by
    simp only [List.all_cons, Bool.and_eq_true] at inDomain
    rw [List.length_cons, readMany_succ, List.flatMap_cons, List.append_assoc,
      lawful.round_trip value inDomain.1]
    simp only
    rw [readMany_written lawful values inDomain.2 rest]
    rfl

/-- What the reader of a lawful format reads one after another is what its writer writes. -/
theorem readMany_canonical {format : Format α} (lawful : format.Lawful) :
    ∀ (count : Nat) (bytes : Bytes) (values : List α) (rest : Bytes),
      readMany format.read count [] bytes = some (values, rest) →
        values.length = count ∧ values.all format.domain = true ∧
          bytes = values.flatMap format.write ++ rest
  | 0, bytes, values, rest, read => by
    simp only [readMany, List.reverse_nil, Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨rfl, rfl, rfl⟩
  | count + 1, bytes, values, rest, read => by
    rw [readMany_succ] at read
    cases readItem : format.read bytes with
    | none => simp [readItem] at read
    | some found =>
      obtain ⟨item, after⟩ := found
      simp only [readItem] at read
      cases readRest : readMany format.read count [] after with
      | none => simp [readRest] at read
      | some found =>
        obtain ⟨items, afterAll⟩ := found
        simp only [readRest, Option.map_some, Option.some.injEq, Prod.mk.injEq] at read
        obtain ⟨rfl, rfl⟩ := read
        obtain ⟨itemIn, rfl⟩ := lawful.canonical _ _ _ readItem
        obtain ⟨length, itemsIn, rfl⟩ := readMany_canonical lawful count _ _ _ readRest
        refine ⟨by simp [length], by simp [itemIn, itemsIn], ?_⟩
        rw [List.flatMap_cons, List.append_assoc]

/-- The repetition under a limit agrees with the repetition whenever it answers. -/
theorem readManyWithin_agrees {format : Format α} (agrees : format.Agrees) :
    ∀ (count : Nat) (done : List α) (limit : Nat) (bytes : Bytes)
      (result : Option (List α × Bytes)),
      (readManyWithin format.readWithin count done limit bytes).answer = some result →
        readMany format.read count done bytes = result
  | 0, done, limit, bytes, result, answered => by
    simp only [readManyWithin, Reading.answer, Option.some.injEq] at answered
    simpa [readMany] using answered
  | count + 1, done, 0, bytes, result, answered => by
    simp [readManyWithin, Reading.answer] at answered
  | count + 1, done, limit + 1, bytes, result, answered => by
    simp only [readManyWithin] at answered
    simp only [readMany]
    cases readItem : format.readWithin limit bytes with
    | limit => simp [readItem, Reading.answer] at answered
    | refused =>
      simp only [readItem, Reading.answer, Option.some.injEq] at answered
      rw [agrees limit bytes none (by rw [readItem]; rfl)]
      exact answered
    | found item rest left =>
      rw [agrees limit bytes (some (item, rest)) (by rw [readItem]; rfl)]
      simp only [readItem] at answered ⊢
      exact readManyWithin_agrees agrees count (item :: done) left rest result answered

/-- A repetition of a fixed count: as many values as the count, one after another. Each value
read takes one from the limit. -/
def repeated (count : Nat) (element : Format α) : Format (List α) where
  domain values := values.length == count && values.all element.domain
  admits values := values.length == count && values.all element.admits
  write values := values.flatMap element.write
  read bytes := readMany element.read count [] bytes
  width := element.width.map (count * ·)
  readWithin limit bytes := readManyWithin element.readWithin count [] limit bytes

/-- Values of the domain of a lawful format, each admitted. -/
theorem all_admits {format : Format α} (lawful : format.Lawful) {values : List α}
    (inDomain : values.all format.domain = true) : values.all format.admits = true := by
  rw [List.all_eq_true] at inDomain ⊢
  exact fun value member => lawful.admits_domain value (inDomain value member)

/-- The bytes of values of one width, one after another. -/
theorem flatMap_width {format : Format α} (lawful : format.Lawful) {width : Nat}
    (stated : format.width = some width) :
    ∀ (values : List α), values.all format.domain = true →
      (values.flatMap format.write).length = values.length * width
  | [], _ => by simp
  | value :: values, inDomain => by
    simp only [List.all_cons, Bool.and_eq_true] at inDomain
    rw [List.flatMap_cons, List.length_append, lawful.width_written width stated value inDomain.1,
      flatMap_width lawful stated values inDomain.2, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem repeated_lawful (count : Nat) {element : Format α} (lawful : element.Lawful) :
    (repeated count element).Lawful where
  round_trip := by
    intro values inDomain rest
    simp only [repeated, Bool.and_eq_true, beq_iff_eq] at inDomain ⊢
    rw [← inDomain.1]
    exact readMany_written lawful values inDomain.2 rest
  canonical := by
    intro bytes values rest read
    simp only [repeated] at read ⊢
    obtain ⟨length, inDomain, written⟩ := readMany_canonical lawful count bytes values rest read
    exact ⟨by simp [length, inDomain], written⟩
  width_written := by
    intro width stated values inDomain
    simp only [repeated, Bool.and_eq_true, beq_iff_eq] at stated inDomain ⊢
    cases elementWidth : element.width with
    | none => simp [elementWidth] at stated
    | some each =>
      simp only [elementWidth, Option.map_some, Option.some.injEq] at stated
      rw [flatMap_width lawful elementWidth values inDomain.2, inDomain.1, stated]
  admits_domain := by
    intro values inDomain
    simp only [repeated, Bool.and_eq_true, beq_iff_eq] at inDomain ⊢
    exact ⟨inDomain.1, all_admits lawful inDomain.2⟩

theorem repeated_agrees (count : Nat) {element : Format α} (agrees : element.Agrees) :
    (repeated count element).Agrees := by
  intro limit bytes result answered
  exact readManyWithin_agrees agrees count [] limit bytes result answered

/-- A repetition after its count: the number of values in a format of numbers, and then the
values, one after another. Each value read takes one from the limit. -/
def counted (length : Format Nat) (element : Format α) : Format (List α) where
  domain values := length.domain values.length && values.all element.domain
  admits values := length.admits values.length && values.all element.admits
  write values := length.write values.length ++ values.flatMap element.write
  read bytes :=
    match length.read bytes with
    | none => none
    | some (count, rest) => readMany element.read count [] rest
  width := none
  readWithin limit bytes :=
    (length.readWithin limit bytes).andThen fun count rest left =>
      readManyWithin element.readWithin count [] left rest

theorem counted_lawful {length : Format Nat} {element : Format α} (lengthLawful : length.Lawful)
    (lawful : element.Lawful) : (counted length element).Lawful where
  round_trip := by
    intro values inDomain rest
    simp only [counted, Bool.and_eq_true] at inDomain ⊢
    rw [List.append_assoc, lengthLawful.round_trip values.length inDomain.1]
    exact readMany_written lawful values inDomain.2 rest
  canonical := by
    intro bytes values rest read
    simp only [counted] at read ⊢
    cases readLength : length.read bytes with
    | none => simp [readLength] at read
    | some found =>
      obtain ⟨count, after⟩ := found
      simp only [readLength] at read
      obtain ⟨countIn, rfl⟩ := lengthLawful.canonical _ _ _ readLength
      obtain ⟨sameLength, inDomain, rfl⟩ := readMany_canonical lawful count _ _ _ read
      rw [sameLength]
      exact ⟨by simp [countIn, inDomain], by rw [List.append_assoc]⟩
  width_written := by
    intro width stated
    simp [counted] at stated
  admits_domain := by
    intro values inDomain
    simp only [counted, Bool.and_eq_true] at inDomain ⊢
    exact ⟨lengthLawful.admits_domain _ inDomain.1, all_admits lawful inDomain.2⟩

theorem counted_agrees {length : Format Nat} {element : Format α} (lengthAgrees : length.Agrees)
    (agrees : element.Agrees) : (counted length element).Agrees := by
  intro limit bytes result answered
  simp only [counted] at answered ⊢
  cases readLength : length.readWithin limit bytes with
  | limit => simp [readLength, Reading.andThen, Reading.answer] at answered
  | refused =>
    simp only [readLength, Reading.andThen, Reading.answer, Option.some.injEq] at answered
    rw [lengthAgrees limit bytes none (by rw [readLength]; rfl)]
    exact answered
  | found count after left =>
    rw [lengthAgrees limit bytes (some (count, after)) (by rw [readLength]; rfl)]
    simp only [readLength, Reading.andThen] at answered ⊢
    exact readManyWithin_agrees agrees count [] left after result answered

end Format

end Zkc.Core
