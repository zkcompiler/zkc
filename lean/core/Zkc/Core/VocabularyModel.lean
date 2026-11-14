module

public import Zkc.Core.CanonicalLayout
public import Zkc.Core.DecodingLimit
public import Zkc.Core.Merlin
public import Zkc.Core.Elaborate

public section

/-! The executor's model of the rows of the vocabulary, and the running of a function.

Every nominal type has the carrier of plain data (`Concrete.Datum`). What a row computes is
read from the vocabulary's entry for its type, never from its name alone:

- a type whose arithmetic is a prime field is the naturals below its `Order`: one
  implementation for `koala-bear` and `bls12-381.fr`, an element a number;
- an extension is the polynomials over its `Base`, a prime field, modulo
  `x^Degree - nonresidue`: an element is its `Degree` coefficients, lowest first;
- `bls12-381.g1` is the group of `Concrete`: a point is its two coordinates, or no datum for
  the point at infinity; its scalar acts by its natural below the order;
- `nonzero<F>` has the data of `F`;
- a collection row is the fold of the row of its elements; the function members of the sorts
  are the views of an element that their names say; `field.root` is a power of the generator
  of the two-adic subgroup that the entry gives; `hash.sha256` is SHA-256;
- the rows of the layout `zkc::layout::canonical` that put and take a value of a type are the
  writer and the reader of the format of the type (`formatOf` of `Zkc.Core.CanonicalLayout`): a
  writer, a reader and a proof are bytes; `put` appends the bytes of the value, and `take` gives
  the flag `true`, the value at the front of the reader and the bytes after it, or the flag
  `false`, a value of the type and the reader unchanged. A reader given what the writer wrote for
  a value, followed by anything, gives the value and what follows (`takeRow_written`);
- the rows of the suite `suite.merlin3.bls12-381.fr64be/0` are a Merlin 1.0 transcript
  (`Zkc.Core.Merlin`), whose datum is its 203 numbers; a value is absorbed as the bytes that the
  format of its type writes for it, so a proof's bytes are the bytes absorbed (`absorbRow`).

A row whose type has no implementation, or that the model does not implement (`field.root`
of a type without a generator, the hashes other than SHA-256, a suite's `derive` at a law
other than its challenge field), is missing: a run of a package that applies one stops before it
starts, with a message that names the row. A row that writes or reads values of a type in the
canonical layout is implemented exactly when the type has a format, which is decided of the
type and not by applying the row.

A run takes a limit on the number of elements of collections that one reading of a value builds
(`run`, `defaultLimit`). Under it the row that takes a value reads with the reader under the
limit, which agrees with the reader whenever it answers (`takeRow_within`). A run that reaches
the limit ends with the limit (`Run.limit`): the function did not return, and it did not stop.
The functions that a run runs are those of the meaning under the model, cut where a reading
reaches the limit (`limitedFunctions_within`). The programs of roles, a verifier that reads a
proof among them, run under the same limit in `Zkc.Core.VocabularyExecute`.

A row of a package is compared with the vocabulary (`mismatch`): its name and its static
arguments name a row of the vocabulary, and its kind, its domain row, its inputs and its outputs
are those that the vocabulary gives that row. The vocabulary admits a package when every row is
the vocabulary's and the model implements it (`missing` is empty).

The restricted row `field.nonzero` has a value exactly where its domain row `field.is_nonzero`
gives `true`, and it is the one restricted row of the vocabulary. So the model satisfies the
domain laws of the operation table of every package that the core elaborates and whose rows are
the vocabulary's (`model_domainLaws`).
-/

set_option autoImplicit false

namespace Zkc.Core.Vocabulary

open Zkc.Source
open Zkc.Core.Concrete (Datum)

/-! ## Rows -/

/-- Why a row has no value. -/
inductive Failure where
  /-- Outside the domain of a row: of a restricted row, or a datum that the format of the type
  at which a row of the layout writes does not admit. -/
  | outside
  /-- The model does not implement the row at these static arguments. -/
  | missing (message : String)
  /-- The row reached the limit on the number of elements that a reader builds. -/
  | limit (elements : Nat)
  deriving Repr, Inhabited

def describe (name : String) (arguments : List Value) : String :=
  let shown := arguments.map fun
    | .type type => reprStr type
    | .natural value => toString value
  if shown.isEmpty then s!"`{name}`" else s!"`{name}` at {", ".intercalate shown}"

/-- The failure of a row that the model does not implement at its static arguments. -/
def Failure.noImplementation (name : String) (arguments : List Value) : Failure :=
  .missing s!"the row {describe name arguments} has no implementation in the model"

/-- The static argument of a row that is a type, at a position. -/
@[expose] def typeArgument (arguments : List Value) (position : Nat) : Option Closed :=
  match arguments[position]? with
  | some (.type type) => some type
  | _ => none

/-- What a row computes on data. -/
@[expose] def apply (table : Table) (name : String) (arguments : List Value) (inputs : List Datum) :
    Except Failure (List Datum) := do
  let missing {α : Type} : Except Failure α := .error (.noImplementation name arguments)
  let elementAt (position : Nat) : Except Failure Element :=
    match (typeArgument arguments position).bind (elementOf table) with
    | some element => .ok element
    | none => missing
  let element ← elementAt 0
  -- the restricted row and its domain row: `field.nonzero` has a value exactly where
  -- `field.is_nonzero` gives `true`
  if name = "field.nonzero" then
    match inputs with
    | [a] => if element.isZero a then .error .outside else return [a]
    | _ => missing
  else if name = "field.is_nonzero" then
    match inputs with
    | [a] => return [Datum.ofBool (!element.isZero a)]
    | _ => missing
  else
  match name, inputs with
  | "field.add", [a, b] | "group.add", [a, b] => return [element.add a b]
  | "field.sub", [a, b] | "group.sub", [a, b] => return [element.sub a b]
  | "field.mul", [a, b] | "ring.mul", [a, b] => return [element.mul a b]
  | "field.neg", [a] | "group.neg", [a] => return [element.neg a]
  | "field.pow", [a, n] | "ring.pow", [a, n] => return [element.pow a n.toNat]
  | "field.inverse", [a] => return [element.inverse a]
  | "field.equal", [a, b] | "group.equal", [a, b] => return [Datum.ofBool (element.equal a b)]
  | "field.from_nonzero", [a] => return [a]
  | "group.zero", [] => return [element.zero]
  | "group.scale", [a, s] => return [element.scale a s]
  | "group.generator", [] =>
    if element == .curve then return [Datum.ofPoint Concrete.generator] else missing
  | "field.from_nat", [n] => return [element.ofNat n.toNat]
  | "field.to_nat", [a] =>
    match element with
    | .prime _ => return [a]
    | _ => missing
  | "field.components", [a] | "field.coefficients", [a] =>
    match element with
    | .prime _ => return [.sequence [a]]
    | .extension _ degree _ => return [Extension.ofCoefficients (Extension.coefficients degree a)]
    | .curve => missing
  | "field.from_components", [c] | "field.from_coefficients", [c] =>
    match element with
    | .prime _ => return [c.items.headD (.number 0)]
    | .extension _ degree _ => return [Extension.ofCoefficients (Extension.coefficients degree c)]
    | .curve => missing
  | "field.embed", [b] =>
    match element with
    | .extension _ degree _ =>
      return [Extension.ofCoefficients ((List.range degree).map fun i => if i == 0 then b.toNat else 0)]
    | _ => missing
  | "field.root", [k] =>
    match element, (typeArgument arguments 0) with
    | .prime order, some (.row row) =>
      let some entry := table.type? row | missing
      let some generator := entry.twoAdicGenerator | missing
      let some (_, adicity) := entry.naturalMembers.find? (·.1 == "TwoAdicity") | missing
      if k.toNat > adicity then missing
      else return [.number (powerModulo generator (2 ^ (adicity - k.toNat)) order)]
    | _, _ => missing
  | "seq.add", [a, b] => return [.sequence ((a.items.zip b.items).map fun (x, y) => element.add x y)]
  | "seq.sub", [a, b] => return [.sequence ((a.items.zip b.items).map fun (x, y) => element.sub x y)]
  | "seq.scale", [a, s] => return [.sequence (a.items.map fun x => element.scale x s)]
  | "seq.sum", [a] => return [a.items.foldl element.add element.zero]
  | "seq.product", [a] => return [a.items.foldl element.mul (element.ofNat 1)]
  | "seq.inner", [a, s] =>
    return [(a.items.zip s.items).foldl (fun total (x, y) => element.add total (element.scale x y))
      element.zero]
  | "seq.equal", [a, b] =>
    return [Datum.ofBool (a.items.length == b.items.length &&
      (a.items.zip b.items).all fun (x, y) => element.equal x y)]
  | _, _ => missing

/-! ## The rows of the canonical layout

A writer, a reader and a proof are bytes: a datum that is the sequence of their numbers. The
rows that put and take a value of a type are the writer and the reader of the format of the
type (`formatOf`); a type without a format has neither row. -/

/-- Bytes as a datum: the sequence of their numbers. -/
@[expose] def bytesDatum (bytes : Bytes) : Datum := .sequence (bytes.map fun byte => .number byte.val)

/-- The byte that a datum is: a number below 256. -/
@[expose] def asByte : Datum → Option Byte
  | .number value => if below : value < 256 then some ⟨value, below⟩ else none
  | .sequence _ => none

/-- The bytes that a datum is: a sequence of numbers below 256. -/
@[expose] def asBytes : Datum → Option Bytes
  | .sequence items => items.mapM asByte
  | .number _ => none

/-- The datum of bytes is read as the bytes. -/
theorem asBytes_bytesDatum (bytes : Bytes) : asBytes (bytesDatum bytes) = some bytes := by
  simp only [asBytes, bytesDatum]
  induction bytes with
  | nil => rfl
  | cons byte rest hypothesis =>
    simp only [List.map_cons, List.mapM_cons, hypothesis, asByte, byte.isLt, ↓reduceDIte]
    rfl

/-- The row that puts a value on a writer: the bytes written so far, and then the bytes of the
value. A datum that the format does not admit has no bytes, and the row no value. -/
@[expose] def putRow (format : Format Datum) (writer value : Datum) : Except Failure (List Datum) :=
  if format.admits value then
    .ok [.sequence (writer.items ++ (format.write value).map fun byte => .number byte.val)]
  else .error .outside

/-- What the row that takes a value gives when the reader does not start with one: the flag
`false`, a value of the type and the reader unchanged. Under a limit that a value of the type
does not fit, it is the limit that is reached. -/
@[expose] def refusal (table : Table) (type : Closed) (limit : Option Nat) (reader : Datum) :
    Except Failure (List Datum) :=
  match limit with
  | some limit =>
    if limit < defaultElements type then .error (.limit limit)
    else .ok [Datum.ofBool false, defaultValue table type, reader]
  | none => .ok [Datum.ofBool false, defaultValue table type, reader]

/-- The row that takes a value from a reader: the flag `true`, the value at the front of the
reader and the bytes after it, or the refusal. Without a limit the reader is the reader of the
format. Under a limit it is the reader under the limit, and the row has no value when the limit
is reached: it does not say that the reader has no value. -/
@[expose] def takeRow (table : Table) (type : Closed) (format : Format Datum) (limit : Option Nat)
    (reader : Datum) : Except Failure (List Datum) :=
  match asBytes reader with
  | none => refusal table type limit reader
  | some bytes =>
    match limit with
    | none =>
      match format.read bytes with
      | some (value, rest) => .ok [Datum.ofBool true, value, bytesDatum rest]
      | none => refusal table type none reader
    | some limit =>
      match format.readWithin limit bytes with
      | .found value rest _ => .ok [Datum.ofBool true, value, bytesDatum rest]
      | .refused => refusal table type (some limit) reader
      | .limit => .error (.limit limit)

/-- The writer's row on a value of the domain: the bytes written so far, followed by the bytes
that the format writes for the value. -/
theorem putRow_written {format : Format Datum} (lawful : format.Lawful) (written : Bytes)
    {value : Datum} (inDomain : format.domain value = true) :
    putRow format (bytesDatum written) value = .ok [bytesDatum (written ++ format.write value)] := by
  simp [putRow, lawful.admits_domain value inDomain, bytesDatum, Datum.items]

/-- The reader's row on what the writer wrote, followed by anything: the flag `true`, the value
and what follows. -/
theorem takeRow_written (table : Table) (type : Closed) {format : Format Datum}
    (lawful : format.Lawful) {value : Datum} (inDomain : format.domain value = true)
    (rest : Bytes) :
    takeRow table type format none (bytesDatum (format.write value ++ rest)) =
      .ok [Datum.ofBool true, value, bytesDatum rest] := by
  simp only [takeRow, asBytes_bytesDatum, lawful.round_trip value inDomain rest]

/-- The reader's row gives the flag `true` only on bytes that the writer writes for the value it
gives, a value of the domain, followed by the bytes it leaves. -/
theorem takeRow_canonical (table : Table) (type : Closed) {format : Format Datum}
    (lawful : format.Lawful) {bytes : Bytes} {value left : Datum}
    (taken : takeRow table type format none (bytesDatum bytes) =
      .ok [Datum.ofBool true, value, left]) :
    format.domain value = true ∧
      ∃ rest, left = bytesDatum rest ∧ bytes = format.write value ++ rest := by
  simp only [takeRow, asBytes_bytesDatum] at taken
  cases read : format.read bytes with
  | none => simp [read, refusal, Datum.ofBool] at taken
  | some found =>
    obtain ⟨foundValue, rest⟩ := found
    simp only [read, Except.ok.injEq, List.cons.injEq, and_true, true_and] at taken
    obtain ⟨rfl, rfl⟩ := taken
    obtain ⟨inDomain, written⟩ := lawful.canonical _ _ _ read
    exact ⟨inDomain, rest, rfl, written⟩

/-- The reader's row under a limit reaches the limit, or is the reader's row. -/
theorem takeRow_within (table : Table) (type : Closed) {format : Format Datum}
    (agrees : format.Agrees) (limit : Nat) (reader : Datum) :
    takeRow table type format (some limit) reader = .error (.limit limit) ∨
      takeRow table type format (some limit) reader = takeRow table type format none reader := by
  have refuses : refusal table type (some limit) reader = .error (.limit limit) ∨
      refusal table type (some limit) reader = refusal table type none reader := by
    simp only [refusal]
    by_cases large : limit < defaultElements type
    · exact .inl (by simp [large])
    · exact .inr (by simp [large])
  simp only [takeRow]
  cases asBytes reader with
  | none => exact refuses
  | some bytes =>
    simp only
    cases read : format.readWithin limit bytes with
    | limit => exact .inl rfl
    | refused =>
      rw [agrees limit bytes none (by rw [read]; rfl)]
      exact refuses
    | found value rest left =>
      rw [agrees limit bytes (some (value, rest)) (by rw [read]; rfl)]
      exact .inr rfl

/-! ## The Merlin suites -/

/-- The module of a Merlin suite whose row, with a member, is named: `<suite>.<member>`. -/
def merlinSuite? (table : Table) (name member : String) : Option ModuleEntry :=
  table.modules.find? fun entry =>
    entry.implements == some "zkc::construction::Suite" && entry.row.startsWith "suite.merlin3." &&
      name == entry.row ++ "." ++ member

/-- A challenge of a prime field from squeezed bytes: their number, most significant first,
modulo the order. -/
def reduceChallenge (order : Nat) (bytes : List Nat) : Nat := Concrete.numberOf bytes % order

/-- A label of the Fiat–Shamir step as bytes: each of its numbers in eight bytes, least
significant first. A label is not a value of the canonical layout: this is the suite's own
encoding of the label that it is given. -/
def labelBytes (label : Datum) : List Nat :=
  label.items.flatMap fun number => (littleEndian 8 number.toNat).map (·.val)

/-- The transcript that a datum is: its numbers. -/
@[expose] def transcriptOf (datum : Datum) : Merlin.Transcript :=
  Merlin.Transcript.ofNumbers (datum.items.map Datum.toNat)

/-- A transcript as a datum: its numbers. -/
@[expose] def transcriptDatum (transcript : Merlin.Transcript) : Datum :=
  .sequence (transcript.toNumbers.map .number)

/-- The row of a suite that absorbs a value: the bytes that the format writes for the value,
appended to the transcript under the bytes of the label. A datum that the format does not admit
has no bytes, and the row no value. -/
@[expose] def absorbRow (format : Format Datum) (transcript label value : Datum) :
    Except Failure (List Datum) :=
  if format.admits value then
    .ok [transcriptDatum ((transcriptOf transcript).appendMessage (labelBytes label)
      ((format.write value).map (·.val)))]
  else .error .outside

/-- The absorbing row on a value of the domain appends the bytes that the format writes for the
value. Two values of the domain that the row absorbs alike under one transcript and one label
have bytes that the transcript does not tell apart, and values with the same bytes are one
value (`Format.Lawful.write_injective`). -/
theorem absorbRow_written {format : Format Datum} (lawful : format.Lawful)
    (transcript label : Datum) {value : Datum} (inDomain : format.domain value = true) :
    absorbRow format transcript label value =
      .ok [transcriptDatum ((transcriptOf transcript).appendMessage (labelBytes label)
        ((format.write value).map (·.val)))] := by
  simp [absorbRow, lawful.admits_domain value inDomain]

/-- Whether a row writes or reads values of its type argument in the canonical layout: the rows
of the layout that put and take a value, and the row of a suite that absorbs one. The model
implements such a row at a type exactly when the type has a format. -/
@[expose] def usesFormat (table : Table) (name : String) : Bool :=
  name == "layout.canonical.put" || name == "layout.canonical.take" ||
    (merlinSuite? table name "absorb").isSome

/-- A row that uses the format of its type argument, at the format: the row has no
implementation at a type without one. -/
@[expose] def withFormat (table : Table) (name : String) (arguments : List Value)
    (apply : Closed → Format Datum → Except Failure (List Datum)) : Except Failure (List Datum) :=
  match typeArgument arguments 0 with
  | some type =>
    match formatOf table type with
    | some format => apply type format
    | none => .error (.noImplementation name arguments)
  | none => .error (.noImplementation name arguments)

/-- The rows of a Merlin suite and of the canonical layout but the one that takes a value, when
`name` is one:

- `start` from the identity: the transcript with the label of the suite's row, to which the
  identity's bytes are appended under the label `identity`;
- `absorb` at a type: the bytes that the format of the type writes for the value, appended
  under the label's bytes;
- `derive` at the suite's `Challenge`: `ChallengeUnits` bytes of a challenge under the label's
  bytes, read most significant first, modulo the field's order;
- the layout: a writer and a reader are the bytes written and the bytes left; `put` appends the
  bytes that the format of the type writes for the value. -/
@[expose] def applyWritten (table : Table) (name : String) (arguments : List Value) (inputs : List Datum) :
    Option (Except Failure (List Datum)) :=
  let missing : Except Failure (List Datum) := .error (.noImplementation name arguments)
  if let some suite := merlinSuite? table name "start" then
    match inputs with
    | [identity] =>
      let transcript := Merlin.Transcript.new (Merlin.bytesOfText suite.row)
      some (.ok [transcriptDatum
        (transcript.appendMessage (Merlin.bytesOfText "identity") identity.toBytes)])
    | _ => some missing
  else if (merlinSuite? table name "absorb").isSome then
    match inputs with
    | [transcript, label, value] => some <| withFormat table name arguments fun _ format =>
      absorbRow format transcript label value
    | _ => some missing
  else if let some suite := merlinSuite? table name "derive" then
    match inputs with
    | [transcript, label] => some <|
      match typeArgument arguments 0, suite.typeMembers.find? (·.1 == "Challenge"),
          suite.naturalMembers.find? (·.1 == "ChallengeUnits") with
      | some law, some (_, challenge), some (_, units) =>
        match challenge.at table [], elementOf table law with
        | some challenge, some (.prime order) =>
          if law == challenge then
            let (bytes, transcript) :=
              (transcriptOf transcript).challengeBytes (labelBytes label) units
            .ok [.number (reduceChallenge order bytes), transcriptDatum transcript]
          else missing
        | _, _ => missing
      | _, _, _ => missing
    | _ => some missing
  else
    match name, inputs with
    | "layout.canonical.open", [] => some (.ok [bytesDatum []])
    | "layout.canonical.put", [writer, value] =>
      some (withFormat table name arguments fun _ format => putRow format writer value)
    | "layout.canonical.close", [writer] => some (.ok [writer])
    | "layout.canonical.read", [proof] => some (.ok [proof])
    | "layout.canonical.exhausted", [reader] => some (.ok [Datum.ofBool reader.items.isEmpty])
    | _, _ => none

/-- The rows of a Merlin suite and of the canonical layout, when `name` is one: the row that
takes a value of a type, `take`, is the reader of the format of the type, under the limit when
one is given (`takeRow`); the others are `applyWritten`. -/
@[expose] def applyBytes (table : Table) (name : String) (arguments : List Value) (inputs : List Datum)
    (limit : Option Nat := none) : Option (Except Failure (List Datum)) :=
  if name = "layout.canonical.take" then
    match inputs with
    | [reader] =>
      some (withFormat table name arguments fun type format =>
        takeRow table type format limit reader)
    | _ => none
  else applyWritten table name arguments inputs

/-- `hash.sha256`, on bytes, and the rows of the Merlin suites and of the canonical layout; the
other rows of `zkc::hash` are missing. Under a limit, the row that takes a value reads under
it. -/
@[expose] def applyRow (table : Table) (name : String) (arguments : List Value) (inputs : List Datum)
    (limit : Option Nat := none) : Except Failure (List Datum) :=
  match applyBytes table name arguments inputs limit with
  | some result => result
  | none =>
  match name, inputs with
  | "hash.sha256", [bytes] => .ok [Datum.ofBytes (Concrete.hash bytes.toBytes)]
  | "seq.equal", [a, b] =>
    -- an element type without arithmetic: equality of the data
    match (typeArgument arguments 0).bind (elementOf table) with
    | some _ => apply table name arguments inputs
    | none => .ok [Datum.ofBool (a == b)]
  | _, _ => apply table name arguments inputs

/-- A row under a limit reaches the limit, or is the row. -/
theorem applyRow_within (table : Table) (name : String) (arguments : List Value)
    (inputs : List Datum) (limit : Nat) :
    applyRow table name arguments inputs (some limit) = .error (.limit limit) ∨
      applyRow table name arguments inputs (some limit) = applyRow table name arguments inputs := by
  unfold applyRow applyBytes
  by_cases takes : name = "layout.canonical.take"
  · simp only [takes, ↓reduceIte]
    match inputs with
    | [reader] =>
      simp only [withFormat]
      cases typeArgument arguments 0 with
      | none => exact .inr rfl
      | some type =>
        simp only
        cases built : formatOf table type with
        | none => exact .inr rfl
        | some format =>
          simp only
          exact takeRow_within table type (formatOf_agrees table type built) limit reader
    | [] => exact .inr rfl
    | _ :: _ :: _ => exact .inr rfl
  · exact .inr (by simp only [takes, ↓reduceIte])

/-! ## The model of a package -/

mutual
  /-- The parts of a type: one per constructor in it. -/
  @[expose] def typeParts : Ty → Nat
    | .seq element _ => 1 + typeParts element
    | .tuple components => 1 + listParts components
    | .record _ _ fields => 1 + listParts fields
    | .variant _ alternatives => 1 + listParts alternatives
    | _ => 1

  def listParts : List Ty → Nat
    | [] => 0
    | type :: rest => typeParts type + listParts rest
end

/-- The closed type of the vocabulary that a type of a package stands for: a nominal row by
its catalogue name, `nonzero` at a type by that type, a sized collection and a tuple by their
parts. -/
@[expose] def closedOf (types : Array CatalogueRow) (type : Ty) : Option Closed :=
  go (types.size + typeParts type) type
where
  /-- A `type` static of a type row names an earlier row, so the rows read are at most the
  rows of the table; each other step reads a part of the type. -/
  go : Nat → Ty → Option Closed
    | 0, _ => none
    | _ + 1, .bool => some .bool
    | _ + 1, .nat => some .nat
    | _ + 1, .fin bound => some (.index bound)
    | depth + 1, .seq element size => (go depth element).map (.seq · size)
    | depth + 1, .nominal row => do
      let entry ← types[row]?
      match entry.name.toString, entry.statics with
      | "nonzero", [.type field] => (go depth field).map .nonzero
      | name, _ => some (.row name)
    | depth + 1, .tuple components => (components.mapM (go depth)).map .tuple
    | _, _ => none

/-- The static arguments of an operation row of a package. -/
def argumentsOf (types : Array CatalogueRow) (row : CatalogueRow) : Option (List Value) :=
  row.statics.mapM fun
    | .nat value => some (.natural value)
    | .type type => (closedOf types type).map .type
    | .domain _ => none

/-- What a row of a package's table computes. Under a limit, a row that takes a value reads
under it. -/
def applyOperation (table : Table) (types : Array CatalogueRow) (operation : Operation)
    (inputs : List Datum) (limit : Option Nat := none) : Except Failure (List Datum) :=
  match argumentsOf types operation.identity with
  | some arguments => applyRow table operation.identity.name.toString arguments inputs limit
  | none => .error (.missing s!"the row `{operation.identity.name.toString}` has static arguments that the vocabulary does not read")

/-- A row of a package under a limit reaches the limit, or is the row. -/
theorem applyOperation_within (table : Table) (types : Array CatalogueRow) (operation : Operation)
    (inputs : List Datum) (limit : Nat) :
    applyOperation table types operation inputs (some limit) = .error (.limit limit) ∨
      applyOperation table types operation inputs (some limit) =
        applyOperation table types operation inputs := by
  unfold applyOperation
  cases argumentsOf types operation.identity with
  | none => exact .inr rfl
  | some arguments => exact applyRow_within table _ arguments inputs limit

/-- The datum of a literal of a nominal type: a number of a field, the image of the number. -/
@[expose] def literalDatum (table : Table) (types : Array CatalogueRow) (row : Nat) (data : List Nat) : Datum :=
  match (closedOf types (.nominal row)).bind (elementOf table) with
  | some element => element.ofNat (data.headD 0)
  | none => Datum.ofBytes data

/-- The model of a package's rows. A pure row with no value gives the inhabitants of its
outputs; a run never reaches one, since a run of a package with a missing row does not
start. Its carrier is the concrete one by definition. -/
@[expose] def model (table : Table) (package : Raw.Package) : Model where
  Carrier := Concrete.Carrier
  pure row populated arguments :=
    let fallback := Ty.inhabitants (fun _ => (default : Datum)) row.outputs populated
    match package.operations[row.row]? with
    | some operation =>
      match applyOperation table package.types.toArray operation (Concrete.toData row.inputs arguments) with
      | .ok results => (Concrete.ofData row.outputs results).getD fallback
      | .error _ => fallback
    | none => fallback
  restricted row arguments :=
    match package.operations[row.row]? with
    | some operation =>
      match applyOperation table package.types.toArray operation (Concrete.toData row.inputs arguments) with
      | .ok results => Concrete.ofData row.outputs results
      | .error _ => none
    | none => none
  «opaque» _ _ := .error .refused
  literal row data := literalDatum table package.types.toArray row data

/-- The pure rows of the model of a package under a limit: a row that takes a value reads under
the limit, and has no value when the limit is reached. The executor gives the definition number
of the site that it reserves for the mark of the limit. -/
@[expose] def limitedRows (table : Table) (package : Raw.Package) (limit reserved : Nat) :
    LimitedRows (model table package) where
  limit := limit
  reserved := reserved
  pure row populated arguments :=
    let fallback := Ty.inhabitants (fun _ => (default : Datum)) row.outputs populated
    match package.operations[row.row]? with
    | some operation =>
      match applyOperation table package.types.toArray operation
          (Concrete.toData row.inputs arguments) (some limit) with
      | .ok results => some ((Concrete.ofData row.outputs results).getD fallback)
      | .error (.limit _) => none
      | .error _ => some fallback
    | none => some fallback
  agrees := by
    intro row populated arguments values given
    simp only [model]
    cases found : package.operations[row.row]? with
    | none =>
      simp only [found] at given ⊢
      exact (Option.some.inj given).symm
    | some operation =>
      simp only [found] at given ⊢
      rcases applyOperation_within table package.types.toArray operation
          (Concrete.toData row.inputs arguments) limit with reached | same
      · simp [reached] at given
      · rw [same] at given
        cases applied : applyOperation table package.types.toArray operation
            (Concrete.toData row.inputs arguments) with
        | ok results =>
          simp only [applied] at given ⊢
          exact (Option.some.inj given).symm
        | error failure =>
          cases failure with
          | limit elements => simp [applied] at given
          | outside =>
            simp only [applied] at given ⊢
            exact (Option.some.inj given).symm
          | missing message =>
            simp only [applied] at given ⊢
            exact (Option.some.inj given).symm

/-! ## Laws

One definition of what a value of a law is, read by every source of coins: the coins of a seed
(`seededCoins`), the data of the comparison of runs (`ValidData`) and a caller's own source.
A law makes a value of a closed type from a stream of numbers:

- `bool` and `index<n>`: a number modulo 2 and modulo `n`; `index<0>` has no value;
- an element of a prime field: a number modulo the order; a unit of it: one more than a number
  modulo the order less one;
- an element of an extension: a coefficient per number, each modulo the order of the base; a
  unit of it: the same, and the element one when every coefficient is zero, so the one is
  twice as likely as any other unit;
- a point of G1: the generator times a number below a bound on scalars. The bound is the order
  of the group for the coins of a run; a source that makes many points gives a smaller one and
  says so, because a multiple of a point is costly in the model;
- a tuple and a collection with a size: component by component, each from numbers of its own.

`nat`, a collection without a size, and a nominal type without arithmetic have no law. -/

namespace Law

/-- A `bool` from a number. -/
def bool (number : Nat) : Datum := Datum.ofBool (number % 2 == 1)

/-- An `index<bound>` from a number, for a bound above zero. -/
def index (bound number : Nat) : Datum := .number (number % bound)

/-- An element of a prime field from a number. -/
def field (order number : Nat) : Datum := .number (number % order)

/-- A unit of a prime field of order two or more from a number. -/
def unit (order number : Nat) : Datum := .number (1 + number % (order - 1))

/-- An element of an extension, or a unit of it, from the numbers at `next` and after. -/
def extension (order degree : Nat) (unit : Bool) (numbers : Nat → Nat) (next : Nat) : Datum :=
  let values := (List.range degree).map fun index => numbers (next + index) % order
  Extension.ofCoefficients (if unit && values.all (· == 0) then 1 :: values.drop 1 else values)

/-- A point of G1 from a number: the generator times the number below the bound on scalars. -/
def point (scalars number : Nat) : Datum :=
  Datum.ofPoint (Concrete.scalePoint Concrete.generator (number % scalars))

/-- A value of an element type, or a unit of it, from the numbers at `next` and after; with the
position after the numbers it read. -/
def element (scalars : Nat) (numbers : Nat → Nat) (unit : Bool) :
    Element → Nat → Except String (Datum × Nat)
  | .prime order, next =>
    if unit then
      if order < 2 then .error s!"a field of order {order} has no unit"
      else .ok (Law.unit order (numbers next), next + 1)
    else .ok (Law.field order (numbers next), next + 1)
  | .extension order degree _, next => .ok (extension order degree unit numbers next, next + degree)
  | .curve, next =>
    if unit then .error "a point of G1 is no unit"
    else .ok (point scalars (numbers next), next + 1)

/-- `count` values in a row, each made by `one` from where the one before it ended. -/
def repeated (one : Nat → Except String (Datum × Nat)) :
    Nat → Nat → Array Datum → Except String (List Datum × Nat)
  | 0, next, items => .ok (items.toList, next)
  | count + 1, next, items =>
    match one next with
    | .error reason => .error reason
    | .ok (item, after) => repeated one count after (items.push item)

end Law

mutual
  /-- The value of the law of a closed type from a stream of numbers, from the position `next`
  on, with the position after the numbers it read; or why the type has no law. `scalars`
  bounds the scalar of a point. -/
  def lawValue (table : Table) (scalars : Nat) (numbers : Nat → Nat) :
      Closed → Nat → Except String (Datum × Nat)
    | .bool, next => .ok (Law.bool (numbers next), next + 1)
    | .nat, _ => .error "`nat` has no law"
    | .index bound, next =>
      if bound == 0 then .error "`index<0>` has no value"
      else .ok (Law.index bound (numbers next), next + 1)
    | .nonzero field, next =>
      match elementOf table field with
      | some found => Law.element scalars numbers true found next
      | none => .error "`nonzero` of a type without arithmetic has no law"
    | .seq _ none, _ => .error "a collection without a size has no law"
    | .seq element (some size), next =>
      match Law.repeated (lawValue table scalars numbers element) size next #[] with
      | .error reason => .error reason
      | .ok (items, after) => .ok (.sequence items, after)
    | .tuple components, next =>
      match lawValues table scalars numbers components next with
      | .error reason => .error reason
      | .ok (items, after) => .ok (.sequence items, after)
    | .row name, next =>
      match elementOf table (.row name) with
      | some found => Law.element scalars numbers false found next
      | none => .error s!"`{name}` has no law: the model of the vocabulary has no arithmetic for it"

  /-- The values of the laws of the components of a tuple, in order. -/
  def lawValues (table : Table) (scalars : Nat) (numbers : Nat → Nat) :
      List Closed → Nat → Except String (List Datum × Nat)
    | [], next => .ok ([], next)
    | component :: rest, next =>
      match lawValue table scalars numbers component next with
      | .error reason => .error reason
      | .ok (item, after) =>
        match lawValues table scalars numbers rest after with
        | .error reason => .error reason
        | .ok (items, last) => .ok (item :: items, last)
end

/-- The value of the law of a type of a package from a stream of numbers, or why it has none. -/
def lawValueOf (table : Table) (types : Array CatalogueRow) (scalars : Nat) (numbers : Nat → Nat)
    (type : Ty) : Except String Datum :=
  match closedOf types type with
  | some closed => (·.1) <$> lawValue table scalars numbers closed 0
  | none => .error "a type that the vocabulary does not close has no law"

/-! ## The rows of a package against the vocabulary -/

/-- Whether the types of a row of a package are the closed types that the vocabulary gives the
row, in order. -/
@[expose] def sameTypes (types : Array CatalogueRow) : List Ty → List Closed → Bool
  | [], [] => true
  | type :: rest, closed :: others =>
    (match closedOf types type with
      | some found => found == closed
      | none => false) && sameTypes types rest others
  | _, _ => false

/-- Whether the kind of a row of a package is the kind that the vocabulary gives the row. A
restricted row names its domain row by its number in the package: that row has the name that
the vocabulary gives and the static arguments of the restricted row. -/
@[expose] def sameKind (operations : List Operation) (identity : CatalogueRow) : OperationKind → Kind → Bool
  | .pure, .pure => true
  | .sampling, .sampling => true
  | .restricted none, .restricted none => true
  | .restricted (some row), .restricted (some name) =>
    match operations[row]? with
    | some domain => domain.identity.name.toString == name && domain.identity.statics == identity.statics
    | none => false
  | _, _ => false

/-- Why a row of a package is not the row of the vocabulary that its name and its static
arguments name, when it is not: the vocabulary does not read its static arguments, it has no row
of the name at them, or it gives the row another kind (the domain row included), other inputs or
other outputs. -/
def mismatch (table : Table) (package : Raw.Package) (operation : Operation) : Option String :=
  let name := operation.identity.name.toString
  let types := package.types.toArray
  match argumentsOf types operation.identity with
  | none => some s!"the row `{name}` has static arguments that the vocabulary does not read"
  | some arguments =>
    match table.signature? name arguments with
    | none => some s!"the row {describe name arguments} is not a row of the vocabulary"
    | some signature =>
      if !sameKind package.operations operation.identity operation.signature.kind signature.kind then
        some s!"the row {describe name arguments} does not have the kind that the vocabulary gives it"
      else if !sameTypes types operation.signature.inputs signature.inputs then
        some s!"the row {describe name arguments} does not have the inputs that the vocabulary gives it"
      else if !sameTypes types operation.signature.outputs signature.outputs then
        some s!"the row {describe name arguments} does not have the outputs that the vocabulary gives it"
      else none

/-- The message of the model when it does not implement a row of a package. A row that writes
or reads values of its type argument in the canonical layout (`usesFormat`) is implemented
exactly when the type has a format. Every other pure or restricted row is tried on one value per
input, the image of 1 in an element type, to tell a row that the model does not implement from
the edge of a domain; a sampling row needs no implementation. -/
@[expose] def unimplemented (table : Table) (package : Raw.Package) (operation : Operation) : Option String :=
  if operation.signature.kind == .sampling then none
  else
    match argumentsOf package.types.toArray operation.identity with
    | none => none
    | some arguments =>
      let name := operation.identity.name.toString
      if usesFormat table name then
        match (typeArgument arguments 0).bind (formatOf table) with
        | some _ => none
        | none => some s!"the row {describe name arguments} has no implementation in the model"
      else
        let probe := operation.signature.inputs.map fun type =>
          match (closedOf package.types.toArray type).bind (elementOf table) with
          | some element => element.ofNat 1
          | none => (default : Datum)
        match applyRow table name arguments probe with
        | .error (.missing message) => some message
        | _ => none

/-- The rows of a package that are not rows of the vocabulary, each with the reason
(`mismatch`). It reads the tables of the package and of the vocabulary only, not the model, so
the kernel computes it. -/
@[expose] def mismatches (table : Table) (package : Raw.Package) : List String :=
  package.operations.filterMap (mismatch table package)

/-- Whether the vocabulary has a row of a name, at whatever static arguments. -/
@[expose] def Table.names (table : Table) (name : String) : Bool :=
  table.rows.any fun entry => entry.name == name

/-- The rows of a package under a name of the vocabulary that are not the vocabulary's rows,
each with the reason (`mismatch`): static arguments at which the vocabulary has no row of the
name, or another kind, other inputs or other outputs. A row under a name that the vocabulary
does not have is a row of an extension of the vocabulary, and nothing is said of it here. -/
@[expose] def misstated (table : Table) (package : Raw.Package) : List String :=
  package.operations.filterMap fun operation =>
    cond (table.names operation.identity.name.toString) (mismatch table package operation) none

/-- The names of the rows of a package that the vocabulary does not have: the rows of an
extension of the vocabulary. A package without one is a package of the vocabulary alone. -/
@[expose] def extensions (table : Table) (package : Raw.Package) : List String :=
  package.operations.filterMap fun operation =>
    cond (table.names operation.identity.name.toString) none
      (some operation.identity.name.toString)

/-- A package whose rows under the vocabulary's names are the vocabulary's, and that has no
row of an extension, has the vocabulary's rows. -/
theorem mismatches_of_misstated {table : Table} {package : Raw.Package}
    (stated : misstated table package = []) (closed : extensions table package = []) :
    mismatches table package = [] := by
  unfold misstated at stated
  unfold extensions at closed
  unfold mismatches
  rw [List.filterMap_eq_nil_iff] at stated closed ⊢
  intro operation member
  have one := stated operation member
  have two := closed operation member
  cases named : table.names operation.identity.name.toString with
  | true =>
      rw [named] at one
      exact one
  | false =>
      rw [named] at two
      cases two

/-- The rows of a package that the vocabulary does not admit, each with the reason: a row that is
not the vocabulary's row of its name at its static arguments, with the vocabulary's kind, domain
row, inputs and outputs (`mismatch`), or one that the model does not implement
(`unimplemented`). A package that the vocabulary admits has none. -/
@[expose] def missing (table : Table) (package : Raw.Package) : List String :=
  package.operations.filterMap fun operation =>
    match mismatch table package operation with
    | some message => some message
    | none => unimplemented table package operation

/-- A package that the vocabulary admits has the vocabulary's rows. -/
theorem mismatches_of_admitted {table : Table} {package : Raw.Package}
    (admitted : missing table package = []) : mismatches table package = [] := by
  unfold missing at admitted
  unfold mismatches
  rw [List.filterMap_eq_nil_iff] at admitted ⊢
  intro operation member
  have none_ := admitted operation member
  cases found : mismatch table package operation with
  | none => rfl
  | some message => simp [found] at none_

/-! ## Running a function -/

/-- How a run ends. -/
inductive Run where
  | returned (outputs : List Datum)
  | stopped (reason : PIR.Stop)
  /-- A reading of a value reached the limit of the run on the number of elements it builds.
  The function was not run to its end: it did not return, and it did not stop. -/
  | limit (elements : Nat)
  /-- The run did not start, or the function is not one the runner can run. -/
  | failed (message : String)
  deriving Inhabited

mutual
  /-- Whether a datum is a value of a type of a package, with the arithmetic of its nominal
  types: a number below the bound of an index, an element of a field below its order, a unit of
  a field that is not zero, a point of G1 that is of the group, and the collections, tuples,
  records and variants of these. -/
  def validInput (table : Table) (types : Array CatalogueRow) : Ty → Datum → Bool
    | .bool, .number value => value < 2
    | .nat, .number _ => true
    | .fin bound, .number value => value < bound
    | .nominal row, datum =>
      match closedOf types (.nominal row) with
      | some (.nonzero field) =>
        match elementOf table field with
        | some element => element.valid datum && !element.isZero datum
        | none => true
      | some closed =>
        match elementOf table closed with
        | some element => element.valid datum
        | none => true
      | none => true
    | .seq element size, .sequence items =>
      (size.all (· == items.length)) && items.all (validInput table types element)
    | .tuple components, .sequence items => validInputs table types components items
    | .record _ _ fields, .sequence items => validInputs table types fields items
    | .variant _ alternatives, .sequence [.number position, item] =>
      validAlternative table types alternatives position item
    | _, _ => false

  /-- Whether data are values of types, one of each, in order. -/
  def validInputs (table : Table) (types : Array CatalogueRow) : List Ty → List Datum → Bool
    | [], [] => true
    | type :: rest, item :: items =>
      validInput table types type item && validInputs table types rest items
    | _, _ => false

  /-- Whether a datum is a value of the alternative at a position. -/
  def validAlternative (table : Table) (types : Array CatalogueRow) :
      List Ty → Nat → Datum → Bool
    | [], _, _ => false
    | alternative :: _, 0, item => validInput table types alternative item
    | _ :: rest, position + 1, item => validAlternative table types rest position item
end

/-- The type of a writer, a reader and a proof of the canonical layout: bytes. -/
abbrev bytesType : Ty := .seq (.fin 256) none

/-- A datum that validation found to be a value of a type of a package. It is made only by
validation (`checked?`, and `Checked.ofBytes` for bytes, which are values of their type), so a
run that takes one does not validate it again: an input is validated once and run as often as
a caller likes. -/
structure Checked (table : Table) (package : Raw.Package) where
  private mk ::
  type : Ty
  datum : Datum
  valid : validInput table package.types.toArray type datum = true

/-- A datum validated at a type of a package, when it is a value of the type. -/
def checked? (table : Table) (package : Raw.Package) (type : Ty) (datum : Datum) :
    Option (Checked table package) :=
  if valid : validInput table package.types.toArray type datum = true then
    some ⟨type, datum, valid⟩
  else none

/-- Bytes are values of the type of bytes. -/
theorem validInput_bytes (table : Table) (types : Array CatalogueRow) (bytes : Bytes) :
    validInput table types bytesType (bytesDatum bytes) = true := by
  simp only [bytesDatum, validInput, Option.all_none, Bool.true_and, List.all_map,
    List.all_eq_true]
  intro byte _
  simp [validInput, byte.isLt]

/-- Bytes as a validated input: a proof that a verifier reads. -/
def Checked.ofBytes (table : Table) (package : Raw.Package) (bytes : Bytes) :
    Checked table package :=
  ⟨bytesType, bytesDatum bytes, validInput_bytes table package.types.toArray bytes⟩

/-- A validated input was found to be a value of its type. -/
theorem Checked.isValid {table : Table} {package : Raw.Package} (input : Checked table package) :
    validInput table package.types.toArray input.type input.datum = true := input.valid

section Run

variable (table : Table) (package : Raw.Package)

/-- The function with a number among the functions of a program, most recent first. -/
def nthFunction {m : Model} : (headers : List FunctionHeader) → FunctionTable m headers → Nat →
    Option ((header : FunctionHeader) × header.Meaning m)
  | [], .nil, _ => none
  | header :: _, .cons meaning _, 0 => some ⟨header, meaning⟩
  | _ :: rest, .cons _ meanings, index + 1 => nthFunction rest meanings index

/-- The end of the process of a function of the local dialect, which has no effect. -/
def finish {m : Model} {α : Type} : PIR.Process (Effects m) α → Except String (Except PIR.Stop α)
  | .done value => .ok (.ok value)
  | .halt reason => .ok (.error reason)
  | .call .. => .error "the function applies an effect"

end Run

/-- The functions that a run runs: the functions of the package under the model of the
vocabulary's rows, with every pure row under the limit. -/
@[expose] def limitedFunctions (table : Table) (package : Raw.Package) (typed : Typed)
    (limit : Nat) : FunctionTable (model table package) typed.functions :=
  typed.program.functions.limitedTable (model table package)
    (limitedRows table package limit package.protocols.length)

/-- The functions that a run runs are the functions of the meaning under the model of the
vocabulary's rows, cut where a reading reaches the limit: a function that returns or stops in a
run does so in the meaning. -/
theorem limitedFunctions_within (table : Table) (package : Raw.Package) (typed : Typed)
    (limit : Nat) :
    TableWithin (limitedFunctions table package typed limit)
      (typed.program.functionTable (model table package)) :=
  Functions.limitedTable_within (limitedRows table package limit package.protocols.length)
    typed.program.functions

/-- Runs the function with a number of an admitted package on validated inputs, under the model
of the vocabulary's rows, with a limit on the number of elements of collections that one reading
of a value builds (`defaultLimit` when none is given). Each input was validated at the type that
the function takes at its position; the run does not validate it again. A run that reaches the
limit ends with the limit: the function did not return and did not stop. -/
def run (table : Table) (package : Raw.Package) (function : Nat)
    (inputs : List (Checked table package)) (limit : Nat := defaultLimit) : Run :=
  match elaborate package with
  | .error refusal => .failed s!"the core refuses the package: {reprStr refusal}"
  | .ok typed =>
    match missing table package with
    | first :: _ => .failed first
    | [] =>
      let m := model table package
      let count := typed.functions.length
      if function ≥ count then .failed s!"the package has {count} functions" else
      match nthFunction typed.functions (limitedFunctions table package typed limit)
          (count - 1 - function) with
      | none => .failed s!"the package has no function {function}"
      | some ⟨header, meaning⟩ =>
        if inputs.length != header.inputs.length then
          .failed s!"the function takes {header.inputs.length} inputs; {inputs.length} are given"
        else if !((header.inputs.zip inputs).all fun (type, input) => decide (input.type = type)) then
          .failed "an input was validated at another type than the function takes"
        else
          match Concrete.ofData header.inputs (inputs.map (·.datum)) with
          | none => .failed "an input is not a value of its type"
          | some arguments =>
            let process := meaning arguments
            match limitOf? m package.protocols.length process with
            | some reached => .limit reached
            | none =>
              match finish process with
              | .error message => .failed message
              | .ok (.error reason) => .stopped reason
              | .ok (.ok values) => .returned (Concrete.toData header.outputs values)

/-- Validates data as the inputs of the function with a number of a package, each at the type
that the function takes at its position, and runs the function on them (`run`). -/
def runData (table : Table) (package : Raw.Package) (function : Nat) (data : List Datum)
    (limit : Nat := defaultLimit) : Run :=
  match elaborate package with
  | .error refusal => .failed s!"the core refuses the package: {reprStr refusal}"
  | .ok typed =>
    match typed.functions[typed.functions.length - 1 - function]? with
    | none => .failed s!"the package has {typed.functions.length} functions"
    | some header =>
      if data.length != header.inputs.length then
        .failed s!"the function takes {header.inputs.length} inputs; {data.length} are given"
      else
        match (header.inputs.zip data).mapM fun (type, datum) => checked? table package type datum with
        | none => .failed "an input is not a value of its type"
        | some inputs => run table package function inputs limit

/-! ## The domain laws

The model satisfies the domain laws of the operation table of a package whose rows are the
vocabulary's. The proof reads the one restricted row off the vocabulary, reads the signature of
the package's row off the comparison with it, and computes what the row and its domain row give
on an element. -/

section DomainLaws

/-- The restricted row of the vocabulary: `field.nonzero`, with the domain row
`field.is_nonzero`. -/
private def nonzeroRow : RowEntry :=
  on "Field" "field.nonzero" [self] [.nonzero self] (kind := .restricted (some "field.is_nonzero"))

/-- Whether a kind is restricted. -/
private def Kind.isRestricted : Kind → Bool
  | .restricted _ => true
  | _ => false

/-- The vocabulary has one restricted row. -/
private theorem restricted_rows :
    Vocabulary.table.rows.filter (·.kind.isRestricted) = [nonzeroRow] := by rfl

/-- A restricted row of the vocabulary is `field.nonzero`. -/
private theorem restricted_entry {entry : RowEntry} {domain : Option String}
    (member : entry ∈ Vocabulary.table.rows) (kind : entry.kind = .restricted domain) :
    entry = nonzeroRow := by
  have filtered : entry ∈ Vocabulary.table.rows.filter (·.kind.isRestricted) :=
    List.mem_filter.mpr ⟨member, by rw [kind]; rfl⟩
  rw [restricted_rows] at filtered
  exact List.mem_singleton.mp filtered

/-- A row of the vocabulary whose signature at static arguments is restricted is `field.nonzero`
at a type: its domain row is `field.is_nonzero`, its one input is the type and its one output
the units of the type. -/
private theorem signature_restricted {name : String} {arguments : List Value} {signature : Signature}
    {domain : Option String} (found : Vocabulary.table.signature? name arguments = some signature)
    (kind : signature.kind = .restricted domain) :
    name = "field.nonzero" ∧ domain = some "field.is_nonzero" ∧
      ∃ closed, arguments = [.type closed] ∧ signature.inputs = [closed] ∧
        signature.outputs = [.nonzero closed] := by
  unfold Table.signature? at found
  cases row : Vocabulary.table.row? name arguments with
  | none => simp [row] at found
  | some entry =>
    have member : entry ∈ Vocabulary.table.rows := List.mem_of_find?_eq_some row
    have holds := List.find?_some row
    simp only [row, Option.bind_eq_bind, Option.bind_some] at found
    cases inputsAt : List.mapM (Term.at Vocabulary.table arguments) entry.inputs with
    | none => simp [inputsAt] at found
    | some inputs =>
      cases outputsAt : List.mapM (Term.at Vocabulary.table arguments) entry.outputs with
      | none => simp [inputsAt, outputsAt] at found
      | some outputs =>
        simp only [inputsAt, outputsAt, Option.bind_some, pure, Option.some.injEq] at found
        subst found
        have isRow := restricted_entry member kind
        subst isRow
        simp only [Bool.and_eq_true, beq_iff_eq] at holds
        obtain ⟨⟨nameEq, lengthEq⟩, accepts⟩ := holds
        have domainEq : some "field.is_nonzero" = domain := Kind.restricted.inj kind
        match arguments, lengthEq, accepts, inputsAt, outputsAt with
        | [.type closed], _, _, inputsAt, outputsAt =>
          have inputsEq : some [closed] = some inputs := inputsAt
          have outputsEq : some [Closed.nonzero closed] = some outputs := outputsAt
          exact ⟨nameEq.symm, domainEq.symm, closed, rfl, (Option.some.inj inputsEq).symm,
            (Option.some.inj outputsEq).symm⟩
        | [.natural _], _, accepts, _, _ => exact absurd accepts (by simp [nonzeroRow, on, Parameter.accepts])
        | [], lengthEq, _, _, _ => exact absurd lengthEq (by simp [nonzeroRow, on])
        | _ :: _ :: _, lengthEq, _, _, _ => exact absurd lengthEq (by simp [nonzeroRow, on])


/-- A row of a package that is the vocabulary's: what the comparison found. -/
theorem mismatch_none {table : Table} {package : Raw.Package} {operation : Operation}
    (same : mismatch table package operation = none) :
    ∃ arguments signature,
      argumentsOf package.types.toArray operation.identity = some arguments ∧
      table.signature? operation.identity.name.toString arguments = some signature ∧
      sameKind package.operations operation.identity operation.signature.kind signature.kind = true ∧
      sameTypes package.types.toArray operation.signature.inputs signature.inputs = true ∧
      sameTypes package.types.toArray operation.signature.outputs signature.outputs = true := by
  unfold mismatch at same
  cases read : argumentsOf package.types.toArray operation.identity with
  | none => simp [read] at same
  | some arguments =>
    cases found : table.signature? operation.identity.name.toString arguments with
    | none => simp [read, found] at same
    | some signature =>
      cases kind : sameKind package.operations operation.identity operation.signature.kind signature.kind <;>
        cases inputs : sameTypes package.types.toArray operation.signature.inputs signature.inputs <;>
        cases outputs : sameTypes package.types.toArray operation.signature.outputs signature.outputs <;>
        simp [read, found, kind, inputs, outputs] at same
      exact ⟨arguments, signature, rfl, found, kind, inputs, outputs⟩

/-- A restricted row of a package that names a domain row has the vocabulary's kind when the
vocabulary's row is restricted with a domain row, and the package's domain row has that name
and the static arguments of the restricted row. -/
private theorem sameKind_restricted {operations : List Operation} {identity : CatalogueRow} {domain : Nat}
    {kind : Kind} (same : sameKind operations identity (.restricted (some domain)) kind = true) :
    ∃ name operation, kind = .restricted (some name) ∧ operations[domain]? = some operation ∧
      operation.identity.name.toString = name ∧ operation.identity.statics = identity.statics := by
  match kind, same with
  | .restricted (some name), same =>
    unfold sameKind at same
    cases found : operations[domain]? with
    | none => simp [found] at same
    | some operation =>
      simp only [found, Bool.and_eq_true, beq_iff_eq] at same
      exact ⟨name, operation, rfl, rfl, same.1, same.2⟩
  | .restricted none, same => exact absurd same (by simp [sameKind])
  | .pure, same => exact absurd same (by simp [sameKind])
  | .sampling, same => exact absurd same (by simp [sameKind])

/-- Types that are one closed type of the vocabulary are one type. -/
private theorem sameTypes_one {types : Array CatalogueRow} {given : List Ty} {closed : Closed}
    (same : sameTypes types given [closed] = true) :
    ∃ type found, given = [type] ∧ closedOf types type = some found ∧ (found == closed) = true := by
  match given, same with
  | [type], same =>
    cases read : closedOf types type with
    | none => simp [sameTypes, read] at same
    | some found =>
      simp only [sameTypes, read, Bool.and_true] at same
      exact ⟨type, found, rfl, read, same⟩
  | [], same => exact absurd same (by simp [sameTypes])
  | _ :: _ :: _, same => exact absurd same (by simp [sameTypes])

/-- A closed type equal to the units of a type is the units of a type. -/
private theorem nonzero_of_beq {found closed : Closed} (same : (found == Closed.nonzero closed) = true) :
    ∃ field, found = .nonzero field := by
  cases found with
  | nonzero field => exact ⟨field, rfl⟩
  | _ => exact absurd same (by simp [BEq.beq, Closed.beq])

/-- A type of a package that stands for the units of a type is a nominal type. -/
private theorem nominal_of_nonzero {types : Array CatalogueRow} :
    ∀ (depth : Nat) (type : Ty) {field : Closed},
      closedOf.go types depth type = some (.nonzero field) → ∃ row, type = .nominal row
  | 0, _, _, closed => by simp [closedOf.go] at closed
  | depth + 1, type, _, closed => by
    cases type with
    | nominal row => exact ⟨row, rfl⟩
    | _ => simp [closedOf.go] at closed

/-- One type read in a type table is one type. -/
private theorem fillAll_one {typeTable : TypeTable} {type : Ty} {filled : List Ty}
    (fills : Ty.fillAll typeTable [type] = some filled) : ∃ one, filled = [one] := by
  simp only [Ty.fillAll] at fills
  cases one : Ty.fill typeTable type with
  | none => simp [one] at fills
  | some one' => simp [one] at fills; exact ⟨one', fills.symm⟩

/-- A nominal type read in a type table is itself. -/
private theorem fillAll_nominal {typeTable : TypeTable} {row : Nat} {filled : List Ty}
    (fills : Ty.fillAll typeTable [.nominal row] = some filled) : filled = [.nominal row] := by
  simp [Ty.fillAll, Ty.fill] at fills
  exact fills.symm

/-- An entry of a filled list is the filled entry of the given list at the same position. -/
theorem fillEach_getElem? {α : Type} {fill : α → Option α} :
    ∀ {entries filled : List α}, fillEach fill entries = some filled →
      ∀ {index : Nat} {entry : α}, filled[index]? = some entry →
        ∃ given, entries[index]? = some given ∧ fill given = some entry
  | [], _, fills, _, _, found => by
    simp [fillEach] at fills
    subst fills
    simp at found
  | given :: rest, _, fills, index, entry, found => by
    simp only [fillEach] at fills
    cases first : fill given with
    | none => simp [first] at fills
    | some filledFirst =>
      cases others : fillEach fill rest with
      | none => simp [first, others] at fills
      | some filledRest =>
        simp [first, others] at fills
        subst fills
        cases index with
        | zero =>
          simp at found
          subst found
          exact ⟨given, rfl, first⟩
        | succ index =>
          simp at found
          simpa using fillEach_getElem? others found

/-- A row read in a type table keeps its kind; its inputs and outputs are read in the table. -/
theorem fill_signature {typeTable : TypeTable} {given filled : Operation}
    (fills : Operation.fill typeTable given = some filled) :
    filled.signature.kind = given.signature.kind ∧
      Ty.fillAll typeTable given.signature.inputs = some filled.signature.inputs ∧
      Ty.fillAll typeTable given.signature.outputs = some filled.signature.outputs := by
  unfold Operation.fill at fills
  split at fills
  · rename_i inputs outputs _ fillsInputs fillsOutputs
    cases fills
    exact ⟨rfl, fillsInputs, fillsOutputs⟩
  · cases fills


/-- No module of the vocabulary is a Merlin suite whose row, with the member, is the name, when
no row of a module with the member is the name. -/
theorem merlinSuite?_none (name member : String)
    (differs : (Vocabulary.table.modules.all fun entry => name != entry.row ++ "." ++ member) = true) :
    merlinSuite? Vocabulary.table name member = none := by
  unfold merlinSuite?
  rw [List.find?_eq_none]
  intro entry isModule
  have other := List.all_eq_true.mp differs entry isModule
  simp only [bne_iff_ne, ne_eq] at other
  simp [other]

/-- No row of a suite or of the layout is named `field.nonzero` or `field.is_nonzero`. -/
private theorem applyBytes_none {name : String} (arguments : List Value) (inputs : List Datum)
    (start : merlinSuite? Vocabulary.table name "start" = none)
    (absorb : merlinSuite? Vocabulary.table name "absorb" = none)
    (derive : merlinSuite? Vocabulary.table name "derive" = none)
    (field : name = "field.nonzero" ∨ name = "field.is_nonzero") :
    applyBytes Vocabulary.table name arguments inputs = none := by
  have other : name ≠ "layout.canonical.take" := by
    rcases field with rfl | rfl <;> decide
  unfold applyBytes applyWritten
  simp only [other, start, derive, absorb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  split <;> first | rfl | exact absurd field (by decide +kernel)

/-- The rows `field.nonzero` and `field.is_nonzero` are rows of the element arithmetic: no row of
a suite or of the layout has either name. -/
private theorem applyRow_field {name : String} (arguments : List Value) (inputs : List Datum)
    (start : merlinSuite? Vocabulary.table name "start" = none)
    (absorb : merlinSuite? Vocabulary.table name "absorb" = none)
    (derive : merlinSuite? Vocabulary.table name "derive" = none)
    (field : name = "field.nonzero" ∨ name = "field.is_nonzero") :
    applyRow Vocabulary.table name arguments inputs = apply Vocabulary.table name arguments inputs := by
  unfold applyRow
  simp only [applyBytes_none arguments inputs start absorb derive field]
  split <;> first | rfl | exact absurd field (by decide +kernel)

/-- What `field.nonzero` gives on one datum. -/
private theorem apply_nonzero (closed : Closed) (a : Datum) :
    apply Vocabulary.table "field.nonzero" [.type closed] [a] =
      match elementOf Vocabulary.table closed with
      | some element => if element.isZero a then .error .outside else .ok [a]
      | none => .error (.noImplementation "field.nonzero" [.type closed]) := by
  unfold apply
  cases found : elementOf Vocabulary.table closed with
  | none => simp [typeArgument, found, bind, Except.bind]
  | some element => simp [typeArgument, found, bind, Except.bind, pure, Except.pure]

/-- What `field.is_nonzero` gives on one datum. -/
private theorem apply_isNonzero (closed : Closed) (a : Datum) :
    apply Vocabulary.table "field.is_nonzero" [.type closed] [a] =
      match elementOf Vocabulary.table closed with
      | some element => .ok [Datum.ofBool (!element.isZero a)]
      | none => .error (.noImplementation "field.is_nonzero" [.type closed]) := by
  unfold apply
  cases found : elementOf Vocabulary.table closed with
  | none => simp [typeArgument, found, bind, Except.bind]
  | some element => simp [typeArgument, found, bind, Except.bind, pure, Except.pure]


private theorem applyRow_nonzero (closed : Closed) (a : Datum) :
    applyRow Vocabulary.table "field.nonzero" [.type closed] [a] =
      match elementOf Vocabulary.table closed with
      | some element => if element.isZero a then .error .outside else .ok [a]
      | none => .error (.noImplementation "field.nonzero" [.type closed]) :=
  (applyRow_field _ _ (merlinSuite?_none _ _ (by decide +kernel))
    (merlinSuite?_none _ _ (by decide +kernel)) (merlinSuite?_none _ _ (by decide +kernel))
    (.inl rfl)).trans (apply_nonzero closed a)

private theorem applyRow_isNonzero (closed : Closed) (a : Datum) :
    applyRow Vocabulary.table "field.is_nonzero" [.type closed] [a] =
      match elementOf Vocabulary.table closed with
      | some element => .ok [Datum.ofBool (!element.isZero a)]
      | none => .error (.noImplementation "field.is_nonzero" [.type closed]) :=
  (applyRow_field _ _ (merlinSuite?_none _ _ (by decide +kernel))
    (merlinSuite?_none _ _ (by decide +kernel)) (merlinSuite?_none _ _ (by decide +kernel))
    (.inr rfl)).trans (apply_isNonzero closed a)

/-- A restricted row of the model, at a row of the package. -/
private theorem model_restricted (table : Table) (package : Raw.Package) (row : Nat)
    (inputs outputs : List Ty) (arguments : Values Concrete.Value inputs) {operation : Operation}
    (found : package.operations[row]? = some operation) :
    (model table package).restricted ⟨row, inputs, outputs⟩ arguments =
      match applyOperation table package.types.toArray operation (Concrete.toData inputs arguments) with
      | .ok results => Concrete.ofData outputs results
      | .error _ => none := by
  simp only [model, found]

/-- A pure row of the model, at a row of the package. -/
theorem model_pure (table : Table) (package : Raw.Package) (row : Nat)
    (inputs outputs : List Ty) (populated : Ty.allPopulated outputs = true)
    (arguments : Values Concrete.Value inputs) {operation : Operation}
    (found : package.operations[row]? = some operation) :
    (model table package).pure ⟨row, inputs, outputs⟩ populated arguments =
      match applyOperation table package.types.toArray operation (Concrete.toData inputs arguments) with
      | .ok results =>
        (Concrete.ofData outputs results).getD
          (Ty.inhabitants (fun _ => (default : Datum)) outputs populated)
      | .error _ => Ty.inhabitants (fun _ => (default : Datum)) outputs populated := by
  simp only [model, found]

/-- A row of a package whose static arguments the vocabulary reads computes what the
vocabulary's row of its name computes at them. -/
theorem applyOperation_read {table : Table} {types : Array CatalogueRow}
    {operation : Operation} {arguments : List Value} (inputs : List Datum)
    (read : argumentsOf types operation.identity = some arguments) :
    applyOperation table types operation inputs =
      applyRow table operation.identity.name.toString arguments inputs := by
  simp only [applyOperation, read]

/-- The model of the vocabulary satisfies the domain laws of the operation table of a package
whose rows are the vocabulary's, read in a type table: a restricted row that names a domain row
has a value exactly where the domain row gives `true`.

A row of such a package has the vocabulary's signature, so a restricted row of it that names a
domain row is `field.nonzero` at a field, and its domain row is `field.is_nonzero` at the same
field. On an element of a field whose arithmetic the model has, the first has a value exactly
when the element is not zero, which is what the second gives; at a field without arithmetic
here the first has no value and the second gives `false`. -/
theorem model_domainLaws_of_filled {package : Raw.Package} {typeTable : TypeTable}
    {operations : List Operation}
    (filled : fillEach (Operation.fill typeTable) package.operations = some operations)
    (matched : mismatches Vocabulary.table package = []) :
    (model Vocabulary.table package).DomainLaws (operations.map (·.signature)) := by
  intro row domain inputs outputs isRow arguments
  -- The row of the filled table and the row of the package that it fills.
  rw [List.getElem?_map] at isRow
  cases atFilled : operations[row]? with
  | none => rw [atFilled] at isRow; cases isRow
  | some filledRow =>
  rw [atFilled] at isRow
  have signatureEq : filledRow.signature = ⟨inputs, outputs, .restricted (some domain)⟩ :=
    Option.some.inj isRow
  obtain ⟨given, atGiven, fills⟩ := fillEach_getElem? filled atFilled
  obtain ⟨kindEq, fillsInputs, fillsOutputs⟩ := fill_signature fills
  rw [signatureEq] at kindEq fillsInputs fillsOutputs
  -- The package's row is the vocabulary's: `field.nonzero` at a field, with its domain row.
  obtain ⟨statics, signature, read, found, sameKinds, sameInputs, sameOutputs⟩ :=
    mismatch_none (List.filterMap_eq_nil_iff.mp matched given (List.mem_of_getElem? atGiven))
  rw [← kindEq] at sameKinds
  obtain ⟨domainName, domainRow, kind, atDomain, domainNamed, domainStatics⟩ :=
    sameKind_restricted sameKinds
  obtain ⟨named, domainIs, closed, rfl, inputsEq, outputsEq⟩ := signature_restricted found kind
  rw [inputsEq] at sameInputs
  rw [outputsEq] at sameOutputs
  obtain ⟨inputType, _, givenInputs, _, _⟩ := sameTypes_one sameInputs
  obtain ⟨outputType, outputClosed, givenOutputs, readOutput, outputSame⟩ := sameTypes_one sameOutputs
  obtain ⟨_, rfl⟩ := nonzero_of_beq outputSame
  obtain ⟨outputRow, rfl⟩ := nominal_of_nonzero _ _ readOutput
  rw [givenInputs] at fillsInputs
  rw [givenOutputs] at fillsOutputs
  obtain ⟨filledInput, rfl⟩ := fillAll_one fillsInputs
  have outputsAre := fillAll_nominal fillsOutputs
  subst outputsAre
  -- What the two rows compute.
  obtain rfl : domainName = "field.is_nonzero" := Option.some.inj domainIs
  have readDomain : argumentsOf package.types.toArray domainRow.identity = some [.type closed] := by
    unfold argumentsOf at read ⊢
    rw [domainStatics]
    exact read
  change Values Concrete.Value [filledInput] at arguments
  have restricted := model_restricted Vocabulary.table package row [filledInput]
    [.nominal outputRow] arguments atGiven
  have domainGives := model_pure Vocabulary.table package domain [filledInput] [.bool]
    allPopulated_bool arguments atDomain
  rw [applyOperation_read _ read, named, Concrete.toData_one, applyRow_nonzero] at restricted
  rw [applyOperation_read _ readDomain, domainNamed, Concrete.toData_one, applyRow_isNonzero]
    at domainGives
  rw [restricted, domainGives]
  cases elementOf Vocabulary.table closed with
  | none => exact (Ty.inhabitants_bool _ _).symm
  | some element =>
    cases zero : element.isZero (Concrete.toDatum filledInput (arguments.get .here)) with
    | true =>
      simp only [zero, ↓reduceIte, Bool.not_true, Concrete.ofData_bool, Concrete.Datum.toBool_ofBool]
      rfl
    | false =>
      simp only [zero, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Concrete.ofData_nominal,
        Concrete.ofData_bool, Concrete.Datum.toBool_ofBool]
      rfl

/-- The operation table of the typed package of a raw one is the raw table, its types read in
the type table. -/
theorem elaborate_table {package : Raw.Package} {typed : Typed}
    (elaborated : elaborate package = .ok typed) :
    fillEach (Operation.fill (typeTableOf package.types package.records package.variants))
      package.operations = some typed.table := by
  unfold elaborate at elaborated
  cases fillsTypes : fillEach (CatalogueRow.fill
      (typeTableOf package.types package.records package.variants)) package.types with
  | none => simp [fillsTypes] at elaborated
  | some types =>
    cases fillsOperations : fillEach (Operation.fill
        (typeTableOf package.types package.records package.variants)) package.operations with
    | none => simp [fillsTypes, fillsOperations] at elaborated
    | some operations =>
      simp only [fillsTypes, fillsOperations] at elaborated
      revert elaborated
      repeat' split
      all_goals intro elaborated
      all_goals first | (cases elaborated; rfl) | cases elaborated

/-- The model of the vocabulary satisfies the domain laws of the operation table of a package
that the core elaborates and whose rows are the vocabulary's; a package that the vocabulary
admits is one (`mismatches_of_admitted`). With it, the statements that take the domain laws of a
model (a function, a protocol for a side and the program of a role that pass the check of facts
never stop `undefined`) hold of the model that runs the package. -/
theorem model_domainLaws {package : Raw.Package} {typed : Typed}
    (elaborated : elaborate package = .ok typed)
    (matched : mismatches Vocabulary.table package = []) :
    (model Vocabulary.table package).DomainLaws (typed.table.map (·.signature)) :=
  model_domainLaws_of_filled (elaborate_table elaborated) matched

end DomainLaws

/-! ## The rows of the layout in the model of a package

What the rows of the canonical layout compute on typed values, in the model that runs a package
whose rows are the vocabulary's. A writer, a reader and a proof are bytes. The row that puts a
value appends the bytes that the format of the type writes for it, and the row that takes a
value, on those bytes followed by anything, gives the flag `true`, the value and what follows.
Nothing here speaks of a transcript. -/

section LayoutRows

/-- A pure row of the model of a package, when the row of the package is the vocabulary's row of
a name at static arguments and that row gives the data of typed values: those values. -/
theorem model_pure_applied (table : Table) (package : Raw.Package) {row : Nat}
    {operation : Operation} {name : String} {statics : List Value}
    (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = name)
    (read : argumentsOf package.types.toArray operation.identity = some statics)
    {inputs outputs : List Ty} (populated : Ty.allPopulated outputs = true)
    (arguments : Values Concrete.Value inputs) {values : Values Concrete.Value outputs}
    (applied : applyRow table name statics (Concrete.toData inputs arguments) =
      .ok (Concrete.toData outputs values)) :
    (model table package).pure ⟨row, inputs, outputs⟩ populated arguments = values := by
  rw [model_pure table package row inputs outputs populated arguments found,
    applyOperation_read _ read, named, applied]
  simp only [Concrete.ofData_toData, Option.getD_some]
  rfl

/-- The data of bytes. -/
private theorem toData_bytes (bytes : Bytes) :
    Concrete.toData [bytesType] (.cons bytes .nil) = [bytesDatum bytes] := by
  rw [Concrete.toData_one, Values.get_here, Concrete.toDatum_bytes]
  rfl

/-- The data of a writer and a value. -/
private theorem toData_put (writer : Bytes) {type : Ty} (value : Concrete.Value type) :
    Concrete.toData [bytesType, type] (.cons writer (.cons value .nil)) =
      [bytesDatum writer, Concrete.toDatum type value] := by
  rw [Concrete.toData_cons, Concrete.toData_one]
  simp only [Values.get_here, Values.tail, Concrete.toDatum_bytes]
  rfl

/-- The data of a flag, a value and the rest of a reader. -/
private theorem toData_taken (flag : Bool) {type : Ty} (value : Concrete.Value type)
    (rest : Bytes) :
    Concrete.toData [.bool, type, bytesType] (.cons flag (.cons value (.cons rest .nil))) =
      [Datum.ofBool flag, Concrete.toDatum type value, bytesDatum rest] := by
  rw [Concrete.toData_cons, Concrete.toData_cons, Concrete.toData_one]
  simp only [Values.get_here, Values.tail, Concrete.toDatum_bytes, Concrete.toDatum_bool]
  rfl

/-- The names of the rows of the layout are not names of rows of a suite. -/
private theorem layout_not_suite (name member : String)
    (differs : (Vocabulary.table.modules.all fun entry => name != entry.row ++ "." ++ member) = true) :
    merlinSuite? Vocabulary.table name member = none :=
  merlinSuite?_none name member differs

/-- The row that opens a writer gives no bytes. -/
theorem applyRow_open :
    applyRow Vocabulary.table "layout.canonical.open" [] [] = .ok [bytesDatum []] := by
  simp [applyRow, applyBytes, applyWritten,
    layout_not_suite "layout.canonical.open" "start" (by decide +kernel),
    layout_not_suite "layout.canonical.open" "absorb" (by decide +kernel),
    layout_not_suite "layout.canonical.open" "derive" (by decide +kernel)]

/-- The row that closes a writer gives its bytes, the proof. -/
theorem applyRow_close (writer : Datum) :
    applyRow Vocabulary.table "layout.canonical.close" [] [writer] = .ok [writer] := by
  simp [applyRow, applyBytes, applyWritten,
    layout_not_suite "layout.canonical.close" "start" (by decide +kernel),
    layout_not_suite "layout.canonical.close" "absorb" (by decide +kernel),
    layout_not_suite "layout.canonical.close" "derive" (by decide +kernel)]

/-- The row that opens a reader on a proof gives its bytes. -/
theorem applyRow_read (proof : Datum) :
    applyRow Vocabulary.table "layout.canonical.read" [] [proof] = .ok [proof] := by
  simp [applyRow, applyBytes, applyWritten,
    layout_not_suite "layout.canonical.read" "start" (by decide +kernel),
    layout_not_suite "layout.canonical.read" "absorb" (by decide +kernel),
    layout_not_suite "layout.canonical.read" "derive" (by decide +kernel)]

/-- The row that tests a reader says whether no byte is left. -/
theorem applyRow_exhausted (reader : Datum) :
    applyRow Vocabulary.table "layout.canonical.exhausted" [] [reader] =
      .ok [Datum.ofBool reader.items.isEmpty] := by
  simp [applyRow, applyBytes, applyWritten,
    layout_not_suite "layout.canonical.exhausted" "start" (by decide +kernel),
    layout_not_suite "layout.canonical.exhausted" "absorb" (by decide +kernel),
    layout_not_suite "layout.canonical.exhausted" "derive" (by decide +kernel)]

/-- The row that puts a value of a type with a format is the writer's row of the format. -/
theorem applyRow_put {closed : Closed} {format : Format Datum}
    (built : formatOf Vocabulary.table closed = some format) (writer value : Datum) :
    applyRow Vocabulary.table "layout.canonical.put" [.type closed] [writer, value] =
      putRow format writer value := by
  simp [applyRow, applyBytes, applyWritten, withFormat, typeArgument, built,
    layout_not_suite "layout.canonical.put" "start" (by decide +kernel),
    layout_not_suite "layout.canonical.put" "absorb" (by decide +kernel),
    layout_not_suite "layout.canonical.put" "derive" (by decide +kernel)]

/-- The row that takes a value of a type with a format is the reader's row of the format, under
the limit when one is given. -/
theorem applyRow_take {closed : Closed} {format : Format Datum}
    (built : formatOf Vocabulary.table closed = some format) (limit : Option Nat)
    (reader : Datum) :
    applyRow Vocabulary.table "layout.canonical.take" [.type closed] [reader] limit =
      takeRow Vocabulary.table closed format limit reader := by
  simp [applyRow, applyBytes, withFormat, typeArgument, built]

variable {package : Raw.Package} {row : Nat} {operation : Operation}

/-- In the model of a package, the row that opens a writer gives no bytes. -/
theorem model_open (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = "layout.canonical.open")
    (read : argumentsOf package.types.toArray operation.identity = some [])
    (populated : Ty.allPopulated [bytesType] = true) :
    (model Vocabulary.table package).pure ⟨row, [], [bytesType]⟩ populated .nil =
      .cons ([] : Bytes) .nil :=
  model_pure_applied Vocabulary.table package found named read populated
    (.nil : Values Concrete.Value [])
    (values := (.cons [] .nil : Values Concrete.Value [bytesType]))
    (by rw [Concrete.toData_nil, applyRow_open, toData_bytes])

/-- In the model of a package, the row that closes a writer gives its bytes, the proof. -/
theorem model_close (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = "layout.canonical.close")
    (read : argumentsOf package.types.toArray operation.identity = some [])
    (populated : Ty.allPopulated [bytesType] = true) (writer : Bytes) :
    (model Vocabulary.table package).pure ⟨row, [bytesType], [bytesType]⟩ populated
      (.cons writer .nil) = .cons writer .nil :=
  model_pure_applied Vocabulary.table package found named read populated
    (.cons writer .nil : Values Concrete.Value [bytesType])
    (values := (.cons writer .nil : Values Concrete.Value [bytesType]))
    (by rw [toData_bytes, applyRow_close])

/-- In the model of a package, the row that opens a reader on a proof gives its bytes. -/
theorem model_read (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = "layout.canonical.read")
    (read : argumentsOf package.types.toArray operation.identity = some [])
    (populated : Ty.allPopulated [bytesType] = true) (proof : Bytes) :
    (model Vocabulary.table package).pure ⟨row, [bytesType], [bytesType]⟩ populated
      (.cons proof .nil) = .cons proof .nil :=
  model_pure_applied Vocabulary.table package found named read populated
    (.cons proof .nil : Values Concrete.Value [bytesType])
    (values := (.cons proof .nil : Values Concrete.Value [bytesType]))
    (by rw [toData_bytes, applyRow_read])

/-- In the model of a package, the row that tests a reader says whether no byte is left. -/
theorem model_exhausted (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = "layout.canonical.exhausted")
    (read : argumentsOf package.types.toArray operation.identity = some [])
    (populated : Ty.allPopulated [.bool] = true) (reader : Bytes) :
    (model Vocabulary.table package).pure ⟨row, [bytesType], [.bool]⟩ populated
      (.cons reader .nil) = .cons reader.isEmpty .nil :=
  model_pure_applied Vocabulary.table package found named read populated
    (.cons reader .nil : Values Concrete.Value [bytesType])
    (values := (.cons reader.isEmpty .nil : Values Concrete.Value [.bool])) (by
    rw [toData_bytes, applyRow_exhausted, Concrete.toData_one, Values.get_here,
      Concrete.toDatum_bool]
    simp [bytesDatum, Datum.items])

/-- In the model of a package, the row that puts a value of the domain of the format of its type
on a writer gives the bytes written so far, followed by the bytes that the format writes for the
value. -/
theorem model_put (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = "layout.canonical.put")
    {closed : Closed} {format : Format Datum}
    (read : argumentsOf package.types.toArray operation.identity = some [.type closed])
    (built : formatOf Vocabulary.table closed = some format) (lawful : format.Lawful)
    {type : Ty} (populated : Ty.allPopulated [bytesType] = true) (writer : Bytes)
    (value : Concrete.Value type)
    (inDomain : format.domain (Concrete.toDatum type value) = true) :
    (model Vocabulary.table package).pure ⟨row, [bytesType, type], [bytesType]⟩ populated
      (.cons writer (.cons value .nil)) =
        .cons (writer ++ format.write (Concrete.toDatum type value)) .nil :=
  model_pure_applied Vocabulary.table package found named read populated
    (.cons writer (.cons value .nil) : Values Concrete.Value [bytesType, type])
    (values := (.cons (writer ++ format.write (Concrete.toDatum type value)) .nil :
      Values Concrete.Value [bytesType])) (by
    rw [toData_put, toData_bytes, applyRow_put built]
    exact putRow_written lawful writer inDomain)

/-- In the model of a package, the row that takes a value, on a reader that is the bytes which
the format of the type writes for a value of its domain, followed by anything, gives the flag
`true`, the value and what follows. -/
theorem model_take (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = "layout.canonical.take")
    {closed : Closed} {format : Format Datum}
    (read : argumentsOf package.types.toArray operation.identity = some [.type closed])
    (built : formatOf Vocabulary.table closed = some format) (lawful : format.Lawful)
    {type : Ty} (populated : Ty.allPopulated [.bool, type, bytesType] = true)
    (value : Concrete.Value type)
    (inDomain : format.domain (Concrete.toDatum type value) = true) (rest : Bytes) :
    (model Vocabulary.table package).pure ⟨row, [bytesType], [.bool, type, bytesType]⟩ populated
      (.cons (format.write (Concrete.toDatum type value) ++ rest) .nil) =
        .cons true (.cons value (.cons rest .nil)) :=
  model_pure_applied Vocabulary.table package found named read populated
    (.cons (format.write (Concrete.toDatum type value) ++ rest) .nil :
      Values Concrete.Value [bytesType])
    (values := (.cons true (.cons value (.cons rest .nil)) :
      Values Concrete.Value [.bool, type, bytesType])) (by
    rw [toData_bytes, toData_taken, applyRow_take built]
    exact takeRow_written Vocabulary.table closed lawful inDomain rest)

end LayoutRows

end Zkc.Core.Vocabulary
