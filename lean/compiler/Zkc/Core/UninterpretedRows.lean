module

public import Zkc.Core.RunComparison

@[expose] public section

/-! A second provider of runs, in which the rows of the vocabulary are uninterpreted.

It satisfies no law of the vocabulary and is used only to compare two programs: two emissions
of one source, or a package and a change of it. A row applied to terms is a term, equality is
equality of terms, and a coin is a term of its event. So every row of an admitted package runs,
also where the arithmetic of the vocabulary's model does not compute it or would take long, and
a run costs one digest per row.

**Terms.** A value of a nominal type is a term, encoded as a datum: the number of a 128-bit
digest of the term's structure, so that a term of any size is one number and two terms are the
same datum exactly when they are built alike (up to a collision of the digest). The terms are:

- an **input**: an atom keyed by the position of its port and its place inside the port's type;
- a **coin**: an atom keyed by the key of its site in the source, its count at the site and its
  place inside the law's type;
- a **literal**: an atom keyed by its type (by catalogue name, not by its number in the
  package) and its numbers;
- the **result of a row**: the application of the row, by its catalogue name and static
  arguments (never its number in the package), to the data of its arguments; a nominal part of
  an output is the projection of the application at the place of the part. The two arguments of
  a row whose name ends in `.add`, `.mul` or `.equal` and whose two inputs have one type are put
  in a fixed order first, so that `a + b` and `b + a` are one term.

**Answers of the types the core fixes.** A part of a row's output of a type the core fixes is a
deterministic function of the seed, the application and the place: a `bool` a bit of a digest,
a natural below 1024, an index below its bound, a collection without a size of fewer than four
elements, an alternative of a variant. So a predicate has the same answer in two programs that
apply it to the same terms, and both of its answers are reached over the seeds. Under every
seed an equality row (a name that ends in `.equal`, two inputs of one type) applied to two equal
arguments gives `true`. Under a seed below `trueSeeds` (seed 0 alone by default) every equality
gives `true`, so that a run passes every guard that is an equality of values of nominal types;
another row that gives a `bool` (`field.is_nonzero`, whose negation is how `x == 0` is written)
gives `true` under an even such seed and `false` under an odd one. A restricted row always has
its value.

**Inputs and coins.** Atoms at nominal types; the naturals, `bool`s, indices, sizes of
collections and alternatives of variants drawn as `ValidData` draws them. Nothing is validated
by the vocabulary, no row is missing, and no run reaches a limit.

**What a comparison under it sees, and does not.** Two programs whose roles send, hear or
return different terms differ; two whose runs build different terms at a guard differ there
under half the seeds. A mistake in the arithmetic of the vocabulary's model is not seen. And
two programs that compute equal values by different terms (`x * 2` and `x + x`, `a - b == c`
and `a == b + c`, `seq.add` and a loop of `field.add`) differ under it: a program that emits
what the source says does not produce them, and a difference of that kind is read.

No statement is true or false under it, so a generator of true statements is not used: the
inputs are atoms, and seed 0 passes every equality.

Constructed schemes are not run under it. The rows of a transcript (`start`, `absorb`,
`derive`) are uninterpreted as any row, but a proof is the bytes that the layout's `put` writes
and the verifier's `take` reads back: an uninterpreted `take` gives a fresh term, not the value
written, so the verifier would check terms unrelated to the prover's.
-/

set_option autoImplicit false

namespace Zkc.Core.UninterpretedRows

open Zkc.Source
open Zkc.Core.Concrete (Datum)
open Vocabulary
open RunComparison

/-! ## Digests -/

/-- A 64-bit mixing step (the finaliser of SplitMix64). -/
def mix64 (x : UInt64) : UInt64 :=
  let x := x + 0x9e3779b97f4a7c15
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

/-- A digest in two lanes of 64 bits, each absorbing the same words by a different step. -/
structure Digest where
  first : UInt64
  second : UInt64
  deriving BEq, Inhabited

def Digest.start (tag : Nat) : Digest :=
  ⟨mix64 (0x6a09e667f3bcc908 + tag.toUInt64), mix64 (0xbb67ae8584caa73b ^^^ tag.toUInt64)⟩

def Digest.word (digest : Digest) (word : UInt64) : Digest :=
  ⟨mix64 (digest.first ^^^ word), mix64 (digest.second + mix64 (word ^^^ 0x3c6ef372fe94f82b))⟩

def Digest.digest (digest other : Digest) : Digest := (digest.word other.first).word other.second

def Digest.toNat (digest : Digest) : Nat := digest.first.toNat * 2 ^ 64 + digest.second.toNat

def Digest.less (left right : Digest) : Bool :=
  left.first < right.first || (left.first == right.first && left.second < right.second)

/-- The 64-bit limbs of a number, least significant first. -/
partial def limbs (value : Nat) : List UInt64 :=
  if value < 2 ^ 64 then [value.toUInt64] else (value % 2 ^ 64).toUInt64 :: limbs (value / 2 ^ 64)

def Digest.nat (digest : Digest) (value : Nat) : Digest :=
  let parts := limbs value
  parts.foldl Digest.word (digest.word parts.length.toUInt64)

def Digest.nats (digest : Digest) (values : List Nat) : Digest :=
  values.foldl Digest.nat (digest.word values.length.toUInt64)

/-- A datum, by its shape: a number, or a sequence of its items. -/
partial def Digest.datum (digest : Digest) : Datum → Digest
  | .number value => (digest.word 0xa1).nat value
  | .sequence items => items.foldl Digest.datum ((digest.word 0xa2).word items.length.toUInt64)

def digestOf (datum : Datum) : Digest := (Digest.start 0).datum datum

mutual
  /-- A type, its nominal rows by their catalogue names and static arguments, and a record or
  a variant by its fields or alternatives (not by the number of its declaration). -/
  partial def Digest.type (types : Array CatalogueRow) (depth : Nat) (digest : Digest) : Ty → Digest
    | .bool => digest.word 1
    | .nat => digest.word 2
    | .fin bound => (digest.word 3).nat bound
    | .nominal row =>
      match types[row]?, depth with
      | some entry, depth + 1 => Digest.statics types depth ((digest.word 4).nats entry.name) entry.statics
      | _, _ => (digest.word 9).nat row
    | .seq element size =>
      let inner := Digest.type types depth (digest.word 5) element
      match size with
      | some count => (inner.word 1).nat count
      | none => inner.word 0
    | .tuple components => components.foldl (Digest.type types depth) ((digest.word 6).word components.length.toUInt64)
    | .record _ _ fields => fields.foldl (Digest.type types depth) ((digest.word 7).word fields.length.toUInt64)
    | .variant _ alternatives =>
      alternatives.foldl (Digest.type types depth) ((digest.word 8).word alternatives.length.toUInt64)

  partial def Digest.statics (types : Array CatalogueRow) (depth : Nat) (digest : Digest) (statics : List Static) :
      Digest :=
    statics.foldl (init := digest.word statics.length.toUInt64) fun digest static =>
      match static with
      | .domain name => (digest.word 1).nats name
      | .nat value => (digest.word 2).nat value
      | .type type => Digest.type types depth (digest.word 3) type
end

/-! ## The model -/

/-- The tags of the kinds of term. -/
def tagInput : Nat := 1
def tagCoin : Nat := 2
def tagLiteral : Nat := 3
def tagApplication : Nat := 4
def tagProjection : Nat := 5
def tagAnswer : Nat := 6

/-- What the model reads of a row of a package: the digest of its catalogue name and static
arguments, whether its two arguments are put in a fixed order, and whether it is an equality. -/
structure RowInfo where
  key : Digest
  commutative : Bool
  equality : Bool
  deriving Inhabited

/-- The rows of a package as the model reads them, by their numbers in the package. -/
def rowsOf (package : Raw.Package) : Array RowInfo :=
  let types := package.types.toArray
  package.operations.toArray.map fun operation =>
    let name := operation.identity.name.toString
    let sameInputs := match operation.signature.inputs with
      | [first, second] => first == second
      | _ => false
    { key := Digest.statics types (types.size + 1) ((Digest.start tagApplication).nats operation.identity.name)
        operation.identity.statics
      commutative := sameInputs && [".add", ".mul", ".equal"].any fun member => name.endsWith member
      equality := name.endsWith ".equal" && sameInputs }

/-- The digest of a part of an answer: the seed, the application and the place. -/
def answerDigest (seed : Nat) (application : Digest) (place : List Nat) : Digest :=
  ((Digest.start tagAnswer).nat seed |>.digest application).nats place

/-- The term of a nominal part of an answer: the projection of the application at the place. -/
def projection (application : Digest) (place : List Nat) : Datum :=
  .number (((Digest.start tagProjection).digest application).nats place).toNat

/-- A part of the answer of a row, by its type, at a place: see the module's description. -/
partial def shape (seed : Nat) (application : Digest) (forced : Option Bool) :
    Ty → List Nat → Datum
  | .bool, place =>
    Datum.ofBool (forced.getD ((answerDigest seed application place).first % 2 == 1))
  | .nat, place => .number ((answerDigest seed application place).first.toNat % 1024)
  | .fin bound, place =>
    .number (if bound == 0 then 0 else (answerDigest seed application place).toNat % bound)
  | .nominal _, place => projection application place
  | .seq element (some count), place =>
    .sequence ((List.range count).map fun index => shape seed application forced element (place ++ [index]))
  | .seq element none, place =>
    let count := (answerDigest seed application place).first.toNat % 4
    .sequence ((List.range count).map fun index => shape seed application forced element (place ++ [index]))
  | .tuple components, place | .record _ _ components, place =>
    .sequence (components.zipIdx.map fun (component, index) =>
      shape seed application forced component (place ++ [index]))
  | .variant _ alternatives, place =>
    let populated := alternatives.zipIdx.filter (·.1.populated)
    if populated.isEmpty then .sequence []
    else
      let (payload, position) := populated[(answerDigest seed application place).toNat % populated.length]!
      .sequence [.number position, shape seed application forced payload (place ++ [position])]

/-- The answer of a row on the data of its arguments: one datum per output. -/
def answer (rows : Array RowInfo) (seed trueSeeds : Nat) (row : OperationRow)
    (inputs : List Datum) : List Datum :=
  let info := rows[row.row]?.getD { key := (Digest.start 99).nat row.row, commutative := false, equality := false }
  let arguments := inputs.map digestOf
  let arguments := match info.commutative, arguments with
    | true, [first, second] => if second.less first then [second, first] else arguments
    | _, _ => arguments
  let application := arguments.foldl Digest.digest info.key
  let equal := match info.equality, arguments with
    | true, [first, second] => first == second
    | _, _ => false
  -- an equality of equal arguments is `true`; under a seed below `trueSeeds` an equality is
  -- `true`, and another row that gives a `bool` (`field.is_nonzero`) is `true` under an even
  -- seed and `false` under an odd one
  let forced : Option Bool :=
    if equal then some true
    else if seed < trueSeeds then some (info.equality || seed % 2 == 0)
    else none
  row.outputs.zipIdx.map fun (type, index) => shape seed application forced type [index]

/-- The term of a literal of a nominal type: its type and its numbers. -/
def literalTerm (types : Array CatalogueRow) (row : Nat) (data : List Nat) : Datum :=
  .number ((Digest.type types (types.size + 1) (Digest.start tagLiteral) (.nominal row)).nats data).toNat

/-- The model of a package's rows under a seed. Its carrier is the concrete one. -/
def modelWith (types : Array CatalogueRow) (rows : Array RowInfo) (seed trueSeeds : Nat) :
    Model where
  Carrier := Concrete.Carrier
  pure row populated arguments :=
    let fallback := Ty.inhabitants (fun _ => (default : Datum)) row.outputs populated
    (Concrete.ofData row.outputs (answer rows seed trueSeeds row (Concrete.toData row.inputs arguments))).getD
      fallback
  restricted row arguments :=
    Concrete.ofData row.outputs (answer rows seed trueSeeds row (Concrete.toData row.inputs arguments))
  «opaque» _ _ := .error .refused
  literal row data := literalTerm types row data

/-- What the provider is given: the seeds below `trueSeeds` answer `true` to every equality. -/
structure Settings where
  trueSeeds : Nat := 1
  deriving Inhabited

def model (package : Raw.Package) (seed : Nat) (settings : Settings) : Model :=
  modelWith package.types.toArray (rowsOf package) seed settings.trueSeeds

/-! ## Inputs and coins -/

/-- A value of a type: an atom at each nominal place (`atom` of the place), the leaves of the
types the core fixes drawn as `ValidData` draws them; with the position after it. -/
partial def freeValue (draw : ValidData.Draw) (atom : List Nat → Datum) :
    Ty → List Nat → Nat → Except String (Datum × Nat)
  | .bool, _, next =>
    .ok (ValidData.leaf draw [Datum.ofBool false, Datum.ofBool true] (fun n => Datum.ofBool (n % 2 == 1)) next)
  | .nat, _, next =>
    .ok (ValidData.leaf draw [.number 0, .number 1, .number 2, .number 255] (fun n => .number (n % 1024)) next)
  | .fin bound, _, next =>
    if bound == 0 then .error "`index<0>` has no value"
    else .ok (ValidData.leaf draw [.number 0, .number (1 % bound), .number (bound - 1)]
      (fun n => .number (n % bound)) next)
  | .nominal _, place, next => .ok (atom place, next)
  | .seq item size, place, next => do
    let (count, next) := match size with
      | some size => (size, next)
      | none => ValidData.unsizedLength draw next
    let (items, next) ← (List.range count).foldlM (init := (#[], next)) fun (items, next) index => do
      let (value, next) ← freeValue draw atom item (place ++ [index]) next
      return (items.push value, next)
    return (.sequence items.toList, next)
  | .tuple components, place, next | .record _ _ components, place, next => do
    let (items, next) ← components.zipIdx.foldlM (init := (#[], next)) fun (items, next) (component, index) => do
      let (value, next) ← freeValue draw atom component (place ++ [index]) next
      return (items.push value, next)
    return (.sequence items.toList, next)
  | .variant _ alternatives, place, next => do
    if alternatives.isEmpty then throw "a variant without an alternative has no value"
    let (position, next) := match draw with
      | .boundary index => (index % alternatives.length, next)
      | .mixed numbers | .taken numbers => (numbers next % alternatives.length, next + 1)
    let (payload, next) ← freeValue draw atom (alternatives[position]!) (place ++ [position]) next
    return (.sequence [.number position, payload], next)

/-- The atom of a place of an input port. -/
def inputAtom (port : Nat) (place : List Nat) : Datum :=
  .number (((Digest.start tagInput).nat port).nats place).toNat

/-- Values of the types of the inputs of a run, one per port, from one draw. -/
def inputs (draw : ValidData.Draw) (inputTypes : List Ty) : Except String (List Datum) := do
  let (data, _) ← inputTypes.zipIdx.foldlM (init := (#[], 0)) fun (data, next) (type, port) => do
    let (datum, next) ← freeValue draw (inputAtom port) type [] next
    return (data.push datum, next)
  return data.toList

/-- The `count`-th coin at a site whose key is given: atoms keyed by the key, the count and the
place; the other leaves drawn under the seed as `ValidData.coin` draws them. -/
def coin (seed : Nat) (key : List Nat) (count : Nat) (type : Ty) : Except String Datum :=
  let atom := fun place => Datum.number ((((Digest.start tagCoin).nats key).nat count).nats place).toNat
  (·.1) <$> freeValue (ValidData.Draw.ofSeed seed (key ++ [count])) atom type [] 0

def coinsOf (package : Raw.Package) (settings : Settings) (key : Site → Option (List Nat)) (seed : Nat) :
    Execute.Coins (model package seed settings) :=
  fun site count type =>
    match key site with
    | none => none
    | some found =>
      match coin seed found count type with
      | .ok datum => Execute.valueOf (model package seed settings) rfl type datum
      | .error _ => none

/-! ## Functions -/

/-- The run of the last function of an elaborated package on data under a seed. -/
def runFunction (package : Raw.Package) (typed : Typed) (settings : Settings) (seed : Nat)
    (data : List Datum) : Vocabulary.Run :=
  let m := model package seed settings
  match nthFunction typed.functions (typed.program.functionTable m) 0 with
  | none => .failed "the package has no function"
  | some ⟨header, meaning⟩ =>
    if data.length != header.inputs.length then
      .failed s!"the function takes {header.inputs.length} inputs; {data.length} are given"
    else
      match Concrete.ofData header.inputs data with
      | none => .failed "an input is not a value of its type"
      | some arguments =>
        match finish (meaning arguments) with
        | .error message => .failed message
        | .ok (.error reason) => .stopped reason
        | .ok (.ok values) => .returned (Concrete.toData header.outputs values)

/-! ## Protocols -/

/-- The process of a role of the newest protocol on the data of every port, returning its
outputs as data. -/
def roleProcess (package : Raw.Package) (typed : Typed) (settings : Settings) (seed : Nat)
    (data : List Datum) (role : Nat) :
    Except String (PIR.Process (Effects (model package seed settings)) (List Datum)) :=
  let m := model package seed settings
  match Execute.roleEntry m (typed.program.functionTable m) Identities.written role
      typed.program.protocols with
  | .error message => .error message
  | .ok ⟨header, program⟩ =>
    match Execute.roleValues m rfl (roleHeader role header).inputs
        (Execute.ownData role header.inputs data) with
    | none => .error "an input is not a value of its port's type"
    | some arguments =>
      .ok ((program [] arguments).bind fun values =>
        .done (Execute.roleData m rfl (roleHeader role header).outputs values))

/-- Every role of the newest protocol of a package run together on data, one datum per input
port: what each role shows. -/
def runProtocol (settings : Settings) (side : RunComparison.Side) (seed : Nat)
    (data : List Datum) : Except String (List Shown) := do
  let m := model side.package seed settings
  let some header := side.typed.protocols.head? | throw "the program has no protocol"
  let processes ← (List.range header.roles).mapM
    (roleProcess side.package side.typed settings seed data)
  let observed := Execute.observeRoles m rfl (coinsOf side.package settings side.key seed)
    processes none
  return (observed.outcomes.zip observed.did).map fun (ended, did) => shown side.key ended did

/-! ## The provider -/

/-- The provider of uninterpreted rows. -/
def provider (settings : Settings := {}) : Provider where
  name := "the model of uninterpreted rows"
  computes := false
  refuses _ := none
  inputs _ seed types := inputs (.ofSeed seed []) types
  function package _ :=
    match elaborate package with
    | .error refusal => .error s!"the core refuses the package: {reprStr refusal}"
    | .ok typed =>
      match typed.functions.head? with
      | none => .error "the package has no function"
      | some header => .ok (header, fun seed data => runFunction package typed settings seed data)
  protocol side seed data _ := runProtocol settings side seed data
  scheme := none

end Zkc.Core.UninterpretedRows
