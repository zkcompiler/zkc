module

public import Std.Data.HashMap

@[expose] public section

/-! The vocabulary: the types, the modules and the operation rows that exist outside the
source language, as one value.

A type of the vocabulary has a row name, the sorts it has (a sort is named as its interface
is in `zkc::algebra`), its type members and its natural members, and what its arithmetic is.
A module has a row name, the interface it implements, and its members. Each sort has a
default representative. An operation row has a catalogue name, the static arguments it
takes, its kind (a restricted row names the row that decides its domain), and its type,
stated in a small term language over its static arguments: `Term.at` gives the type at
given static arguments. Several rows may share a name when their static arguments differ
in kind: `field.mul` on a field and on the units of a field. The sampling row `law.uniform`
takes a type that is a law (TY15 of the reference), a tuple or a collection of laws included,
and gives a value of it.

A catalogue suite that the Fiat–Shamir step can apply has, beside its module, a transcript type
and a label type and three rows, each named by the suite's row and a member: `start` from the
proof identity, `absorb` at a type, `derive` at a law. The suite
`suite.merlin3.bls12-381.fr64be/0` has them. The layout `zkc::layout::canonical` has the six rows
of the serialize step, named `layout.canonical.*`, over bytes: `open`, `put` at a type, `close`,
`read`, `take` at a type, which gives a flag, a value and the rest, and `exhausted`.

The numbers of the types:

- `koala-bear`: the order `2130706433 = 2^31 - 2^24 + 1` and the two-adicity 24, with the
  generator `1791270792` of the subgroup of order `2^24` (the catalogue entry `koala-bear`);
- `koala-bear.ext4`: degree 4 over `koala-bear` with `x^4 = 3` (entry
  `koala-bear.ext4-binomial3`); its order is `p^4`, and its two-adicity 26 is the exponent
  of 2 in `p^4 - 1 = (p - 1)(p + 1)(p^2 + 1)`: 24 + 1 + 1. The catalogue gives no generator
  of its two-adic subgroup;
- `bls12-381.fr`: the order `r` of the catalogue entry `bls12-381.fr`; its two-adicity 32 is
  the exponent of 2 in `r - 1`; an element is 32 bytes. The catalogue gives no generator of
  its two-adic subgroup;
- `bls12-381.g1`, `.g2`, `.gt`: the groups of order `r` with the scalar `bls12-381.fr`.
-/

set_option autoImplicit false

namespace Zkc.Core.Vocabulary

mutual
  /-- A natural in a type term: a number, a natural static argument, a natural member of a
  type, or one more than a natural. -/
  inductive Size where
    | number (value : Nat)
    | argument (position : Nat)
    | member (type : Term) (name : String)
    | succ (size : Size)
    deriving Repr, Inhabited, BEq

  /-- A type term over the static arguments of a row. -/
  inductive Term where
    | bool
    | nat
    | index (bound : Size)
    | nonzero (field : Term)
    | seq (element : Term) (size : Option Size)
    /-- The type static argument at a position. -/
    | argument (position : Nat)
    /-- A type member of a type. -/
    | member (type : Term) (name : String)
    /-- A type of the vocabulary. -/
    | row (name : String)
    deriving Repr, Inhabited, BEq
end

/-- A closed type of the vocabulary. -/
inductive Closed where
  | bool
  | nat
  | index (bound : Nat)
  | nonzero (field : Closed)
  | seq (element : Closed) (size : Option Nat)
  | tuple (components : List Closed)
  | row (name : String)
  deriving Repr, Inhabited, Hashable

mutual
  /-- Equality of closed types, by structural recursion so that the kernel computes it. -/
  def Closed.beq : Closed → Closed → Bool
    | .bool, .bool => true
    | .nat, .nat => true
    | .index a, .index b => a == b
    | .nonzero a, .nonzero b => Closed.beq a b
    | .seq a m, .seq b n => Closed.beq a b && m == n
    | .tuple as, .tuple bs => Closed.beqList as bs
    | .row a, .row b => a == b
    | _, _ => false

  def Closed.beqList : List Closed → List Closed → Bool
    | [], [] => true
    | a :: as, b :: bs => Closed.beq a b && Closed.beqList as bs
    | _, _ => false
end

instance : BEq Closed := ⟨Closed.beq⟩

/-- A static argument of a row: a closed type or a natural. -/
inductive Value where
  | type (type : Closed)
  | natural (value : Nat)
  deriving Repr, Inhabited, BEq

/-- What the arithmetic of a type is. -/
inductive Arithmetic where
  /-- The naturals below the natural member `Order`. -/
  | primeField
  /-- Polynomials over the type member `Base` modulo `x^Degree - nonresidue`. -/
  | extension (nonresidue : Nat)
  /-- The points of BLS12-381 G1. -/
  | curveG1
  /-- None that the model implements. -/
  | none
  deriving Repr, Inhabited, BEq

/-- A type of the vocabulary. -/
structure TypeEntry where
  row : String
  sorts : List String
  typeMembers : List (String × Term)
  naturalMembers : List (String × Nat)
  arithmetic : Arithmetic
  /-- A generator of the subgroup of order `2^TwoAdicity`, when the catalogue gives one. -/
  twoAdicGenerator : Option Nat := none
  deriving Repr, Inhabited

/-- A module of the vocabulary: the interface it implements, by its path (`zkc::hash::Hash`),
and its members. A row that a project binds has no interface in the table. -/
structure ModuleEntry where
  row : String
  implements : Option String
  typeMembers : List (String × Term)
  naturalMembers : List (String × Nat)
  deriving Repr, Inhabited

/-- What a static argument of a row is. -/
inductive Parameter where
  /-- A type, of the sort when one is named. -/
  | type (sort : Option String)
  /-- `nonzero<T>`, for a type `T` of the sort. -/
  | units (sort : String)
  | natural
  /-- A type that is a law (TY15). -/
  | law
  deriving Repr, Inhabited, BEq

/-- The kind of a row. A restricted row names its domain row: the row of that name at the same
static arguments, pure, with the same inputs and one `bool` output. A sampling row is a law: the
uniform distribution on its output type, which the sampler of a run draws from. -/
inductive Kind where
  | pure
  | restricted (domain : Option String)
  | sampling
  deriving Repr, Inhabited, BEq

/-- An operation row. -/
structure RowEntry where
  name : String
  parameters : List Parameter
  kind : Kind
  inputs : List Term
  outputs : List Term
  deriving Repr, Inhabited

/-- The vocabulary. -/
structure Table where
  types : List TypeEntry
  modules : List ModuleEntry
  /-- For each sort, the row of its default representative. -/
  representatives : List (String × String)
  rows : List RowEntry
  deriving Inhabited

namespace Table

def type? (table : Table) (row : String) : Option TypeEntry := table.types.find? (·.row == row)

def module? (table : Table) (row : String) : Option ModuleEntry :=
  table.modules.find? (·.row == row)

def representative? (table : Table) (sort : String) : Option String :=
  (table.representatives.find? (·.1 == sort)).map (·.2)

/-- Whether a closed type has a sort: a type of the vocabulary that the table gives it; a sized
collection of elements of a `Group` is a `Group`. -/
def hasSort (table : Table) : Closed → String → Bool
  | .row name, sort => (table.type? name).any (·.sorts.contains sort)
  | .seq element (some _), sort => sort == "Group" && table.hasSort element "Group"
  | _, _ => false

mutual
  /-- Whether a closed type is a law (TY15): finite with a value. `bool`, an `index<n>` with
  `0 < n`, a field, `nonzero<F>`, a type of sort `Group`, a tuple of laws, `[L; n]` with `L` a
  law or `n == 0`. -/
  def isLaw (table : Table) : Closed → Bool
    | .bool => true
    | .nat => false
    | .index bound => 0 < bound
    | .nonzero field => table.hasSort field "Field"
    | .seq element (some size) => size == 0 || table.isLaw element
    | .seq _ none => false
    | .tuple components => table.allLaws components
    | .row name => table.hasSort (.row name) "Field" || table.hasSort (.row name) "Group"

  def allLaws (table : Table) : List Closed → Bool
    | [] => true
    | component :: rest => table.isLaw component && table.allLaws rest
end

end Table

/-! ## Types at static arguments -/

mutual
  /-- A type term at static arguments, within `depth` steps: each step reads one part of the
  term or one member of a type. -/
  def Term.within (table : Table) (arguments : List Value) : Nat → Term → Option Closed
    | 0, _ => none
    | _ + 1, .bool => some .bool
    | _ + 1, .nat => some .nat
    | depth + 1, .index bound => (bound.within table arguments depth).map .index
    | depth + 1, .nonzero field => (field.within table arguments depth).map .nonzero
    | depth + 1, .seq element size => do
      let element ← element.within table arguments depth
      match size with
      | some size => return .seq element (some (← size.within table arguments depth))
      | none => return .seq element none
    | _ + 1, .argument position =>
      match arguments[position]? with
      | some (.type type) => some type
      | _ => none
    | depth + 1, .member type name => do
      let .row row ← type.within table arguments depth | none
      let entry ← table.type? row
      let (_, member) ← entry.typeMembers.find? (·.1 == name)
      member.within table [] depth
    | _ + 1, .row name => some (.row name)

  /-- A natural of a term at static arguments, within `depth` steps. -/
  def Size.within (table : Table) (arguments : List Value) : Nat → Size → Option Nat
    | 0, _ => none
    | _ + 1, .number value => some value
    | _ + 1, .argument position =>
      match arguments[position]? with
      | some (.natural value) => some value
      | _ => none
    | depth + 1, .member type name => do
      let .row row ← type.within table arguments depth | none
      let entry ← table.type? row
      let (_, member) ← entry.naturalMembers.find? (·.1 == name)
      return member
    | depth + 1, .succ size => (size.within table arguments depth).map (· + 1)
end

/-- The steps that a term of the table needs at most. -/
def depth : Nat := 16

/-- A type term at static arguments. -/
def Term.at (table : Table) (arguments : List Value) (term : Term) : Option Closed :=
  term.within table arguments depth

/-- Whether static arguments are of the kinds a row takes. -/
def Parameter.accepts (table : Table) : Parameter → Value → Bool
  | .type none, .type _ => true
  | .type (some sort), .type closed => table.hasSort closed sort
  | .units sort, .type (.nonzero field) => table.hasSort field sort
  | .natural, .natural _ => true
  | .law, .type closed => table.isLaw closed
  | _, _ => false

/-- A row at static arguments: its kind and its type. -/
structure Signature where
  kind : Kind
  inputs : List Closed
  outputs : List Closed
  deriving Repr, Inhabited, BEq

namespace Table

/-- The entry of a row of this name whose parameters accept the static arguments. -/
def row? (table : Table) (name : String) (arguments : List Value) : Option RowEntry :=
  table.rows.find? fun entry =>
    entry.name == name && entry.parameters.length == arguments.length &&
      (entry.parameters.zip arguments).all fun (parameter, argument) => parameter.accepts table argument

/-- The signature of a row at static arguments, when the table has the row. -/
def signature? (table : Table) (name : String) (arguments : List Value) : Option Signature := do
  let entry ← table.row? name arguments
  let inputs ← entry.inputs.mapM (Term.at table arguments)
  let outputs ← entry.outputs.mapM (Term.at table arguments)
  return { kind := entry.kind, inputs, outputs }

end Table

/-! ## The table -/

def koalaBearOrder : Nat := 2130706433

/-- The order of the groups of BLS12-381 and the characteristic of its scalar field. -/
def bls12381Order : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

def self : Term := .argument 0

/-- A row on the type of its one static argument, of a sort. -/
def on (sort : String) (name : String) (inputs outputs : List Term)
    (kind : Kind := .pure) : RowEntry :=
  { name, parameters := [.type (some sort)], kind, inputs, outputs }

/-- A row on the units of a field: its one static argument is `nonzero<F>`. -/
def onUnits (name : String) (inputs outputs : List Term) : RowEntry :=
  { name, parameters := [.units "Field"], kind := .pure, inputs, outputs }

/-- A row on sized collections: its static arguments are the element type and the size. -/
def onSized (sort : Option String) (name : String) (inputs outputs : List Term) : RowEntry :=
  { name, parameters := [.type sort, .natural], kind := .pure, inputs, outputs }

def sized : Term := .seq self (some (.argument 1))

def scalar : Term := .member self "Scalar"

def byte : Term := .index (.number 256)

def bytes : Term := .seq byte none

/-- The rows of §7.4 of the reference that are not operations the core owns, the rows of the
units of a field, the function members of the sorts, and the rows that the core library's
modules bind. -/
def rows : List RowEntry := [
  -- a field
  on "Field" "field.add" [self, self] [self],
  on "Field" "field.sub" [self, self] [self],
  on "Field" "field.mul" [self, self] [self],
  on "Field" "field.neg" [self] [self],
  on "Field" "field.inverse" [.nonzero self] [.nonzero self],
  on "Field" "field.pow" [self, .nat] [self],
  on "Field" "field.equal" [self, self] [.bool],
  on "Field" "field.is_nonzero" [self] [.bool],
  on "Field" "field.nonzero" [self] [.nonzero self] (kind := .restricted (some "field.is_nonzero")),
  on "Field" "field.from_nonzero" [.nonzero self] [self],
  -- the units of a field
  onUnits "field.mul" [self, self] [self],
  onUnits "field.neg" [self] [self],
  onUnits "field.pow" [self, .nat] [self],
  -- a ring that is not a field: its `+`, `-` and `==` are those of the group
  on "Ring" "ring.mul" [self, self] [self],
  on "Ring" "ring.pow" [self, .nat] [self],
  -- a group
  on "Group" "group.zero" [] [self],
  on "Group" "group.add" [self, self] [self],
  on "Group" "group.sub" [self, self] [self],
  on "Group" "group.neg" [self] [self],
  on "Group" "group.scale" [self, scalar] [self],
  on "Group" "group.equal" [self, self] [.bool],
  -- collections
  onSized (some "Group") "seq.add" [sized, sized] [sized],
  onSized (some "Group") "seq.sub" [sized, sized] [sized],
  onSized (some "Group") "seq.scale" [sized, scalar] [sized],
  onSized none "seq.equal" [sized, sized] [.bool],
  { name := "seq.equal", parameters := [.type none], kind := .pure,
    inputs := [.seq self none, .seq self none], outputs := [.bool] },
  onSized (some "Group") "seq.sum" [sized] [self],
  { name := "seq.sum", parameters := [.type (some "Group")], kind := .pure,
    inputs := [.seq self none], outputs := [self] },
  onSized (some "Ring") "seq.product" [sized] [self],
  { name := "seq.product", parameters := [.type (some "Ring")], kind := .pure,
    inputs := [.seq self none], outputs := [self] },
  onSized (some "Group") "seq.inner" [sized, .seq scalar (some (.argument 1))] [self],
  -- the function members of the sorts
  on "PrimeOrderGroup" "group.generator" [] [self],
  on "Ring" "field.from_nat" [.nat] [self],
  on "PrimeField" "field.to_nat" [self] [.index (.member self "Order")],
  on "Field" "field.components" [self] [.seq (.member self "Prime") (some (.member self "Dimension"))],
  on "Field" "field.from_components" [.seq (.member self "Prime") (some (.member self "Dimension"))] [self],
  on "ExtensionField" "field.embed" [.member self "Base"] [self],
  on "ExtensionField" "field.coefficients" [self] [.seq (.member self "Base") (some (.member self "Degree"))],
  on "ExtensionField" "field.from_coefficients" [.seq (.member self "Base") (some (.member self "Degree"))] [self],
  on "TwoAdicField" "field.root" [.index (.succ (.member self "TwoAdicity"))] [.nonzero self],
  -- the rows of the modules of `zkc::hash`
  { name := "hash.sha256", parameters := [], kind := .pure,
    inputs := [.seq byte none], outputs := [.seq byte (some (.number 32))] },
  { name := "hash.keccak256", parameters := [], kind := .pure,
    inputs := [.seq byte none], outputs := [.seq byte (some (.number 32))] },
  { name := "hash.shake128", parameters := [.natural], kind := .pure,
    inputs := [.seq byte none], outputs := [.seq byte (some (.argument 0))] },
  { name := "hash.shake256", parameters := [.natural], kind := .pure,
    inputs := [.seq byte none], outputs := [.seq byte (some (.argument 0))] },
  -- the laws: the uniform distribution on a type that is a law, a tuple or a collection of laws
  -- included (TY15)
  { name := "law.uniform", parameters := [.law], kind := .sampling, inputs := [], outputs := [self] },
  -- the rows of the suite `suite.merlin3.bls12-381.fr64be/0` that the Fiat–Shamir step applies:
  -- the start from the proof identity, the absorption of a value of a type with a label, and the
  -- derivation of a value of a law with a label
  { name := "suite.merlin3.bls12-381.fr64be/0.start", parameters := [], kind := .pure
    inputs := [.row "suite.merlin3.bls12-381.fr64be/0.label"]
    outputs := [.row "suite.merlin3.bls12-381.fr64be/0.state"] },
  { name := "suite.merlin3.bls12-381.fr64be/0.absorb", parameters := [.type none], kind := .pure
    inputs := [.row "suite.merlin3.bls12-381.fr64be/0.state",
      .row "suite.merlin3.bls12-381.fr64be/0.label", self]
    outputs := [.row "suite.merlin3.bls12-381.fr64be/0.state"] },
  { name := "suite.merlin3.bls12-381.fr64be/0.derive", parameters := [.law], kind := .pure
    inputs := [.row "suite.merlin3.bls12-381.fr64be/0.state",
      .row "suite.merlin3.bls12-381.fr64be/0.label"]
    outputs := [self, .row "suite.merlin3.bls12-381.fr64be/0.state"] },
  -- the rows of the layout `zkc::layout::canonical` that the serialize step applies: a writer, a
  -- reader and a proof are bytes
  { name := "layout.canonical.open", parameters := [], kind := .pure, inputs := [], outputs := [bytes] },
  { name := "layout.canonical.put", parameters := [.type none], kind := .pure
    inputs := [bytes, self], outputs := [bytes] },
  { name := "layout.canonical.close", parameters := [], kind := .pure, inputs := [bytes], outputs := [bytes] },
  { name := "layout.canonical.read", parameters := [], kind := .pure, inputs := [bytes], outputs := [bytes] },
  { name := "layout.canonical.take", parameters := [.type none], kind := .pure
    inputs := [bytes], outputs := [.bool, self, bytes] },
  { name := "layout.canonical.exhausted", parameters := [], kind := .pure, inputs := [bytes],
    outputs := [.bool] }]

/-- The vocabulary. -/
def table : Table where
  types := [
    { row := "koala-bear", sorts := ["Group", "Ring", "Field", "PrimeField", "TwoAdicField"]
      typeMembers := [("Scalar", .row "koala-bear"), ("Prime", .row "koala-bear")]
      naturalMembers := [("Order", koalaBearOrder), ("Characteristic", koalaBearOrder),
        ("Dimension", 1), ("Bytes", 4), ("TwoAdicity", 24)]
      arithmetic := .primeField, twoAdicGenerator := some 1791270792 },
    { row := "koala-bear.ext4", sorts := ["Group", "Ring", "Field", "ExtensionField", "TwoAdicField"]
      typeMembers := [("Scalar", .row "koala-bear.ext4"), ("Prime", .row "koala-bear"),
        ("Base", .row "koala-bear")]
      naturalMembers := [("Order", koalaBearOrder ^ 4), ("Characteristic", koalaBearOrder),
        ("Dimension", 4), ("Degree", 4), ("TwoAdicity", 26)]
      arithmetic := .extension 3 },
    { row := "bls12-381.fr", sorts := ["Group", "Ring", "Field", "PrimeField", "TwoAdicField"]
      typeMembers := [("Scalar", .row "bls12-381.fr"), ("Prime", .row "bls12-381.fr")]
      naturalMembers := [("Order", bls12381Order), ("Characteristic", bls12381Order),
        ("Dimension", 1), ("Bytes", 32), ("TwoAdicity", 32)]
      arithmetic := .primeField },
    { row := "bls12-381.g1", sorts := ["Group", "PrimeOrderGroup"]
      typeMembers := [("Scalar", .row "bls12-381.fr")], naturalMembers := [("Order", bls12381Order)]
      arithmetic := .curveG1 },
    { row := "bls12-381.g2", sorts := ["Group", "PrimeOrderGroup"]
      typeMembers := [("Scalar", .row "bls12-381.fr")], naturalMembers := [("Order", bls12381Order)]
      arithmetic := .none },
    { row := "bls12-381.gt", sorts := ["Group"]
      typeMembers := [("Scalar", .row "bls12-381.fr")], naturalMembers := [("Order", bls12381Order)]
      arithmetic := .none },
    -- the sealed types that `zkc::oracle` binds
    { row := "oracle.handle", sorts := [], typeMembers := [], naturalMembers := [], arithmetic := .none },
    { row := "oracle.claim", sorts := [], typeMembers := [], naturalMembers := [], arithmetic := .none },
    -- the transcript and the label of the suite `suite.merlin3.bls12-381.fr64be/0`
    { row := "suite.merlin3.bls12-381.fr64be/0.state", sorts := [], typeMembers := []
      naturalMembers := [], arithmetic := .none },
    { row := "suite.merlin3.bls12-381.fr64be/0.label", sorts := [], typeMembers := []
      naturalMembers := [], arithmetic := .none }]
  modules := [
    { row := "bls12-381", implements := some "zkc::algebra::Pairing"
      typeMembers := [("Scalar", .row "bls12-381.fr"), ("G1", .row "bls12-381.g1"),
        ("G2", .row "bls12-381.g2"), ("Target", .row "bls12-381.gt")]
      naturalMembers := [] },
    { row := "hash.sha256", implements := some "zkc::hash::Hash", typeMembers := []
      naturalMembers := [("Size", 32)] },
    { row := "hash.keccak256", implements := some "zkc::hash::Hash", typeMembers := []
      naturalMembers := [("Size", 32)] },
    { row := "hash.shake128", implements := some "zkc::hash::ExtendableOutput"
      typeMembers := [], naturalMembers := [] },
    { row := "hash.shake256", implements := some "zkc::hash::ExtendableOutput"
      typeMembers := [], naturalMembers := [] },
    { row := "suite.merlin3.bls12-381.fr64be/0", implements := some "zkc::construction::Suite"
      typeMembers := [("Challenge", .row "bls12-381.fr"),
        ("State", .row "suite.merlin3.bls12-381.fr64be/0.state")]
      naturalMembers := [("ChallengeUnits", 64), ("PositionUnits", 16)] },
    { row := "suite.poseidon2-duplex.koala-bear/0", implements := some "zkc::construction::Suite"
      typeMembers := [("Challenge", .row "koala-bear.ext4")]
      naturalMembers := [("ChallengeUnits", 4), ("PositionUnits", 1)] },
    { row := "suite.schnorr-signature", implements := none
      typeMembers := [("Challenge", .row "bls12-381.fr")]
      naturalMembers := [("ChallengeUnits", 64), ("PositionUnits", 16)] },
    { row := "suite.ml-dsa", implements := none, typeMembers := []
      naturalMembers := [("ChallengeUnits", 32), ("PositionUnits", 8)] }]
  representatives := [("Group", "bls12-381.gt"), ("PrimeOrderGroup", "bls12-381.g1"),
    ("Ring", "koala-bear"), ("Field", "koala-bear"), ("PrimeField", "koala-bear"),
    ("TwoAdicField", "koala-bear"), ("ExtensionField", "koala-bear.ext4")]
  rows := rows

end Zkc.Core.Vocabulary
