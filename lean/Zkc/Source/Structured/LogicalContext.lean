module

public import Zkc.Source.Structured.ContractInstantiation

@[expose] public section

/-! Typed logical contexts, independent of how a protocol packs runtime ports.

A binder is a lexical position in a typed context. Its sort is either a native
ABI type or a library sort that need not have any native representation. Sort,
predicate and view instances are identified by their declaration together with
normalized static arguments, so two instances with one native ABI can still be
different objects. Runtime ports enter only as explicit observations: a logical
choice never silently becomes an observation, nor the converse. The legacy
selector-named parameter and witness slots are keys of the same store, so the
existing `LogicalAssignments` is a view of this carrier rather than a second
namespace. Choosing a value supplies no quantifier, agreement, causality or
security assumption; those belong to the property consumer. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Logical
open Zkc.Source Zkc.Source.Structured

/-- Normalized static arguments that belong to an instance's identity. -/
inductive StaticArgument where
  | nat (value : Nat)
  | domain (name : String)
  | declaration (name : String)
  deriving DecidableEq, Repr

/-- A declaration instance: the selected declaration and its static arguments.
A source digest identifies a declaration version; it proves neither semantic
equality nor inequality of two differently spelled declarations. -/
structure Identity where
  declaration : String
  statics : List StaticArgument
  deriving DecidableEq, Repr

/-- Logical sorts: native ABI types, or library sorts without a native port. -/
inductive LogicalType (Sorts : Type) where
  | native (type : Ty)
  | sort (sort : Sorts)
  deriving DecidableEq

/-- A library's logical vocabulary. Codes are typed; identities are what an
export names. Views are explicit, deterministic and possibly partial maps, for
example from a runtime vector to a table of a statically fixed arity. -/
structure Vocabulary where
  Sorts : Type
  Predicates : Type
  Views : Type
  sortIdentity : Sorts → Identity
  predicateIdentity : Predicates → Identity
  viewIdentity : Views → Identity
  arguments : Predicates → List (LogicalType Sorts)
  viewInput : Views → LogicalType Sorts
  viewOutput : Views → LogicalType Sorts

def LogicalType.denote {Sorts : Type} (Value : Ty → Type) (meaning : Sorts → Type) :
    LogicalType Sorts → Type
  | .native type => Value type
  | .sort code => meaning code

/-- One interpretation per subject and experiment. Every use of a predicate or
view code reads this single meaning, so two source spellings resolving to the
same code cannot receive different meanings. Opaque meanings remain choices of
the experiment; executable formula meanings are supplied by their own owner. -/
structure Interpretation (V : Vocabulary) (Value : Ty → Type) where
  sorts : V.Sorts → Type
  holds : (predicate : V.Predicates) →
    Values (LogicalType.denote Value sorts) (V.arguments predicate) → Prop
  view : (view : V.Views) → LogicalType.denote Value sorts (V.viewInput view) →
    Option (LogicalType.denote Value sorts (V.viewOutput view))

abbrev Interpretation.Denote {V : Vocabulary} {Value : Ty → Type}
    (interpretation : Interpretation V Value) : LogicalType V.Sorts → Type :=
  LogicalType.denote Value interpretation.sorts

/-- One key family. Lexical binders are the logical identities; `parameter` and
`witness` keep the legacy selector-named slots in the same store. A selector in
a key names a slot; it is never read from the runtime boundary. -/
inductive Key (Sorts : Type) (signature : ProtocolSignature) (context : List (LogicalType Sorts)) :
    LogicalType Sorts → Type where
  | binder {type : LogicalType Sorts} (ref : Var context type) : Key Sorts signature context type
  | parameter {type : Ty} (selector : BoundarySelector signature type) :
      Key Sorts signature context (.native type)
  | witness {type : Ty} (selector : BoundarySelector signature type) :
      Key Sorts signature context (.native type)

variable {snapshot : Snapshot} {imported : Imported snapshot}
  {V : Vocabulary} {Value : Ty → Type}

/-- The single logical store of one owner invocation. Owner and invocation
indices are labels, as for `LogicalAssignments`; they establish no reachability. -/
structure Store (interpretation : Interpretation V Value) (owner : ContractBinding imported)
    (invocation : InvocationCoordinate) (context : List (LogicalType V.Sorts)) where
  get : {type : LogicalType V.Sorts} → Key V.Sorts owner.protocol.signature context type →
    Option (interpretation.Denote type)

/-- How an argument obtains its value. `key` reads the logical store, `observed`
reads an actual boundary selector, `supplied` is a fixed native constant and
`view` applies a vocabulary view. No constructor converts one into another. -/
inductive Term (V : Vocabulary) (Value : Ty → Type) (signature : ProtocolSignature)
    (context : List (LogicalType V.Sorts)) : LogicalType V.Sorts → Type where
  | key {type : LogicalType V.Sorts} (key : Key V.Sorts signature context type) :
      Term V Value signature context type
  | observed {type : Ty} (selector : BoundarySelector signature type) :
      Term V Value signature context (.native type)
  | supplied {type : Ty} (value : Value type) : Term V Value signature context (.native type)
  | unavailable {type : LogicalType V.Sorts} : Term V Value signature context type
  | view (view : V.Views) (argument : Term V Value signature context (V.viewInput view)) :
      Term V Value signature context (V.viewOutput view)

/-- A lexical binder used as an argument. -/
abbrev Term.binder {signature : ProtocolSignature} {context : List (LogicalType V.Sorts)}
    {type : LogicalType V.Sorts} (ref : Var context type) : Term V Value signature context type :=
  .key (.binder ref)

/-- An application of a vocabulary predicate. Arguments are read in order; a
missing argument makes the atom false rather than choosing a fresh value. -/
structure Atom (V : Vocabulary) (Value : Ty → Type) (signature : ProtocolSignature)
    (context : List (LogicalType V.Sorts)) where
  predicate : V.Predicates
  arguments : Values (Term V Value signature context) (V.arguments predicate)

section Reading
variable (interpretation : Interpretation V Value) {owner : ContractBinding imported}
  {invocation : InvocationCoordinate} {context : List (LogicalType V.Sorts)}

def Term.read (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context) : {type : LogicalType V.Sorts} →
    Term V Value owner.protocol.signature context type → Option (interpretation.Denote type)
  | _, .key slot => store.get slot
  | _, .observed selector => selector.read protocolContext boundary
  | _, .supplied value => some value
  | _, .unavailable => none
  | _, .view code argument =>
    (Term.read protocolContext boundary store argument) >>= interpretation.view code

def readTerms (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context) : {types : List (LogicalType V.Sorts)} →
    Values (Term V Value owner.protocol.signature context) types →
    Option (Values interpretation.Denote types)
  | _, .nil => some .nil
  | _, .cons term rest =>
    match term.read interpretation protocolContext boundary store,
        readTerms protocolContext boundary store rest with
    | some value, some values => some (.cons value values)
    | _, _ => none

/-- The existential only packages the unique ordered read result. -/
def Atom.Holds (atom : Atom V Value owner.protocol.signature context)
    (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context) : Prop :=
  ∃ arguments, readTerms interpretation protocolContext boundary store atom.arguments = some arguments ∧
    interpretation.holds atom.predicate arguments

end Reading

section Laws
variable {interpretation : Interpretation V Value} {owner : ContractBinding imported}
  {invocation : InvocationCoordinate} {context : List (LogicalType V.Sorts)}

/-- A binder's value never depends on runtime ports or role context. -/
theorem binder_read_port_independent {type : LogicalType V.Sorts} (ref : Var context type)
    (first second : ProtocolContext)
    (left right : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context) :
    (Term.binder (Value := Value) (signature := owner.protocol.signature) ref).read
        interpretation first left store =
      (Term.binder (Value := Value) (signature := owner.protocol.signature) ref).read
        interpretation second right store := rfl

/-- An observation never depends on the logical store. -/
theorem observed_read_store_independent {type : Ty}
    (selector : BoundarySelector owner.protocol.signature type) (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (left right : Store interpretation owner invocation context) :
    (Term.observed (V := V) (context := context) selector).read interpretation protocolContext boundary left =
      (Term.observed (V := V) (context := context) selector).read interpretation protocolContext boundary right :=
  rfl

/-- Repeated uses of one binder share one value: there is one store lookup. -/
theorem binder_shared {type : LogicalType V.Sorts} (ref : Var context type)
    (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context) :
    (Term.binder (Value := Value) (signature := owner.protocol.signature) ref).read
        interpretation protocolContext boundary store = store.get (.binder ref) := rfl

theorem readTerms_cons {type : LogicalType V.Sorts} {types : List (LogicalType V.Sorts)}
    (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context)
    (term : Term V Value owner.protocol.signature context type)
    (rest : Values (Term V Value owner.protocol.signature context) types)
    (value : interpretation.Denote type) (values : Values interpretation.Denote types)
    (first : term.read interpretation protocolContext boundary store = some value)
    (others : readTerms interpretation protocolContext boundary store rest = some values) :
    readTerms interpretation protocolContext boundary store (.cons term rest) = some (.cons value values) := by
  simp only [readTerms, first, others]

/-- An atom with one unavailable argument never holds. -/
theorem atom_absent_argument (atom : Atom V Value owner.protocol.signature context)
    (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context)
    (absent : readTerms interpretation protocolContext boundary store atom.arguments = none) :
    ¬ atom.Holds interpretation protocolContext boundary store := by
  rintro ⟨arguments, present, _⟩
  rw [absent] at present
  cases present

end Laws

/-- A store holding only lexical binder values; legacy slots are empty. -/
def Store.ofValues {interpretation : Interpretation V Value} {owner : ContractBinding imported}
    {invocation : InvocationCoordinate} {context : List (LogicalType V.Sorts)}
    (values : Values interpretation.Denote context) : Store interpretation owner invocation context :=
  ⟨fun key => match key with
    | .binder ref => some (values.get ref)
    | .parameter _ | .witness _ => none⟩

theorem Store.ofValues_binder {interpretation : Interpretation V Value} {owner : ContractBinding imported}
    {invocation : InvocationCoordinate} {context : List (LogicalType V.Sorts)}
    (values : Values interpretation.Denote context) {type : LogicalType V.Sorts} (ref : Var context type) :
    (Store.ofValues (owner := owner) (invocation := invocation) values).get (.binder ref) =
      some (values.get ref) := rfl

end Zkc.Source.Structured.Logical
