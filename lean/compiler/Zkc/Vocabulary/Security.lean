module

@[expose] public section
set_option autoImplicit false

namespace Zkc.Security

/-- A source-issued subject with an interpretation in the independent formal package. -/
inductive Binding where
  | writtenFork
  deriving Inhabited, BEq, Repr

/-- The generated application is type-checked at the actual formal definition. -/
def Binding.statement : Binding → String
  | .writtenFork => "ZkcFormal.Written.SpecialSoundness"

inductive HonestSide where
  | allRoles | verifier | exceptSimulated
  deriving Inhabited, BEq, Repr

def HonestSide.description : HonestSide → String
  | .allRoles => "every role"
  | .verifier => "the verifier"
  | .exceptSimulated => "every role except the simulated one, with authorized offline trapdoor roles honest"

inductive RequiredClause where
  | none | decision | knowledge | fork | simulation
  deriving Inhabited, BEq, Repr

def RequiredClause.description : RequiredClause → String
  | .none => "—"
  | .decision => "`proves` or `reduces`"
  | .knowledge => "`knowledge`"
  | .fork => "`knowledge` with a two-run extractor"
  | .simulation => "`zero_knowledge`"

/-- The properties that a goal can name (`CORE-LIBRARY.md` §2.9), in the order of the
documents' tables. -/
inductive Property where
  | completeness
  | soundness
  | specialSoundness
  | knowledgeSoundness
  | zeroKnowledge
  | honestVerifierZeroKnowledge
  | unforgeability
  deriving Inhabited, DecidableEq, Repr

namespace Property

/-- The name that a source writes for a property. -/
def spelling : Property → String
  | .completeness => "completeness"
  | .soundness => "soundness"
  | .specialSoundness => "special_soundness"
  | .knowledgeSoundness => "knowledge_soundness"
  | .zeroKnowledge => "zero_knowledge"
  | .honestVerifierZeroKnowledge => "honest_verifier_zero_knowledge"
  | .unforgeability => "unforgeability"

/-- Every property, once. -/
def all : List Property :=
  [.completeness, .soundness, .specialSoundness, .knowledgeSoundness, .zeroKnowledge,
    .honestVerifierZeroKnowledge, .unforgeability]

theorem mem_all (property : Property) : property ∈ all := by
  cases property <;> decide

/-- Whether a goal of this property is published from the written subject: the formal library's
command states its theorems from the goal's row. The issuer of the written subject refuses a
goal of another property at the goal's line; a goal of special soundness is issued by the route
of two-run knowledge, which does not read this. -/
def published : Property → Bool
  | .soundness => true
  | _ => false

end Property

/-- Language-level applicability. A property can be named before its source-to-theorem
binding is implemented. The formal definition supplies the mathematical statement. -/
structure Description where
  property : Property
  honestSide : HonestSide
  clause : RequiredClause
  stages : List String := ["written", "committed", "constructed", "serialized"]
  constructions : List String := ["derived", "interactive", "authored"]
  binding : Option Binding := none
  deriving Inhabited, Repr

/-- The name that a source writes for the described property. -/
def Description.name (description : Description) : String := description.property.spelling

/-- What the language says of each property. -/
def Property.description : Property → Description
  | .completeness =>
    {property := .completeness, honestSide := .allRoles, clause := .none}
  | .soundness =>
    {property := .soundness, honestSide := .verifier, clause := .decision}
  | .specialSoundness =>
    {property := .specialSoundness, honestSide := .verifier, clause := .fork,
     stages := ["written"], binding := some .writtenFork}
  | .knowledgeSoundness =>
    {property := .knowledgeSoundness, honestSide := .verifier, clause := .knowledge}
  | .zeroKnowledge =>
    {property := .zeroKnowledge, honestSide := .exceptSimulated, clause := .simulation}
  | .honestVerifierZeroKnowledge =>
    {property := .honestVerifierZeroKnowledge, honestSide := .allRoles, clause := .simulation,
     stages := ["written", "committed"]}
  | .unforgeability =>
    {property := .unforgeability, honestSide := .verifier, clause := .none,
     stages := ["constructed", "serialized"], constructions := ["derived", "authored"]}

/-- The descriptions of every property, in the documents' order. -/
def properties : Array Description := (Property.all.map Property.description).toArray

end Zkc.Security
