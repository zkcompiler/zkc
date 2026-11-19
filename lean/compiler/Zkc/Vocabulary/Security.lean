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
  | .writtenFork => "Zkc.Formal.Written.SpecialSoundness"

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

/-- Language-level applicability. A property can be named before its source-to-theorem
binding is implemented. The formal definition supplies the mathematical statement. -/
structure Property where
  name : String
  honestSide : HonestSide
  clause : RequiredClause
  stages : List String := ["written", "committed", "constructed", "serialized"]
  constructions : List String := ["derived", "interactive", "authored"]
  binding : Option Binding := none
  deriving Inhabited, Repr

def properties : Array Property := #[
  {name := "completeness", honestSide := .allRoles, clause := .none},
  {name := "soundness", honestSide := .verifier, clause := .decision},
  {name := "special_soundness", honestSide := .verifier, clause := .fork,
   stages := ["written"], binding := some .writtenFork},
  {name := "knowledge_soundness", honestSide := .verifier, clause := .knowledge},
  {name := "zero_knowledge", honestSide := .exceptSimulated,
   clause := .simulation},
  {name := "honest_verifier_zero_knowledge", honestSide := .allRoles, clause := .simulation,
   stages := ["written", "committed"]},
  {name := "unforgeability", honestSide := .verifier, clause := .none,
   stages := ["constructed", "serialized"], constructions := ["derived", "authored"]}]

end Zkc.Security
