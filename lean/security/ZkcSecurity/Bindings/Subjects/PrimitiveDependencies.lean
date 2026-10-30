module

public import Zkc.Source.Structured.RelationMeaning
public import Zkc.Claims.Wire

@[expose] public section

/-! Conservative applicability of the default ideal experiments. Relations
may use the admitted pure Math vocabulary and its checked helper closure.
Executable primitives and internal observations have no default relation
interpretation under an ideal oracle. Every nested callback is inspected. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims Zkc.Source.Structured

def defaultRelationOperation : Op → Bool
  | .indexConstant .. | .indexEqual | .indexLess | .indexPowerOfTwo | .vectorLength .. |
    .fieldConstant .. | .fieldAdd .. | .fieldSubtract .. | .fieldMultiply .. |
    .fieldEmbed .. | .fieldEqual .. | .groupIdentity .. | .groupAdd .. | .groupScale .. |
    .groupEqual .. | .booleanConstant .. | .booleanAnd | .booleanOr | .booleanXor |
    .booleanEqual | .booleanNotEqual | .select .. | .boundedAt .. |
    .makeProduct .. | .getProduct .. | .invoke .. | .multilinearRestrictPrefix .. |
    .fold .. | .collect .. | .map .. | .branch .. | .loop .. | .loopCondition .. | .guard => true
  | .exec .. | .mark .. => false

/-- The admitted declaration table is acyclic. Its size bounds the depth;
zero fuel, missing signatures and duplicate signatures refuse conservatively. -/
def defaultRelationHelper : Nat → List CheckedDefinition → Helper → Bool
  | 0, _, _ => false
  | fuel + 1, definitions, helper =>
      match definitions.filter (fun definition => definition.helper == helper) with
      | [definition] => helper.kind == .math &&
          definition.raw.operations.all defaultRelationOperation &&
          definition.helpers.all (defaultRelationHelper fuel definitions)
      | _ => false

def checkDefaultRelation (definitions : List CheckedDefinition) (helper : Helper) :
    Except ResolutionError Unit :=
  if defaultRelationHelper (definitions.length + 1) definitions helper then .ok ()
  else .error (.schema ("default experiment requires pure registered relation dependencies: " ++ helper.name))

/-- Formula dependencies keep the existing conservative closure check. Opaque
meanings have already been selected by exact registry admission. -/
def checkRetainedMeaning {snapshot : Snapshot} {imported : Imported snapshot}
    {application : RelationApplication} {relation : RelationBinding snapshot application}
    {Value : Zkc.Source.Structured.Ty → Type} {registry : OpaqueRegistry Value}
    (meaning : Zkc.Source.Structured.RelationMeaning imported relation Value registry) :
    Except ResolutionError Unit :=
  match meaning with
  | .formula binding => checkDefaultRelation imported.program.payload.definitions binding.definition.helper
  | .opaque _ => .ok ()

end ZkcSecurity.Claims
