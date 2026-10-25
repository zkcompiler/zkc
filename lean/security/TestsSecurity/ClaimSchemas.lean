import ZkcSecurity.Claims.Parameters
import ZkcSecurity.Claims.HonestModel
import ZkcSecurity.Claims.CanonicalAuthorityKeys

/-! Narrow schema controls. These check request admission and canonical laws,
not a cryptographic theorem or a newly registered proximity experiment. -/
set_option autoImplicit false
namespace TestsSecurity.ClaimSchemas
open Zkc.Claims Zkc.Source.Structured ZkcSecurity.Claims ZkcSecurity.Claims.HonestPair

def cardinality (name : String) : Except Incomplete Nat :=
  if name = "test.field" then .ok 5 else .error ⟨["unregistered cardinality: " ++ name]⟩

def gap (expression : Wire.Expr) : Option Wire.Expr :=
  some (.application "gaps.relative_distance" (some 0) [(none, expression)])

def parameterValue (wire : Option Wire.Expr) : Except ResolutionError (Except Incomplete (Option ℚ≥0)) :=
  ((soundnessParameters cardinality).decode wire).map (·.map (·.map (·.value)))

def refused {α : Type} : Except ResolutionError α → Bool
  | .error _ => true
  | .ok _ => false

def incompleteGap (wire : Option Wire.Expr) : Bool :=
  match (soundnessParameters cardinality).decode wire with
  | .ok (.ok parameters) =>
      match requireExactSoundness (.retained "test.protocol" 0 "target") parameters with
      | .error ⟨["registered relative-distance interpretation for selected clause: test.protocol/0/target"]⟩ => true
      | _ => false
  | _ => false

-- Both directions are proved for every value and every accepted wire.
example (schema : ParameterSchema Unit) (value : Unit) :
    schema.decode (schema.encode value) = .ok (.ok value) := schema.roundtrip value

example (wire : Option Wire.Expr) (parameters : SoundnessParameters cardinality)
    (accepted : (soundnessParameters cardinality).decode wire = .ok (.ok parameters)) :
    wire = (soundnessParameters cardinality).encode parameters :=
  (soundnessParameters cardinality).canonical wire parameters accepted

example (parameters : SoundnessParameters cardinality) :
    (soundnessParameters cardinality).decode ((soundnessParameters cardinality).encode parameters) =
      .ok (.ok parameters) := (soundnessParameters cardinality).roundtrip parameters

example : completenessParameters.decode none = .ok (.ok ()) := rfl
example : knowledgeParameters.decode none = .ok (.ok ()) := rfl
example : parameterValue none = .ok (.ok none) := rfl
example : requireExactSoundness (cardinality := cardinality) (.retained "test.protocol" 0 "target") none =
    .ok () := rfl

example : parameterValue (gap (.binary .div (.natural 2) (.natural 5))) =
    .ok (.ok (some (2 / 5))) := by decide +kernel
example : parameterValue (gap (.binary .div (.natural 1)
    (.application "cardinality" none [(none, .reference "test.field")]))) =
      .ok (.ok (some (1 / 5))) := by decide +kernel
example : parameterValue (gap (.natural 0)) = .ok (.ok (some 0)) := by decide +kernel
example : parameterValue (gap (.natural 1)) = .ok (.ok (some 1)) := by decide +kernel
example : incompleteGap (gap (.binary .div (.natural 2) (.natural 5))) = true := by decide +kernel
example : incompleteGap (gap (.natural 0)) = true := by decide +kernel
example : parameterValue (gap (.binary .div (.natural 1)
    (.application "cardinality" none [(none, .reference "missing.field")]))) =
      .ok (.error ⟨["unregistered cardinality: missing.field"]⟩) := by decide +kernel

-- Negative/range/undefined arithmetic and nonnumeric terms are refused.
example : refused (parameterValue (gap (.neg (.natural 1)))) = true := by decide +kernel
example : refused (parameterValue (gap (.natural 2))) = true := by decide +kernel
example : refused (parameterValue (gap (.binary .div (.natural 1) (.natural 0)))) = true := by decide +kernel
example : refused (parameterValue (gap (.binary .pow (.natural 1)
    (.binary .div (.natural 1) (.natural 2))))) = true := by decide +kernel
example : refused (parameterValue (gap (.list []))) = true := by decide +kernel
example : refused (parameterValue (gap (.reference "subject"))) = true := by decide +kernel
example : refused (parameterValue (gap (.application "unknown.numeric" (some 0) []))) = true := by decide +kernel

-- No parameter can repeat a subject, target, selector, quantity or extractor.
example : refused (completenessParameters.decode (gap (.natural 0))) = true := rfl
example : refused (knowledgeParameters.decode (some (.application "extractors.response_difference" (some 0) []))) = true := rfl
example : (soundnessParameters cardinality).decode
    (some (.application "gaps.relative_distance" (some 1) [(none, .natural 0)])) =
      .error (.unknownIdentifier ⟨"gaps.relative_distance", 1⟩) := rfl
example : refused (parameterValue (some (.application "gaps.unknown" (some 0) []))) = true := rfl
example : refused (parameterValue (some (.application "gaps.relative_distance" none [(none, .natural 0)]))) = true := rfl
example : refused (parameterValue (some (.application "gaps.relative_distance" (some 0)
    [(none, .natural 0), (none, .natural 0)]))) = true := rfl
example : refused (parameterValue (some (.list
    [.application "gaps.relative_distance" (some 0) [(none, .natural 0)],
     .application "gaps.relative_distance" (some 0) [(none, .natural 0)]]))) = true := rfl

def conflictingFields : List String :=
  ["subject", "target", "acceptance", "model", "quantity", "capabilities", "gap", "extractor"]

example : conflictingFields.all (fun field => refused (parameterValue
    (some (.application "gaps.relative_distance" (some 0)
      [(none, .natural 0), (some field, .natural 0)])))) = true := by decide +kernel

example : honestModelSchema honestModelApplication = .ok .privateUniform := rfl
example (model : HonestExecutionModel) : honestModelSchema (encodeHonestModel model) = .ok model :=
  honestModel_roundtrip model
example (application : Wire.Application) (model : HonestExecutionModel)
    (accepted : honestModelSchema application = .ok model) : application = encodeHonestModel model :=
  honestModel_canonical application model accepted
example : honestModelEntry.identifier = ⟨"models.honest", 0⟩ := rfl
example : honestModelEntry.schema = "zkc.model.honest/0" := rfl
example : resolveHonestModel ⟨[honestModelEntry]⟩ honestModelApplication = .ok .privateUniform := rfl
example : resolveHonestModel ⟨[honestModelEntry, honestModelEntry]⟩ honestModelApplication =
    .error (.conflict honestModelIdentifier) := rfl
example : resolveHonestModel ⟨[honestModelEntry]⟩ ⟨⟨"models.honest", 1⟩, []⟩ =
    .error (.unknownIdentifier ⟨"models.honest", 1⟩) := rfl
example : resolveHonestModel ⟨[honestModelEntry]⟩ ⟨⟨"models.honest_fiat_shamir", 0⟩, []⟩ =
    .error (.unknownIdentifier ⟨"models.honest_fiat_shamir", 0⟩) := rfl

def refusedModelArguments : List (List (Option String × Wire.Expr)) :=
  [[], [(some "producer", .application "producers.source_role" (some 0) [])],
   [(some "producer", .application "producers.unadmitted" (some 0) [])],
   [(some "producer", .application "user.producer" (some 0) [])],
   [(some "producer", .application "producers.compiled" (some 1) [])],
   [(some "producer", .application "producers.compiled" (some 0) [(some "artifact", .reference "other")])],
   [(some "producer", .reference "producers.compiled")],
   [(some "producer", .application "producers.compiled" (some 0) []),
    (some "producer", .application "producers.compiled" (some 0) [])]]

example : refusedModelArguments.all (fun arguments => refused
    (honestModelSchema ⟨honestModelIdentifier, arguments⟩)) = true := by decide +kernel

example : ["level", "attempts", "retry", "restarts", "oracle", "private_coins", "queries", "unknown"].all
    (fun field => refused (honestModelSchema
      ⟨honestModelIdentifier, honestModelApplication.arguments ++ [(some field, .natural 1)]⟩)) = true := by decide +kernel

def undefinedModel : Export (Wire.Application → Except ResolutionError HonestExecutionModel) :=
  { honestModelEntry with definition := none }

example : ¬ HonestModelAdmission ⟨[undefinedModel]⟩ honestModelApplication := by
  intro admission
  have selected := admission.selected
  change Except.ok undefinedModel = Except.ok honestModelEntry at selected
  have definitions := congrArg Export.definition (Except.ok.inj selected)
  cases definitions

def differentSchema : Export (Wire.Application → Except ResolutionError HonestExecutionModel) :=
  { honestModelEntry with schema := "user.replacement/0" }

example : ¬ HonestModelAdmission ⟨[differentSchema]⟩ honestModelApplication := by
  intro admission
  have selected := admission.selected
  change Except.ok differentSchema = Except.ok honestModelEntry at selected
  have schemas := congrArg Export.schema (Except.ok.inj selected)
  have different : differentSchema.schema ≠ honestModelEntry.schema := by decide
  exact different schemas

-- Both the source input and target checks use this same closed Math guard.
example : defaultRelationOperation (.exec (.indexConstant 0)) = false := rfl
example : defaultRelationOperation (.mark "oracle.role") = false := rfl
example : defaultRelationOperation (.fieldAdd "test.field") = true := rfl
example : defaultRelationHelper 1 [] ⟨"unadmitted", .math, [], []⟩ = false := rfl
example : defaultRelationHelper 0 [] ⟨"cycle", .math, [], []⟩ = false := rfl

def pureBody : Zkc.Source.Region dialect [] [] := .ret .nil
def pureHelper : CheckedDefinition :=
  ⟨"pure", .math, [], [], pureBody.erase, pureBody, pureBody.elaborate_erase⟩
def observedBody : Zkc.Source.Region dialect [] [] :=
  .letOp (.mark "idealized.role") .nil .nil (.ret .nil)
def observedHelper : CheckedDefinition :=
  ⟨"observed", .math, [], [], observedBody.erase, observedBody, observedBody.elaborate_erase⟩
def callerBody (name : String) : Zkc.Source.Region dialect [] [] :=
  .letOp (.invoke ⟨name, .math, [], []⟩) .nil .nil (.ret .nil)

def caller (name : String) : CheckedDefinition :=
  let body := callerBody name
  ⟨"caller", .math, [], [], body.erase, body, body.elaborate_erase⟩

example : checkDefaultRelation [pureHelper] pureHelper.helper = .ok () := by decide +kernel
example : defaultRelationHelper 3 [pureHelper, caller "pure"] (caller "pure").helper = true := by decide +kernel
example : defaultRelationHelper 3 [observedHelper, caller "observed"]
    (caller "observed").helper = false := by decide +kernel
example : defaultRelationHelper 3 [pureHelper, pureHelper] pureHelper.helper = false := by decide +kernel
example : defaultRelationHelper 3 [caller "missing"] (caller "missing").helper = false := by decide +kernel
example : defaultRelationHelper 3 [caller "caller"] (caller "caller").helper = false := by decide +kernel

def nestedBody : Zkc.Source.Region dialect [.boolean] [] :=
  .letOp (.branch [] []) (.cons .here .nil) (.cons observedBody (.cons pureBody .nil)) (.ret .nil)
def nestedHelper : CheckedDefinition :=
  ⟨"nested", .math, [.boolean], [], nestedBody.erase, nestedBody, nestedBody.elaborate_erase⟩
example : defaultRelationHelper 2 [nestedHelper] nestedHelper.helper = false := by decide +kernel

example : reservedIdentifier ⟨"gaps.relative_distance", 1⟩ = true := rfl
example : reservedIdentifier ⟨"producers.compiled", 1⟩ = true := rfl

#print axioms soundnessParameters
#print axioms honestModel_canonical
end TestsSecurity.ClaimSchemas
