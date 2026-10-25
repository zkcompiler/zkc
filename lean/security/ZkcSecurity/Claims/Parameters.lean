module

public import ZkcSecurity.Claims.Admission
public import ZkcSecurity.Claims.CanonicalAuthorityKeys

@[expose] public section

/-! Property-owned parameter schemas. Canonical encoding preserves the finite
numeric expression, so arithmetically equivalent requests keep distinct wire
identities. Numerical interpretation uses the admitted cardinality environment.
An accepted gap is a rational in [0, 1], not a predicate supplied by evidence. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims

/-- A schema pins both directions, including the exact accepted wire form.
Missing registered numeric definitions remain distinct from malformed syntax. -/
structure ParameterSchema (α : Type) where
  decode : Option Wire.Expr → Except ResolutionError (Except Incomplete α)
  encode : α → Option Wire.Expr
  roundtrip : ∀ value, decode (encode value) = .ok (.ok value)
  canonical : ∀ wire value, decode wire = .ok (.ok value) → wire = encode value

def emptyParameters (property : String) : ParameterSchema Unit where
  decode
    | none => .ok (.ok ())
    | some _ => .error (.schema (property ++ " accepts no parameters"))
  encode _ := none
  roundtrip _ := rfl
  canonical wire value accepted := by cases wire <;> simp_all

def completenessParameters := emptyParameters "completeness@0"
def knowledgeParameters := emptyParameters "knowledge@0"

def relativeDistanceIdentifier : Identifier := ⟨"gaps.relative_distance", 0⟩

def numericParameterSyntax : Wire.Expr → Bool
  | .natural _ => true
  | .binary _ left right => numericParameterSyntax left && numericParameterSyntax right
  | .neg operand => numericParameterSyntax operand
  | .application "cardinality" none [(none, .reference _)] => true
  | _ => false

/-- The normalization and evaluation equations bind the value to the exact
request expression. Proof irrelevance gives one typed decoding of that wire. -/
structure RelativeDistance (cardinality : String → Except Incomplete Nat) where
  expression : Wire.Expr
  numericForm : numericParameterSyntax expression = true
  normalized : Wire.Expr
  normalization : Numeric.normalizeWith cardinality expression = .ok normalized
  value : ℚ≥0
  evaluation : Numeric.nonnegativeWith cardinality expression = .ok value
  atMostOne : value ≤ 1

def decodeRelativeDistance (cardinality : String → Except Incomplete Nat)
    (expression : Wire.Expr) : Except ResolutionError (Except Incomplete (RelativeDistance cardinality)) :=
  if numericForm : numericParameterSyntax expression = true then
   match normalized : Numeric.normalizeWith cardinality expression with
  | .error missing => .ok (.error missing)
  | .ok normal =>
    match evaluated : Numeric.nonnegativeWith cardinality expression with
    | .error _ => .error (.schema "relative distance requires a defined nonnegative rational")
    | .ok value =>
      if bounded : value ≤ 1 then .ok (.ok ⟨expression, numericForm, normal, normalized, value, evaluated, bounded⟩)
      else .error (.schema "relative distance exceeds one")
  else .error (.schema "relative distance requires a numeric expression over registered cardinalities")

def encodeRelativeDistance {cardinality : String → Except Incomplete Nat}
    (distance : RelativeDistance cardinality) : Wire.Expr :=
  .application relativeDistanceIdentifier.name (some relativeDistanceIdentifier.version)
    [(none, distance.expression)]

abbrev SoundnessParameters (cardinality : String → Except Incomplete Nat) :=
  Option (RelativeDistance cardinality)

def decodeSoundnessParameters (cardinality : String → Except Incomplete Nat) :
    Option Wire.Expr → Except ResolutionError (Except Incomplete (SoundnessParameters cardinality))
  | none => .ok (.ok none)
  | some (.application "gaps.relative_distance" (some 0) [(none, expression)]) =>
      (decodeRelativeDistance cardinality expression).map (·.map some)
  | some (.application name (some version) _) =>
      if name != relativeDistanceIdentifier.name || version != relativeDistanceIdentifier.version then
        .error (.unknownIdentifier ⟨name, version⟩)
      else .error (.schema "relative distance requires exactly one positional numeric argument")
  | some _ => .error (.schema "expected gaps.relative_distance@0(delta) or absent parameters")

def encodeSoundnessParameters {cardinality : String → Except Incomplete Nat} :
    SoundnessParameters cardinality → Option Wire.Expr :=
  Option.map encodeRelativeDistance

theorem decodeRelativeDistance_roundtrip {cardinality : String → Except Incomplete Nat}
    (distance : RelativeDistance cardinality) :
    decodeRelativeDistance cardinality distance.expression = .ok (.ok distance) := by
  rcases distance with ⟨expression, numericForm, normal, normalized, value, evaluated, bounded⟩
  unfold decodeRelativeDistance
  all_goals split <;> try simp_all
  all_goals split <;> try simp_all
  all_goals split <;> try simp_all
  all_goals split <;> try simp_all
  all_goals grind

theorem decodeRelativeDistance_expression {cardinality : String → Except Incomplete Nat}
    {expression : Wire.Expr} {distance : RelativeDistance cardinality}
    (decoded : decodeRelativeDistance cardinality expression = .ok (.ok distance)) :
    distance.expression = expression := by
  unfold decodeRelativeDistance at decoded
  all_goals split at decoded <;> try simp_all
  all_goals split at decoded <;> try simp_all
  all_goals split at decoded <;> try simp_all
  all_goals split at decoded <;> try simp_all
  all_goals cases decoded; rfl

def soundnessParameters (cardinality : String → Except Incomplete Nat) :
    ParameterSchema (SoundnessParameters cardinality) where
  decode := decodeSoundnessParameters cardinality
  encode := encodeSoundnessParameters
  roundtrip value := by
    cases value with
    | none => rfl
    | some distance =>
        simp only [encodeSoundnessParameters, Option.map, encodeRelativeDistance,
          relativeDistanceIdentifier, decodeSoundnessParameters, decodeRelativeDistance_roundtrip]
        rfl
  canonical wire value accepted := by
      unfold decodeSoundnessParameters at accepted
      split at accepted
      next =>
        have same := Except.ok.inj (Except.ok.inj accepted)
        subst value
        rfl
      next number =>
        cases decoded : decodeRelativeDistance cardinality number with
        | error error =>
            rw [decoded] at accepted
            change (Except.error error : Except ResolutionError (Except Incomplete _)) = Except.ok (Except.ok value) at accepted
            cases accepted
        | ok result =>
            cases result with
            | error missing =>
                rw [decoded] at accepted
                change (Except.ok (Except.error missing) : Except ResolutionError (Except Incomplete _)) = Except.ok (Except.ok value) at accepted
                cases accepted
            | ok distance =>
                rw [decoded] at accepted
                change (Except.ok (Except.ok (some distance)) : Except ResolutionError (Except Incomplete _)) = Except.ok (Except.ok value) at accepted
                have same := Except.ok.inj (Except.ok.inj accepted)
                subst value
                have same := decodeRelativeDistance_expression decoded
                simp [encodeSoundnessParameters, encodeRelativeDistance, relativeDistanceIdentifier, same]
      next name version arguments => split at accepted <;> cases accepted
      next => cases accepted

/-- The registered property key owns its parameter type and both wire laws.
An absent interpretation for a property is not supplied by this schema. -/
def PropertyKey.Parameters (key : PropertyKey) (cardinality : String → Except Incomplete Nat) : Type :=
  match key with
  | .soundness => SoundnessParameters cardinality
  | .completeness | .knowledge | .specialSoundness => Unit

def PropertyKey.parameterSchema (key : PropertyKey) (cardinality : String → Except Incomplete Nat) :
    ParameterSchema (key.Parameters cardinality) :=
  match key with
  | .soundness => soundnessParameters cardinality
  | .completeness => completenessParameters
  | .knowledge => knowledgeParameters
  | .specialSoundness => emptyParameters "special_soundness@0"

/-- No clause in the current equality-only catalogue installs a proximity
interpretation. This guard deliberately refuses to reuse exact soundness for
any present gap, including zero. A future slot must be registered on the
admitted clause before evidence, rather than on a proof method. -/
def requireExactSoundness {cardinality : String → Except Incomplete Nat}
    (clause : Wire.TargetRef) : SoundnessParameters cardinality → Except Incomplete Unit
  | none => .ok ()
  | some _ => .error ⟨["registered relative-distance interpretation for selected clause: " ++
      match clause with
      | .retained owner index name => owner ++ "/" ++ toString index ++ "/" ++ name
      | .importedLanguage owner application => owner ++ "/" ++ application.identifier.name]⟩

end ZkcSecurity.Claims
