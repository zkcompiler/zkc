import Tools.Artifact.Bindings

set_option autoImplicit false

namespace Tools.Artifact
open Lean (Json)
open Tools.Interactive

structure PublicBinding where
  label : Name
  ports : List (Name × Name)

structure Descriptor where
  entry : Name
  producer : Name
  validator : Name
  publicBindings : List PublicBinding
  rng : Name
  draws : List (Name × Name)
  acceptance : Nat
  json : Json

def Descriptor.suite (descriptor : Descriptor) : String :=
  match (Decode.array descriptor.json).toOption with
  | some [_, _, _, _, _, _, _, .str suite, _] => suite
  | _ => Bindings.transcriptIdentity

/-- Application binding labels are UTF-8 strings, not source symbols. Their
bytes are preserved in the root and cannot rename generated MLIR values. -/
def bindingLabel (json : Json) : Result String := do
  let value ← Decode.string json
  ensure (!value.isEmpty && value.utf8ByteSize ≤ 128) "public-binding-label"
  return value

def decodeDescriptor (source : Source) (json : Json)
    (origins : List Algorithms.Origin := []) : Result Descriptor := do
  let [.str tag, entry, producer, validator, publicBindings,
       random, acceptance, .str suite, .str identity] ← Decode.array json
    | throw "construction-descriptor"
  -- The identity policy is a field; both policies are current.
  ensure (tag == "zkc.construction/1" &&
    (identity == "exact" || identity == "normalized")) "construction-descriptor"
  ensure (Bindings.transcriptDomain suite) "construction-transcript-suite"
  let field ← Bindings.associatedIdentity suite "ChallengeField"
  let entry ← Decode.name entry
  let producer ← Decode.name producer
  let validator ← Decode.name validator
  ensure (producer != validator) "construction-roles"
  let binding ← source.binding (← lookup entry source.entries)
  let definition ← source.protocol binding.protocol
  ensure (binding.roles.length == 2 && binding.roles.any (fun p => p.2 == producer) &&
    binding.roles.any (fun p => p.2 == validator)) "construction-roles"
  let port (role name : Name) : Result Port := do
    let p ← lookup name (definition.arguments.map fun p => (p.name, p))
    ensure ((← binding.role p.owner) == role) "public-port-owner"
    return p
  let publicBindings ← (← Decode.array publicBindings limits.ports).mapM fun b => do
    let [label, ports] ← Decode.array b | throw "public-binding"
    let label ← bindingLabel label
    let ports ← Decode.pairs Decode.name Decode.name ports
    ensure (!ports.isEmpty) "public-binding-ports"
    let types ← ports.mapM fun (r,n) => return (← port r n).ty
    ensure (types.all serializable && types.eraseDups.length == 1) "public-binding-types"
    return PublicBinding.mk label ports
  ensure (unique (publicBindings.map PublicBinding.label)) "public-binding-labels"
  let declaredPorts := publicBindings.flatMap fun b => b.ports
  ensure (declaredPorts.eraseDups.length == declaredPorts.length) "public-binding-port-reuse"
  let [rng, draws] ← Decode.array random | throw "construction-random"
  let rng ← Decode.name rng
  ensure ((← port validator rng).ty == ("rng:" ++ field)) "construction-rng-port"
  let draws ← Decode.pairs Decode.name Decode.name draws
  ensure (draws.eraseDups.length == draws.length) "construction-draws"
  let draws ← if origins.isEmpty then pure draws else do
    let selected ← draws.mapM fun (name, site) => do
      let occurrences := origins.filter fun origin => origin.definition == name && origin.originalSite == site
      ensure (!occurrences.isEmpty) "construction-draw-site"
      return occurrences.map fun origin => (origin.function, origin.site)
    pure selected.flatten
  for (name, site) in draws do
    let function ← source.function name
    let some body := function.body | throw "construction-external-draw"
    ensure (!hasLocalControl body) "construction-local-control-draw"
    let some (.op _ operation attributes _ _) := body.find? (fun i => match i with
      | .op s .. => s == site | _ => false) | throw "construction-draw-site"
    let selected ← selectOperation source operation attributes
    ensure (selected.contract == "random.draw" || selected.contract == "random.index") "construction-draw-site"
    ensure (selected.arguments == [field]) "construction-draw-domain"
  let acceptance ← Decode.natural acceptance
  let outputs ← definition.results.filterM fun (role, _) => return (← binding.role role) == validator
  ensure ((outputs[acceptance]?.map Prod.snd) == some "bool") "construction-acceptance"
  return ⟨entry, producer, validator, publicBindings, rng, draws, acceptance, json⟩

private def admitControlledBody (bindings : List OperationBinding) : Nat → List Instruction → Result Unit
  | 0, _ => .error "body-depth-limit"
  | depth + 1, code => do
      for instruction in code do
        match instruction with
        | .op _ name _ _ _ =>
          let signature ← Bindings.resolve false (← lookup name (bindings.map fun b => (b.name, b)))
          ensure ((signature.inputs ++ signature.outputs).all fun ty => !affine ty.spelling)
            "construction-local-control-resource"
        | .conditional _ _ _ yes no _ => admitControlledBody bindings depth yes; admitControlledBody bindings depth no
        | .forLoop _ _ _ _ _ _ nested _ => admitControlledBody bindings depth nested
        | .ret _ | .yield _ => pure ()
        | _ => throw "construction-local-control-resource"

/-- The independent artifact profile has public validator inputs and an
unconstructed original source. Common protocol transformation itself supports
broader resource flows; this check does not restrict PIR's general meaning. -/
def admitArtifactProfile (source : Source) (descriptor : Descriptor) : Result Unit := do
  let .explicit bindings := source.environment
  for function in source.functions do
    if hasLocalControl (function.body.getD []) then
      ensure ((function.arguments.map Prod.snd ++ function.results).all fun ty => !affine ty)
        "construction-local-control-resource"
      admitControlledBody bindings limits.depth (function.body.getD [])
  ensure (source.functions.all (fun f =>
    f.arguments.all (fun p => typeKind p.2 != "transcript") && f.results.all (fun t => typeKind t != "transcript")) &&
    source.protocols.all (fun p => p.arguments.all (fun a => typeKind a.ty != "transcript") &&
      p.results.all (fun r => typeKind r.2 != "transcript"))) "artifact-source-transcript"
  let binding ← source.binding (← lookup descriptor.entry source.entries)
  let definition ← source.protocol binding.protocol
  for p in definition.arguments do
    if (← binding.role p.owner) == descriptor.validator then
      if serializable p.ty then
        ensure (descriptor.publicBindings.any (fun b =>
          b.ports.contains (descriptor.validator, p.name))) "artifact-unbound-verifier-input"
      else
        ensure (typeKind p.ty == "verifier_key" || (typeKind p.ty == "rng" && p.name == descriptor.rng))
          "artifact-verifier-resource"

inductive PathElement where
  | call (site binding : Name)
  | loop (site : Name) (iteration : Nat)
  | localBranch (site : Name) (selected : Bool)
  | localIteration (site : Name) (index : Nat)

def PathElement.json : PathElement → Json
  | .call site binding => .arr #[.str "call", .str site, .str binding]
  | .localBranch site selected => .arr #[.str "if", .str site, .str (if selected then "then" else "else")]
  | .localIteration site index => .arr #[.str "for", .str site, .str (toString index)]
  | .loop site iteration => .arr #[.str "loop", .str site, .str (toString iteration)]

structure Location where
  entry : Name
  binding : Name
  path : List PathElement
  protocol : Name
  role : Name
  sourceRole : Name := ""
  localSite : Name := ""
  function : Name := ""
  operation : Name := ""

def Location.origin (location : Location) (event : Json) : Json :=
  .arr #[.str "zkc.logical-origin/1", .str location.entry, .str location.binding,
    .arr (location.path.map PathElement.json).toArray, event]

def Location.challenge (location : Location) : Json :=
  location.origin (.arr #[.str "challenge", .str location.protocol, .str location.localSite,
    .str location.function, .str location.operation, .str location.sourceRole])

def Location.message (location : Location) (site schema sender receiver : Name) : Json :=
  location.origin (.arr #[.str "message", .str location.protocol, .str site, .str schema,
    .str sender, .str receiver])

def Location.request (location : Location) (kernel : Name) (attrs : List String)
     (arguments : List String := []) : Json :=
  let fields := #[.str "operation", .str location.protocol, .str location.localSite,
    .str location.function, .str location.operation, .str location.sourceRole, .str kernel]
  .arr #[.str "zkc.logical-origin/2", .str location.entry, .str location.binding,
    .arr (location.path.map PathElement.json).toArray,
    .arr (fields ++ #[.arr (arguments.map Json.str).toArray, .arr (attrs.map Json.str).toArray])]

end Tools.Artifact
