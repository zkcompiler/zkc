import ZkcTools.DeclarationAudit
import Zkc.Claims.ClosedString

/-! Declaration records for package-owned code.

Writes one JSON line per declaration written in the source of the selected
module families, sorted by name and module, after a header line. A record
states the declaration's name, module and kind, its structural and explicit
statement hashes (`ZkcTools.Statements` in `ZkcTools.DeclarationAudit`), its axiom closure (actual stored ConstantInfo
types and bodies, opaque proofs included; imported axiom caches are never authority), its docstring, structural tags
and, for theorems, its premise telescope: every leading binder, implicit and
instance binders included, with whether it is a premise and the head constant
of the premise's proposition. Declarations that Lean generates (recursors,
matchers, equation and injectivity lemmas, auxiliary proofs) carry no source
range and are omitted; the declaration audit still covers them.

Run after building the selected packages, from the package directory:

```sh
lake env lean --run ../checks/DeclarationRecords.lean [OPTION]... OUTPUT DIRECTORY...
```

The maintained Python driver builds the `declaration-records` executable and
the audited package first, then runs the executable in that package's Lake
environment. The interpreted command above remains a comparison/debugging
route. Both traverse the same stored declarations; no records are cached.

Each `DIRECTORY` is a source directory or a single `.lean` file relative to the
current directory, such as `Zkc` or `ZkcTools/JsonSupport.lean`; every module
below it is imported and selected. Executable roots, which each define `main`,
cannot be imported together and are selected by their library directories.

Options:
- `--check BASELINE`: compare the fresh records with an earlier output and fail,
  naming each added, removed or changed declaration, when they differ.
- `--registry NAME`: evaluate the registry table `NAME`, a list of identifier,
  category, schema constant and statement, and record it in the header; a
  missing table is an error.
- `--endpoints NAME`: evaluate the table of registered endpoints `NAME`, a list
  of covered endpoint, property, statement form and theorem, record it in the
  header and record every registered endpoint theorem in detail.
- `--detail NAME`: also record the pretty-printed statement and premises of the
  declaration `NAME`, its premise telescope whatever its kind, the registered
  constants (registry schemas and endpoints) it reaches through repository
  declarations, the head constant and arguments of its statement and of its
  value, every binder with the head constant of its type, the premise telescope
  of a statement that is an instance of a registered property (the head of a
  registered endpoint theorem's statement, unfolded once), and the named
  hypotheses of an evidence value (repeatable). A name that is not a declaration
  of the selected modules is noted and skipped; its consumer reports the absence.
- `--trace-records`: print the declaration currently being inspected and its
  elapsed time to stderr. This changes diagnostics only, not the records.

The output is deterministic for a fixed toolchain and fixed sources. Equal
statement hashes are regression evidence, not semantic preservation. -/

open Lean Meta ZkcTools.Statements

namespace DeclarationRecords

/-- Compare complete stored values, including theorem proofs. Only identical
versions may share a provider class; definitional equality/proof irrelevance
must not collapse different proofs or their axiom dependencies. -/
def sameStoredFields : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | .inductInfo a, .inductInfo b =>
    a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
    a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
    a.numNested == b.numNested && a.isRec == b.isRec && a.isUnsafe == b.isUnsafe &&
    a.isReflexive == b.isReflexive
  | .quotInfo a, .quotInfo b => a.toConstantVal == b.toConstantVal &&
    (match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false)
  | _, _ => false

/-- Derived ConstantInfo equality uses Expr.eqv, which ignores binder
annotations. Exact provider equivalence also checks the complete expression
structure, including binder names and visibility, in types, bodies and rules. -/
def sameStored (left right : ConstantInfo) : Bool :=
  sameStoredFields left right && left.type.equal right.type &&
    (match left.value? true, right.value? true with
      | none, none => true
      | some a, some b => a.equal b
      | _, _ => false) &&
    (match left, right with
      | .recInfo a, .recInfo b => a.rules.length == b.rules.length &&
          (a.rules.zip b.rules).all (fun (x, y) => x.rhs.equal y.rhs)
      | _, _ => true)

abbrev Providers := Std.HashMap Name (Option (Name × ConstantInfo))

/-- Lean can store identical generated declarations in several modules. Admit
these only after comparing all stored fields (proof bodies included), choosing
the least module Name as a deterministic representative. Differing versions are
ambiguous even if Lean's merged map happens to prefer one. -/
def providers (env : Environment) : Providers := Id.run do
  let mut found : Providers := {}
  for index in [:env.header.modules.size] do
    let owner := env.header.modules[index]!.module
    let mut localNames : Std.HashSet Name := {}
    for info in env.header.moduleData[index]!.constants do
      if localNames.contains info.name then
        found := found.insert info.name none
        continue
      localNames := localNames.insert info.name
      let value := match found[info.name]? with
        | none => some (owner, info)
        | some none => none
        | some (some (previous, stored)) =>
          if sameStored stored info then some (if Name.lt owner previous then owner else previous, stored)
          else none
      found := found.insert info.name value
  return found

/-- Validate the merged module association against stored declarations too.
A checked identical-provider class may have several owners, but the environment
must actually select one of them when recording a module identity. -/
def resolvedOwners (env : Environment) : Std.HashSet Name := Id.run do
  let mut found : Std.HashSet Name := {}
  for index in [:env.header.modules.size] do
    for info in env.header.moduleData[index]!.constants do
      if (env.getModuleIdxFor? info.name).any (·.toNat == index) then
        found := found.insert info.name
  return found

def provider (sources : Providers) (name : Name) : IO Name := do
  match sources[name]? with
  | some (some (owner, _)) => return owner
  | some none => throw <| IO.userError s!"ambiguous stored providers for dependency: {name}"
  | none => throw <| IO.userError s!"uncovered stored dependency: {name}"

def dependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut refs := info.type.getUsedConstants ++
    ((info.value? true).map Expr.getUsedConstants |>.getD #[])
  match info with
  | .inductInfo value => refs := refs ++ value.all.toArray ++ value.ctors.toArray
  | .ctorInfo value => refs := refs.push value.induct
  | .recInfo value =>
    refs := refs ++ value.all.toArray
    for rule in value.rules do refs := refs.push rule.ctor ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return refs

structure Cache where
  edges : Std.HashMap Name (Array Name) := {}
  closed : Std.HashMap Name (Array Name) := {}
  displayNames : Std.HashMap String Name := {}

/-- Traverse actual resolved ConstantInfo bodies, including opaque proofs.
Never consult collectAxioms' imported extension. Only a fully traversed root is
cached; a cycle sentinel is never published as an axiom closure. If the complete
closure is empty, every visited subclosure is empty too and can safely be cached.
The edge and completed-closure caches belong to this one environment. -/
def storedAxioms (env : Environment) (sources : Providers) (owners : Std.HashSet Name)
    (owned : Std.HashMap Name ConstantInfo) (root : ConstantInfo) (cache : Cache) :
    IO (Array Name × Cache) := do
  let mut cache := cache
  let mut pending := #[root.name]
  let mut visited : Std.HashSet Name := {}
  let mut axioms : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    let _ ← provider sources name
    unless owners.contains name do
      throw <| IO.userError s!"resolved module does not store dependency: {name}"
    if let some previous := cache.displayNames[name.toString]? then
      unless previous == name do
        throw <| IO.userError s!"ambiguous rendered kernel name: {name}"
    cache := { cache with displayNames := cache.displayNames.insert name.toString name }
    visited := visited.insert name
    if let some closed := cache.closed[name]? then
      for axiomName in closed do axioms := axioms.insert axiomName
      continue
    let some info := owned[name]?.orElse (fun _ => env.find? name)
      | throw <| IO.userError s!"unresolved dependency: {name}"
    let some (some (_, stored)) := sources[name]?
      | throw <| IO.userError s!"missing checked provider: {name}"
    unless sameStored stored info do
      throw <| IO.userError s!"resolved declaration differs from stored provider: {name}"
    if info matches .axiomInfo _ then axioms := axioms.insert name
    let refs := match cache.edges[name]? with
      | some refs => refs
      | none => dependencies info
    cache := { cache with edges := cache.edges.insert name refs }
    pending := pending ++ refs
  let result := axioms.toArray
  cache := { cache with closed := cache.closed.insert root.name result }
  if result.isEmpty then
    for name in visited do cache := { cache with closed := cache.closed.insert name #[] }
  return (result, cache)


/-- Module names of every `.lean` file below `directory`. -/
partial def modulesBelow (directory : System.FilePath) : IO (Array Name) := do
  let mut found := #[]
  for entry in ← directory.readDir do
    if ← entry.path.isDir then
      found := found ++ (← modulesBelow entry.path)
    else if entry.path.extension == some "lean" then
      let relative := (entry.path.withExtension "").components
      found := found.push (relative.foldl Name.str Name.anonymous)
  return found

structure Options where
  check : Option System.FilePath := none
  registry : Option Name := none
  endpoints : Option Name := none
  details : Array Name := #[]
  positional : Array String := #[]
  traceRecords : Bool := false

partial def parse : List String → Options → Except String Options
  | [], options => .ok options
  | "--check" :: path :: rest, options => parse rest { options with check := some path }
  | "--registry" :: name :: rest, options => parse rest { options with registry := some name.toName }
  | "--endpoints" :: name :: rest, options => parse rest { options with endpoints := some name.toName }
  | "--detail" :: name :: rest, options =>
      parse rest { options with details := options.details.push name.toName }
  | "--trace-records" :: rest, options => parse rest { options with traceRecords := true }
  | argument :: rest, options =>
      if argument.startsWith "--" then .error s!"unknown or incomplete option: {argument}"
      else parse rest { options with positional := options.positional.push argument }

def tags (env : Environment) (name : Name) (info : ConstantInfo) : Array String := Id.run do
  let mut found := #[]
  if isPrivateName name then found := found.push "private"
  if isClass env name then found := found.push "class"
  else if isStructure env name then found := found.push "structure"
  if Meta.isInstanceCore env name then found := found.push "instance"
  if propositionValued info then found := found.push "proposition-valued"
  return found

def premiseJson (premise : Premise) : Json :=
  Json.mkObj <| [("binder", Json.str (binderName premise.binder)), ("premise", Json.bool premise.proof)] ++
    match premise.head with
    | some head => [("head", Json.str head.toString)]
    | none => []

/-- Module roots of this repository's packages. The walk for registered
constants descends only through declarations of these modules. -/
def repositoryRoots : List Name :=
  [`Zkc, `ZkcExamples, `ZkcTools, `ZkcSecurity, `ZkcArkLib, `ZkcClean, `Tests, `TestsSecurity, `TestsArkLib, `TestsClean]

/-- The registered constants a declaration reaches through the types and
bodies of repository declarations, itself included. Upstream declarations are
recorded when reached but not descended into. -/
def reached (env : Environment) (registered : Std.HashSet Name) (start : Name) : Array Name := Id.run do
  let owned := fun (name : Name) => Id.run do
    let some index := env.getModuleIdxFor? name | return false
    let some module := env.header.modules[index.toNat]? | return false
    return repositoryRoots.any (·.isPrefixOf module.module)
  let mut seen : Std.HashSet Name := {}
  let mut pending := [start]
  let mut found := #[]
  while true do
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      if seen.contains name then continue
      seen := seen.insert name
      if registered.contains name then found := found.push name
      unless owned name do continue
      let some info := env.find? name | continue
      let mut next := info.type.getUsedConstants
      if let some value := info.value? true then next := next ++ value.getUsedConstants
      if let .inductInfo value := info then next := next ++ value.ctors.toArray
      pending := next.toList ++ pending
  return found.qsort Name.lt

/-- The head constant of an application, if any. -/
def headName (expression : Expr) : Option Name :=
  expression.getAppFn.consumeMData.constName?

def nameJson : Option Name → Json
  | some name => Json.str name.toString
  | none => Json.null

/-- The arguments of an application, each with its head constant and its text. -/
def argumentsJson (expression : Expr) : MetaM Json := do
  let arguments ← expression.getAppArgs.mapM fun argument => do
    return Json.mkObj [("head", nameJson (headName argument)), ("text", Json.str (toString (← ppExpr argument)))]
  return Json.arr arguments

/-- Model instances are admitted only on free non-propositional carrier types.
Checking just a class name would admit `Inhabited False`, or `Inhabited (PLift P)`,
as an ordinary model parameter and hide the proof it supplies. The fixed model
registry can extend this conservative policy when it declares another carrier. -/
def modelInstance (declaration : LocalDecl) : MetaM Bool := do
  unless declaration.binderInfo.isInstImplicit do return false
  let allowed : List Name := [`Field, `CommRing, `Fintype, `DecidableEq, `Inhabited,
    `SampleableType, `AddCommGroup, `Module]
  unless (headName declaration.type).any (allowed.contains ·) do return false
  for argument in declaration.type.getAppArgs do
    let argumentType ← whnf (← inferType argument)
    if argumentType.isSort then
      let .fvar carrier := argument.consumeMData | return false
      let carrierType ← whnf (← carrier.getDecl).type
      let .sort level := carrierType | return false
      if level == .zero then return false
  return true

/-- Binders whose values are accounted for by the fixed model context. Other
binders must be treated as potential assumptions, including Type-valued proof
wrappers. Reporting rejects unregistered wrappers even if a proof does not use
them; unused explicit propositions are still audited by the premise telescope. -/
def modelBinder (declaration : LocalDecl) : MetaM Bool := do
  if declaration.type.isSort then return true
  if declaration.binderInfo == .default && declaration.type.isConstOf ``String then return true
  return ← modelInstance declaration

/-- Every leading binder of a type: binder information, whether it is a proof of a
proposition, and the head constant of its type (`sort` for a universe). -/
def bindersJson (type : Expr) : MetaM Json :=
  forallTelescope type fun binders _ => do
    let found ← binders.mapM fun binder => do
      let declaration ← binder.fvarId!.getDecl
      let proof ← isProp declaration.type
      let head := if declaration.type.isSort then Json.str "sort" else nameJson (headName declaration.type)
      return Json.mkObj [("binder", Json.str (binderName declaration.binderInfo)), ("premise", Json.bool proof),
        ("type_head", head), ("model_instance", Json.bool (← modelInstance declaration))]
    return Json.arr found

/-- The structures of evidence whose named hypotheses are recorded. -/
def evidenceStructures : List Name :=
  [`ZkcSecurity.Endpoint.SoundnessEvidence, `ZkcSecurity.Endpoint.KnowledgeEvidence]

partial def listElements (list : Expr) : MetaM (Array Expr) := do
  let list ← whnfD list
  if list.isAppOfArity ``List.cons 3 then
    return #[list.getArg! 1] ++ (← listElements (list.getArg! 2))
  if list.isAppOf ``List.nil then return #[]
  throwError "unresolved list in declaration data"

def stringJson (expression : Expr) : MetaM Json := do
  match (← whnf expression) with
  | .lit (.strVal value) => return Json.str value
  | other => return Json.str (toString (← ppExpr other))

/-- The named hypotheses of an evidence value: the cited identifier, the
category, the claim's head constant (also after reducible unfolding) and
arguments, and the status: a proof, a proof that is a binder of the evidence's
declaration (an assumption by premise), or a reported assumption with the
registry identifier it cites. -/
def hypothesesJson (binders : Array Expr) (evidence : Expr) (structureName : Name) : MetaM Json := do
  let assumptions ← binders.filterM fun binder => do
    let declaration ← binder.fvarId!.getDecl
    if ← isProp declaration.type then return true
    return !(← modelBinder declaration)
  let list ← mkAppM (structureName ++ `hypotheses) #[evidence]
  let elements ← listElements list
  let found ← elements.mapM fun element => do
    let hypothesis ← whnf element
    unless hypothesis.isAppOfArity `ZkcSecurity.Endpoint.Hypothesis.mk 4 do
      return Json.mkObj [("unrecognized", Json.str (toString (← ppExpr hypothesis)))]
    let claim := hypothesis.getArg! 2
    let status ← whnf (hypothesis.getArg! 3)
    let statusJson ← if status.isAppOf `ZkcSecurity.FiatShamir.ObligationStatus.proved then
        let proof := status.appArg!
        let premise := assumptions.any fun binder => proof.containsFVar binder.fvarId!
        pure (Json.mkObj [("kind", Json.str (if premise then "premise" else "proof"))])
      else if status.isAppOf `ZkcSecurity.FiatShamir.ObligationStatus.assumed then
        let entry ← whnf (status.getArg! 2)
        pure (Json.mkObj [("kind", Json.str "assumed"), ("cites", ← stringJson (entry.getArg! 0))])
      else pure (Json.mkObj [("kind", Json.str "unrecognized")])
    return Json.mkObj [("identifier", ← stringJson (hypothesis.getArg! 0)),
      ("category", Json.str (toString (← ppExpr (hypothesis.getArg! 1)))),
      ("claim_head", nameJson (headName claim)),
      ("claim_head_reducible", nameJson (headName (← whnfR claim))),
      ("claim_arguments", ← argumentsJson claim),
      ("claim", Json.str (toString (← ppExpr claim))),
      ("status", statusJson)]
  return Json.arr found

/-- Read closed data using standard operations, never pretty-printed terms. -/
def literalString (expression : Expr) : MetaM String :=
  Zkc.Claims.ClosedString.read 4096 expression

def naturalJson (expression : Expr) : MetaM Json := do
  match ← whnfD expression with
  | .lit (.natVal value) => return toJson value
  | _ => throwError "claim data contains an unresolved natural"

def field (structureName fieldName : Name) (value : Expr) : MetaM Expr :=
  mkAppM (structureName ++ fieldName) #[value]

def identifierJson (value : Expr) : MetaM Json := do
  return Json.mkObj [("name", Json.str (← literalString (← field `Zkc.Claims.Identifier `name value))),
    ("version", ← naturalJson (← field `Zkc.Claims.Identifier `version value))]

partial def wireExpressionJson (value : Expr) : MetaM Json := do
  let value ← whnfD value
  let args := value.getAppArgs
  match headName value with
  | some `Zkc.Claims.Wire.Expr.natural =>
    let number ← naturalJson args[0]!
    return Json.mkObj [("kind", Json.str "natural"), ("value", Json.str number.compress)]
  | some `Zkc.Claims.Wire.Expr.reference =>
    return Json.mkObj [("kind", Json.str "reference"), ("name", Json.str (← literalString args[0]!))]
  | some `Zkc.Claims.Wire.Expr.application =>
    let version ← whnfD args[1]!
    let version ← if version.isAppOf ``Option.some then naturalJson version.appArg! else pure Json.null
    let arguments ← (← listElements args[2]!).mapM fun pair => do
      let label ← whnfD (← mkAppM ``Prod.fst #[pair])
      let label ← if label.isAppOf ``Option.some then pure (Json.str (← literalString label.appArg!)) else pure Json.null
      return Json.mkObj [("label", label), ("value", ← wireExpressionJson (← mkAppM ``Prod.snd #[pair]))]
    return Json.mkObj [("kind", Json.str "application"), ("name", Json.str (← literalString args[0]!)),
      ("version", version), ("arguments", Json.arr arguments)]
  | some `Zkc.Claims.Wire.Expr.binary =>
    let operator ← whnfD args[0]!
    let symbol ← match headName operator with
      | some `Zkc.Claims.Wire.Binary.add => pure "+"
      | some `Zkc.Claims.Wire.Binary.sub => pure "-"
      | some `Zkc.Claims.Wire.Binary.mul => pure "*"
      | some `Zkc.Claims.Wire.Binary.div => pure "/"
      | some `Zkc.Claims.Wire.Binary.pow => pure "^"
      | _ => throwError "unresolved wire operator"
    return Json.mkObj [("kind", Json.str "binary"), ("operator", Json.str symbol),
      ("left", ← wireExpressionJson args[1]!), ("right", ← wireExpressionJson args[2]!)]
  | some `Zkc.Claims.Wire.Expr.neg =>
    return Json.mkObj [("kind", Json.str "unary"), ("operator", Json.str "-"),
      ("operand", ← wireExpressionJson args[0]!)]
  | some `Zkc.Claims.Wire.Expr.list =>
    return Json.mkObj [("kind", Json.str "list"),
      ("items", Json.arr (← (← listElements args[0]!).mapM wireExpressionJson))]
  | _ => throwError "claim data contains an unresolved expression"

/-- Applications reuse the expression serializer without adding a second schema. -/
def wireApplicationJson (value : Expr) : MetaM Json := do
  let identifier ← field `Zkc.Claims.Wire.Application `identifier value
  let name ← field `Zkc.Claims.Identifier `name identifier
  let version ← field `Zkc.Claims.Identifier `version identifier
  let arguments ← field `Zkc.Claims.Wire.Application `arguments value
  wireExpressionJson (← mkAppM `Zkc.Claims.Wire.Expr.application #[name,
    ← mkAppM ``Option.some #[version], arguments])

def wireRequestJson (value : Expr) : MetaM Json := do
  let get := field `Zkc.Claims.Wire.Request
  let subject ← get `subject value
  let stage ← whnfD (← field `Zkc.Claims.SubjectRef `stage subject)
  let stage ← match headName stage with
    | some `Zkc.Claims.Stage.interactive => pure "interactive"
    | some `Zkc.Claims.Stage.compiledIdeal => pure "compiled-ideal"
    | some `Zkc.Claims.Stage.executableBytes => pure "executable-bytes"
    | _ => throwError "unresolved claim stage: {stage}"
  let artifacts ← (← listElements (← field `Zkc.Claims.SubjectRef `artifacts subject)).mapM fun artifact => do
    return Json.mkObj [("role", Json.str (← literalString (← field `Zkc.Claims.ArtifactDigest `role artifact))),
      ("digest", Json.str (← literalString (← field `Zkc.Claims.ArtifactDigest `digest artifact)))]
  let target ← whnfD (← get `target value)
  let target ← match headName target with
    | some `Zkc.Claims.Wire.TargetRef.retained =>
      pure (Json.mkObj [("protocol", Json.str (← literalString target.getAppArgs[0]!)),
        ("clause", ← naturalJson target.getAppArgs[1]!),
        ("name", Json.str (← literalString target.getAppArgs[2]!))])
    | some `Zkc.Claims.Wire.TargetRef.importedLanguage =>
      pure (Json.mkObj [("protocol", Json.str (← literalString target.getAppArgs[0]!)),
        ("language", ← wireApplicationJson target.appArg!)])
    | _ => throwError "unresolved claim target"
  let accept ← get `accept value
  let output ← whnfD (← field `Zkc.Claims.Wire.Acceptance `output accept)
  unless output.isConstOf ``Bool.true || output.isConstOf ``Bool.false do
    throwError "unresolved acceptance direction"
  let quantity ← whnfD (← get `quantity value)
  let quantity ← match headName quantity with
    | some `Zkc.Claims.Wire.Quantity.scalar => pure (Json.mkObj [("kind", Json.str "scalar"),
        ("expression", ← wireExpressionJson quantity.appArg!)])
    | some `Zkc.Claims.Wire.Quantity.guarantee => pure (Json.mkObj [("kind", Json.str "guarantee"),
        ("form", ← wireApplicationJson quantity.appArg!)])
    | some `Zkc.Claims.Wire.Quantity.charged =>
      let charges ← (← listElements quantity.appArg!).mapM fun pair => do
        return Json.mkObj [("site", Json.str (← literalString (← mkAppM ``Prod.fst #[pair]))),
          ("expression", ← wireExpressionJson (← mkAppM ``Prod.snd #[pair]))]
      pure (Json.mkObj [("kind", Json.str "charged"), ("charges", Json.arr charges)])
    | _ => throwError "unresolved claim quantity"
  let parameter ← whnfD (← get `parameters value)
  let parameter ← if parameter.isAppOf ``Option.some then wireExpressionJson parameter.appArg! else pure Json.null
  let identifier ← get `property value
  let property ← identifierJson identifier
  let .ok propertyFields := property.getObj? | throwError "invalid identifier JSON"
  return Json.mkObj [("subject", Json.mkObj [
      ("unit", Json.str (← literalString (← field `Zkc.Claims.SubjectRef `unitDigest subject))),
      ("entry", Json.str (← literalString (← field `Zkc.Claims.SubjectRef `entry subject))),
      ("stage", Json.str stage), ("artifacts", Json.arr artifacts)]),
    ("property", Json.mkObj (propertyFields.toList ++ [("parameters", parameter)])),
    ("model", ← wireApplicationJson (← get `model value)), ("target", target),
    ("accept", Json.mkObj [("output", Json.bool (output.isConstOf ``Bool.true)),
      ("port", ← naturalJson (← field `Zkc.Claims.Wire.Acceptance `port accept)),
      ("role", ← naturalJson (← field `Zkc.Claims.Wire.Acceptance `role accept)),
      ("path", Json.arr (← (← listElements (← field `Zkc.Claims.Wire.Acceptance `path accept)).mapM naturalJson))]),
    ("quantity", quantity),
    ("capabilities", Json.arr (← (← listElements (← get `capabilities value)).mapM wireApplicationJson))]

/-- Actual closure includes proof bodies and types. Upstream constants are leaves;
owned modules are hashed by the Python reader together with verified pins. -/
def dependencyJson (env : Environment) (starts : Array Name) : Json := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut pending := starts.toList
  let mut rows := #[]
  while true do
    let name :: rest := pending | break
    pending := rest
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    let module := (env.getModuleIdxFor? name).bind fun index =>
      (env.header.modules[index.toNat]?).map (·.module)
    let owned := module.any fun module => repositoryRoots.any (·.isPrefixOf module)
    rows := rows.push (Json.mkObj [("name", Json.str name.toString), ("module", nameJson module),
      ("owned", Json.bool owned), ("statement", Json.str (hex (structuralHash info.type)))])
    unless owned do continue
    pending := info.type.getUsedConstants.toList ++ pending
    if let some body := info.value? true then pending := body.getUsedConstants.toList ++ pending
  return Json.arr (rows.qsort fun a b => a.compress < b.compress)

def unfoldTo (expression : Expr) (names : List Name) : MetaM (Option Expr) := do
  let mut current := expression.headBeta
  for _ in [:64] do
    if (headName current).any (names.contains ·) then return some current
    match ← reduceProj? current with
    | some reduced => current := reduced.headBeta
    | none =>
      match ← unfoldDefinition? current with
      | some unfolded => current := unfolded.headBeta
      | none => return none
  return none

/-- Compiler proof sharing introduces source-less `_proof_` constants. Unwrap
only these administrative nodes; authored theorem bodies remain opaque roots. -/
def proofRoot (env : Environment) (expression : Expr) : MetaM Expr := do
  let mut current := expression.headBeta
  for _ in [:64] do
    let .const name levels := current.getAppFn | return current
    unless name.isInternal || name.toString.contains "_proof_" do return current
    if (declRangeExt.find? env name).isSome then return current
    let some info := env.find? name | return current
    let some body := info.value? true | return current
    current := (mkAppN (body.instantiateLevelParams info.levelParams levels) current.getAppArgs).headBeta
  return current

def receiptRoot (expression : Expr) : MetaM String := do
  let mut current := expression.headBeta
  for _ in [:32] do
    match headName current with
    | some `Zkc.Claims.Receipt.ofEndpoint => return "endpoint"
    | some `Zkc.Claims.Receipt.ofDerivation => return "derivation"
    | some `Zkc.Claims.Receipt.ofTheorem => return "theorem"
    | _ => pure ()
    match ← reduceProj? current with
    | some reduced => current := reduced.headBeta
    | none =>
      match ← unfoldDefinition? current with
      | some unfolded => current := unfolded.headBeta
      | none => return "constructor"
  return "constructor"

/-- Best-effort attribution by referenced Evidence declarations. This is not
an application audit: no callbacks are evaluated and no hypothetical arguments
are invented. Neither missing attribution nor Evidence notes affect receipts. -/
def evidenceAttributionJson (env : Environment) (proof : Expr) : Json := Id.run do
  let mut names := #[]
  for name in proof.getUsedConstants do
    let some info := env.find? name | continue
    let mut type := info.type
    while type.isForall do type := type.bindingBody!
    if (headName type).any (evidenceStructures.contains ·) then
      names := names.push (Json.str name.toString)
  return Json.mkObj [("scope", Json.str "referenced-evidence"), ("declarations", Json.arr names)]

def exceptOk (errorType : Name) (value : Expr) : MetaM Expr :=
  mkAppOptM ``Except.ok #[some (mkConst errorType), none, some value]

/-- Expose an actual existential witness in a checked certificate proof.
The witness equation is compared with the independently reconstructed model
call below. This also handles symbolic model computations whose successful
result needs a theorem, rather than definitional evaluation alone. -/
def existsWitness (env : Environment) (proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut current := proof.headBeta
  for _ in [:128] do
    if current.isAppOf ``Exists.intro then
      let args := current.getAppArgs
      return some (args[args.size - 2]!, args.back!)
    match ← reduceProj? current with
    | some reduced => current := reduced.headBeta
    | none =>
      let reduced ← whnf current
      if reduced != current then current := reduced.headBeta
      else
        let .const name levels := current.getAppFn | return none
        let some info := env.find? name | return none
        let some body := info.value? true | return none
        current := (mkAppN (body.instantiateLevelParams info.levelParams levels) current.getAppArgs).headBeta
  return none

/-- Recover a class argument from the actual typed application, never from
instance search in a potentially different receipt context. -/
def finiteArgument (application carrier : Expr) : MetaM Expr := do
  let mut found : Option Expr := none
  for argument in application.getAppArgs do
    let type ← inferType argument
    unless type.isAppOfArity `Fintype 1 do continue
    unless ← isDefEq type.appArg! carrier do continue
    if let some previous := found then
      unless ← isDefEq previous argument do throwError "ambiguous actual finite model instance"
    found := some argument
  let some finite := found | throwError "missing actual finite model instance"
  return finite

/-- Check a constructor proof in the kernel, even for associations synthesized
for a legacy receipt. Definitional comparisons alone are not exported authority. -/
def kernelFields (target : Expr) (constructor : Name) (last : Option Expr := none) : MetaM Unit := do
  let value ← mkFreshExprMVar target
  let goals ← value.mvarId!.apply (← mkConstWithFreshMVarLevels constructor)
  for index in [:goals.length] do
    let goal := goals[index]!
    if index + 1 == goals.length then
      if let some proof := last then
        goal.assign proof
        continue
    goal.refl
  checkWithKernel (← instantiateMVars value)

/-- One Lean-owned policy for all remaining receipt binders. Parameter instances
must be on the actual subject carriers, and every dependent argument may use
only previously admitted parameters. A proposition is never a parameter. -/
def receiptTelescopeJson (binders : Array Expr) (subjectType request : Expr)
    (context model : Option Expr) (authority : Option Expr := none) : MetaM Json := do
  let subjectArgs := subjectType.getAppArgs
  let uniform := headName subjectType == some `ZkcSecurity.Claims.Subject
  let dependent := authority.isSome && !uniform
  let security := uniform || dependent
  let carriers ← if uniform then pure (subjectArgs.extract 0 2) else if dependent then pure #[] else
    binders.filterM fun binder => do pure (← binder.fvarId!.getDecl).type.isSort
  let mut parameters : Std.HashSet FVarId := {}
  let mut rows := #[]
  let mut conditions := #[]
  let mut accepted := true
  for binder in binders do
    let declaration ← binder.fvarId!.getDecl
    let proof ← isProp declaration.type
    let mut parameter := false
    let mut condition := Json.null
    let mut reason := ""
    if !proof then
      if declaration.type.isSort then
        parameter ← if security then carriers.anyM (isDefEq binder ·) else pure true
      else if dependent && declaration.type.isConstOf `Zkc.Source.Structured.DomainModel then
        parameter ← isDefEq binder subjectArgs[0]!
      else if security && declaration.type.isConstOf ``String && declaration.binderInfo == .default then
        if let some context := context then
          if headName (← inferType context) == some `ZkcSecurity.Claims.ModelContext then
            let binding ← whnfD (← field `ZkcSecurity.Claims.ModelContext `application context)
            if binding.isAppOf ``Option.some then
              let value ← field `ZkcSecurity.Claims.ApplicationBinding `value binding.appArg!
              parameter ← isDefEq binder value
      else if !dependent && (← modelInstance declaration) then
        parameter := true
        for argument in declaration.type.getAppArgs do
          let type ← whnf (← inferType argument)
          if type.isSort && !(← carriers.anyM (isDefEq argument ·)) then parameter := false
      -- In particular a carrier/instance cannot depend on a rejected proof,
      -- Type-valued wrapper or an authorized condition that produces values.
      if parameter then
        for dependency in (Lean.collectFVars ({} : Lean.CollectFVars.State) declaration.type).fvarIds do
          unless parameters.contains dependency do parameter := false
    else if uniform then
      let application ← field `Zkc.Claims.Wire.Request `model request
      let recognized ← unfoldTo declaration.type
        [`ZkcSecurity.Claims.FaithfulScalarAction, `ZkcSecurity.Claims.DLogSearchHard]
      if let some actual := recognized then
        let hard := headName actual == some `ZkcSecurity.Claims.DLogSearchHard
        let key ← mkConstWithFreshMVarLevels (if hard then
          `ZkcSecurity.Claims.PremiseKey.dlogSearch else `ZkcSecurity.Claims.PremiseKey.faithfulScalarAction)
        let authorized ← whnfD (← mkAppM `ZkcSecurity.Claims.premiseAuthorized #[application, key])
        let mut expected : Option Expr := none
        if hard then
          if let some model := model then
            let queries ← whnfD (← field `ZkcSecurity.Claims.Model `queries model)
            if queries.isAppOf `ZkcSecurity.Claims.QueryLimit.fixed then
              expected := some (mkAppN (← mkConstWithFreshMVarLevels `ZkcSecurity.Claims.DLogSearchHard)
                #[subjectArgs[0]!, subjectArgs[1]!, subjectArgs[2]!, subjectArgs[4]!,
                  subjectArgs[5]!, subjectArgs[6]!, queries.appArg!])
        else
          expected := some (mkAppN (← mkConstWithFreshMVarLevels `ZkcSecurity.Claims.FaithfulScalarAction)
            #[subjectArgs[0]!, subjectArgs[1]!, subjectArgs[2]!, subjectArgs[4]!, subjectArgs[5]!])
        let argumentsMatch ← match expected with
          | some expectedType => isDefEq declaration.type expectedType
          | none => pure false
        if !authorized.isConstOf ``Bool.true then reason := "registered but unauthorized premise"
        else if !argumentsMatch then reason := "substituted premise arguments or unsupported model parameters"
        else
          let identifier ← mkAppM `ZkcSecurity.Claims.PremiseKey.identifier #[key]
          let name ← literalString (← field `Zkc.Claims.Identifier `name identifier)
          let version ← naturalJson (← field `Zkc.Claims.Identifier `version identifier)
          condition ← pure (Json.mkObj [("id", Json.str (name ++ "@" ++ version.compress)),
            ("identifier", ← identifierJson identifier),
            ("category", Json.str (if hard then "hardness" else "model")),
            ("schema", nameJson (headName actual)), ("arguments", ← argumentsJson actual),
            ("instantiated", Json.str (toString (← ppExpr declaration.type)))])
          conditions := conditions.push condition
    if parameter then parameters := parameters.insert binder.fvarId!
    let admitted := parameter || condition != Json.null
    if !admitted then
      accepted := false
      if reason.isEmpty then reason := if proof then "omitted premise" else "hidden parameter"
    rows := rows.push (Json.mkObj [("binder", Json.str (binderName declaration.binderInfo)),
      ("type", Json.str (toString (← ppExpr declaration.type))),
      ("classification", Json.str (if parameter then "parameter" else if condition != Json.null then "authorized" else "refused")),
      ("reason", Json.str reason)])
  return Json.mkObj [("accepted", Json.bool accepted), ("binders", Json.arr rows),
    ("conditions", Json.arr conditions)]

/-- Named indices keep the record reader independent of a wrapper's implicit
parameter count. These are type indices, never proof-body attribution. -/
def namedIndex (application : Expr) (parameter : Name) : MetaM Expr := do
  let some head := headName application | throwError "missing indexed structure"
  let names ← forallTelescope (← getConstInfo head).type fun binders _ =>
    binders.mapM fun binder => binder.fvarId!.getUserName
  let some index := names.findIdx? (· == parameter) | throwError "missing index {parameter}"
  return application.getAppArgs[index]!

/-- Internal data reconstructed from the closed authority's checked indices.
No author registry installs a view, a binder policy, or a meaning callback. -/
structure AuthorityView where
  authority : Expr
  subject : Expr
  semanticSubject : Expr
  subjectType : Expr
  shape : Name

def authorityView (authority subject : Expr) : MetaM AuthorityView := do
  let type ← inferType authority
  unless type.isAppOfArity `ZkcSecurity.Claims.CanonicalAuthority 1 do
    throwError "unrecognized canonical authority type"
  unless ← isDefEq type.appArg! (← inferType subject) do
    throwError "canonical authority differs from actual subject type"
  let constructor ← whnfD authority
  let some shape := headName constructor | throwError "unresolved canonical authority"
  unless [`ZkcSecurity.Claims.CanonicalAuthority.uniform,
      `ZkcSecurity.Claims.CanonicalAuthority.domains,
      `ZkcSecurity.Claims.CanonicalAuthority.authoredPair].contains shape do
    throwError "unknown canonical authority shape"
  let semanticSubject ← if shape == `ZkcSecurity.Claims.CanonicalAuthority.authoredPair then
      mkAppM ``ULift.down #[subject] else pure subject
  return ⟨authority, subject, semanticSubject, ← inferType semanticSubject, shape⟩

/-- Inspect typed indices and actual proof applications. Provenance is emitted
separately as a claim to audit, never as the authority for these facts. -/
def receiptJson (env : Environment) (info : ConstantInfo) (binders : Array Expr) (body value : Expr) : MetaM Json := do
  let certificateType := body
  let certificateValue := value
  let certificateHead := headName body
  let canonicalCertificate := certificateHead == some `ZkcSecurity.Claims.CanonicalReceipt
  let authorCertificate := certificateHead == some `ZkcSecurity.Claims.AuthorExtensionReceipt
  let authority ← if canonicalCertificate || authorCertificate then
      pure (some (← namedIndex certificateType `authority)) else pure none
  let view ← match authority with
    | none => pure none
    | some actual => pure (some (← authorityView actual (← namedIndex certificateType `subject)))
  let dependentCertificate := view.any (·.shape != `ZkcSecurity.Claims.CanonicalAuthority.uniform)
  let value ← if dependentCertificate then field certificateHead.get! `receipt value else
    match headName body with
    | some `ZkcSecurity.Claims.CanonicalReceipt => mkAppM `ZkcSecurity.Claims.CanonicalReceipt.toAdmittedReceipt #[value]
    | some `ZkcSecurity.Claims.AuthorExtensionReceipt => mkAppM `ZkcSecurity.Claims.AuthorExtensionReceipt.toAdmittedReceipt #[value]
    | _ => pure value
  let body ← inferType value
  let wrapped := headName body == some `ZkcSecurity.Claims.AdmittedReceipt
  let outerValue := value
  let outerBody := body
  let value ← if wrapped then field `ZkcSecurity.Claims.AdmittedReceipt `receipt value else pure value
  let body ← if wrapped then inferType value else pure body
  let args := body.getAppArgs
  unless args.size == 7 do throwError "unexpected Receipt index arity"
  let request := args[4]!
  let resolved := args[5]!
  let meaning := args[6]!
  let resolvedType ← inferType resolved
  let meaningType ← inferType meaning
  unless headName resolvedType == some `Zkc.Claims.Resolved &&
      headName meaningType == some `Zkc.Claims.Evaluated do throwError "unrecognized receipt indices"
  let proof ← field `Zkc.Claims.Receipt `proof value
  let proposition ← field `Zkc.Claims.Evaluated `proposition meaning
  let proofType ← inferType proof
  let matched ← isDefEq proofType proposition
  let constructor ← whnfD value
  let actualProof ← try
    if constructor.isAppOf `Zkc.Claims.Receipt.mk then
      let constructorArguments := constructor.getAppArgs
      proofRoot env constructorArguments[constructorArguments.size - 4]!
    else pure proof
    catch _ => pure proof
  let actualRoot ← try receiptRoot value catch _ => pure "unattributed"
  let subject := args[3]!
  let semanticSubject := (view.map (·.semanticSubject)).getD subject
  let subjectType ← inferType semanticSubject
  let subjectArgs := subjectType.getAppArgs
  let subjectFacts ← if headName subjectType == some `ZkcSecurity.Claims.Subject && subjectArgs.size >= 2 then do
      let art := subjectArgs[subjectArgs.size - 2]!
      let original ← field `ZkcSecurity.Endpoint.Artifacts `original art
      let participant ← field `ZkcSecurity.Endpoint.Artifacts `participant art
      pure (Json.mkObj [("subject_head", nameJson (headName subject)),
        ("artifacts_head", nameJson (headName art)),
        ("original_source", Json.str (← literalString (← field `Zkc.Source.Structured.Snapshot `source original))),
        ("original_entry", Json.str (← literalString (← field `Zkc.Source.Structured.Snapshot `entry original))),
        ("participant_source", Json.str (← literalString (← field `Zkc.Construction.Participant `source participant))),
        ("participant_candidate", Json.str (← literalString (← field `Zkc.Construction.Participant `candidate participant)))])
    else if dependentCertificate then do
      let authority := authority.get!
      let constructor ← whnfD authority
      if headName constructor == some `ZkcSecurity.Claims.CanonicalAuthority.domains then
        let art := subjectArgs.back!
        let original ← field `ZkcSecurity.Endpoint.Domain.Artifacts `original art
        let participant ← field `ZkcSecurity.Endpoint.Domain.Artifacts `participant art
        pure (Json.mkObj [("subject_head", nameJson (headName subject)),
          ("artifacts_head", nameJson (headName art)),
          ("original_source", Json.str (← literalString (← field `Zkc.Source.Structured.Snapshot `source original))),
          ("original_entry", Json.str (← literalString (← field `Zkc.Source.Structured.Snapshot `entry original))),
          ("participant_source", Json.str (← literalString (← field `Zkc.Construction.Participant `source participant))),
          ("participant_candidate", Json.str (← literalString (← field `Zkc.Construction.Participant `candidate participant)))])
      else
        let original := subjectArgs[1]!
        let selection := subjectArgs.back!
        let artifacts ← field `Zkc.Construction.AuthoredPair.Selection `artifacts selection
        let producer ← field `Zkc.Construction.AuthoredPair.Artifacts `producer artifacts
        let validator ← field `Zkc.Construction.AuthoredPair.Artifacts `validator artifacts
        pure (Json.mkObj [("subject_head", nameJson (headName subject)),
          ("artifacts_head", nameJson (headName artifacts)),
          ("original_source", Json.str (← literalString (← field `Zkc.Source.Structured.Snapshot `source original))),
          ("original_entry", Json.str (← literalString (← field `Zkc.Source.Structured.Snapshot `entry original))),
          ("producer_source", Json.str (← literalString (← field `Zkc.Construction.Participant `source producer))),
          ("producer_candidate", Json.str (← literalString (← field `Zkc.Construction.Participant `candidate producer))),
          ("participant_source", Json.str (← literalString (← field `Zkc.Construction.Participant `source validator))),
          ("participant_candidate", Json.str (← literalString (← field `Zkc.Construction.Participant `candidate validator)))])
    else pure Json.null
  let honestInputPolicy ← if headName subjectType == some `ZkcSecurity.Claims.HonestPair.Subject then do
      let policy ← field `ZkcSecurity.Claims.HonestPair.Subject `inputPolicy semanticSubject
      let description ← listElements (← mkAppM `ZkcSecurity.Claims.HonestPair.InputPolicy.description #[policy])
      pure (Json.arr (← description.mapM fun row => do return Json.str (← literalString row)))
    else pure Json.null
  let resolvedConstructor ← whnfD resolved
  unless resolvedConstructor.isAppOf `Zkc.Claims.Resolved.mk do throwError "unresolved Resolved constructor"
  let resolvedFields := resolvedConstructor.getAppArgs
  let property := resolvedFields[resolvedFields.size - 4]!
  let entry ← field `Zkc.Claims.Resolved `entry resolved
  let entryIdentifier ← field `Zkc.Claims.Export `identifier entry
  let registeredIdentifier ← identifierJson entryIdentifier
  let registeredSchema ← literalString (← field `Zkc.Claims.Export `schema entry)
  let lookup ← whnfD (← mkAppM `Zkc.Claims.Registry.lookup #[args[1]!, entryIdentifier])
  let lookupChecked ← if lookup.isAppOf ``Except.ok then isDefEq lookup.appArg! entry else pure false
  -- Recognize the selected definition, not the registry container. Unrelated
  -- exports may be appended to either registry without changing this meaning.
  let selected ← unfoldTo property [`ZkcSecurity.Claims.soundnessProperty, `ZkcSecurity.Claims.knowledgeProperty]
  let mut propertyChecked := false
  let mut exportChecked := false
  let mut modelChecked := false
  let mut modelContext : Option Expr := none
  let mut consumer := ""
  let mut admittedRegistry : Option Expr := if wrapped then some outerBody.getAppArgs[outerBody.getAppArgs.size - 2]! else none
  if dependentCertificate then admittedRegistry := some (← namedIndex certificateType `registry)
  let mut admittedFinite : Option Expr := none
  if wrapped then admittedFinite := some (← finiteArgument outerBody subjectArgs[0]!)
  if let some selected := selected then
    if headName subjectType == some `ZkcSecurity.Claims.Subject then
      let modelRegistry := selected.getAppArgs.back!
      if let some associated := admittedRegistry then
        unless ← isDefEq associated modelRegistry do throwError "admitted model registry differs from the selected property's actual registry"
      admittedRegistry := some modelRegistry
      let actualFinite ← finiteArgument selected subjectArgs[0]!
      if let some associated := admittedFinite then
        unless ← isDefEq associated actualFinite do throwError "admitted finite instance differs from the selected property's actual instance"
      admittedFinite := some actualFinite
      let canonicalProperty := selected
      propertyChecked ← isDefEq property canonicalProperty
      let canonicalRegistry := mkAppN (← mkConstWithFreshMVarLevels `ZkcSecurity.Claims.properties)
        selected.getAppArgs
      let canonicalLookup ← whnfD (← mkAppM `Zkc.Claims.Registry.lookup #[canonicalRegistry, entryIdentifier])
      if canonicalLookup.isAppOf ``Except.ok then
        exportChecked ← isDefEq entry canonicalLookup.appArg!
  if let some modelRegistry := admittedRegistry then
    if headName subjectType == some `ZkcSecurity.Claims.Subject then
      let modelApplication ← field `Zkc.Claims.Wire.Request `model request
      let modelIdentifier ← field `Zkc.Claims.Wire.Application `identifier modelApplication
      let modelLookup ← whnfD (← mkAppM `Zkc.Claims.Registry.lookup #[modelRegistry, modelIdentifier])
      if modelLookup.isAppOf ``Except.ok then
        let actualEntry := modelLookup.appArg!
        let definition ← whnfD (← field `Zkc.Claims.Export `definition actualEntry)
        if definition.isAppOf ``Option.some then
          let elaborator ← whnfD definition.appArg!
          -- The context is extracted only to propose a canonical comparator.
          -- Equality of the complete export (including its elaborator) is the
          -- authority, so a custom function containing this name cannot pass.
          if let some schema := elaborator.find? (fun e =>
              e.isAppOf `ZkcSecurity.Claims.modelSchema && e.getAppNumArgs >= 4) then
            let context := schema.getAppArgs[3]!
            unless context.hasLooseBVars do
              let canonicalModels ← mkAppM `ZkcSecurity.Claims.models #[context, subjectArgs.back!]
              let canonicalModel ← whnfD (← mkAppM `Zkc.Claims.Registry.lookup #[canonicalModels, modelIdentifier])
              if canonicalModel.isAppOf ``Except.ok then
                modelChecked ← isDefEq actualEntry canonicalModel.appArg!
                if modelChecked then modelContext := some context
  if propertyChecked && exportChecked && modelChecked && lookupChecked then
    consumer := if (selected.bind headName) == some `ZkcSecurity.Claims.soundnessProperty then "soundness@0" else "knowledge@0"
  if canonicalCertificate || authorCertificate then
    modelContext := some (← namedIndex certificateType `context)
    let modelCertificate ← field certificateHead.get! `modelAdmission certificateValue
    checkWithKernel modelCertificate
    modelChecked := true
    let association ← field certificateHead.get! `association certificateValue
    checkWithKernel association
    if canonicalCertificate then
      let key ← namedIndex certificateType `key
      let target ← mkAppM `ZkcSecurity.Claims.CanonicalAdmission #[authority.get!, admittedRegistry.get!, key, resolved]
      unless ← isDefEq (← inferType association) target do throwError "wrong canonical association indices"
      propertyChecked := true
      exportChecked := true
      let identifier ← field `Zkc.Claims.Wire.Request `property request
      let name ← field `Zkc.Claims.Identifier `name identifier
      let version ← field `Zkc.Claims.Identifier `version identifier
      consumer := (← literalString name) ++ "@" ++ (← naturalJson version).compress
  let canonicalRegistry := propertyChecked && exportChecked && modelChecked && lookupChecked
  let mut actualModel : Option Expr := none
  let mut modelProof : Option Expr := none
  let admission ← if headName subjectType == some `ZkcSecurity.Claims.Subject then do
      let checked ← mkAppM `ZkcSecurity.Claims.Subject.check #[subject, request]
      let subjectResult ← whnfD checked
      let checkedUnit ← exceptOk `Zkc.Claims.ResolutionError (mkConst ``Unit.unit)
      let subjectChecked ← isDefEq checked checkedUnit
      let mut modelStatus := "unassociated"
      let mut modelValue := Json.null
      let mut modelCertificateChecked := false
      let mut successAuthority := "none"
      if let some registry := admittedRegistry then
        let modelApplication ← field `Zkc.Claims.Wire.Request `model request
        let art := subjectArgs[subjectArgs.size - 2]!
        let original ← field `ZkcSecurity.Endpoint.Artifacts `original art
        let some finite := admittedFinite | throwError "missing associated model instance"
        let actual := mkAppN (← mkConstWithFreshMVarLevels `ZkcSecurity.Claims.resolveModel)
          #[registry, subjectArgs[0]!, finite, original, subjectArgs.back!, modelApplication]
        if wrapped then
          let proof ← field `ZkcSecurity.Claims.AdmittedReceipt `modelAdmitted outerValue
          let expected ← withLocalDeclD `actual (mkConst `ZkcSecurity.Claims.Model) fun model => do
            let equation ← mkEq actual (← exceptOk `Zkc.Claims.ResolutionError (← exceptOk `Zkc.Claims.Incomplete model))
            mkAppM ``Exists #[← mkLambdaFVars #[model] equation]
          modelCertificateChecked ← isDefEq (← inferType proof) expected
        let outcome ← whnfD actual
        if outcome.isAppOf ``Except.ok then
          let inner ← whnfD outcome.appArg!
          if inner.isAppOf ``Except.ok then
            let expected ← exceptOk `Zkc.Claims.ResolutionError (← exceptOk `Zkc.Claims.Incomplete inner.appArg!)
            if ← isDefEq actual expected then
              modelStatus := "admitted"
              successAuthority := "definitional-evaluation"
              modelValue := Json.str (toString (← ppExpr inner.appArg!))
              actualModel := some inner.appArg!
              let witness := inner.appArg!
              let predicate ← withLocalDeclD `model (mkConst `ZkcSecurity.Claims.Model) fun model => do
                mkLambdaFVars #[model] (← mkEq actual
                  (← exceptOk `Zkc.Claims.ResolutionError (← exceptOk `Zkc.Claims.Incomplete model)))
              modelProof := some (← mkAppOptM ``Exists.intro
                #[none, some predicate, some witness, some (← mkEqRefl actual)])
          else if inner.isAppOf ``Except.error then modelStatus := "registered-undefined"
          else modelStatus := "open"
        else if outcome.isAppOf ``Except.error then modelStatus := "refused"
        else modelStatus := "open"
        if modelStatus == "open" && wrapped && modelCertificateChecked then
          modelStatus := "admitted"
          successAuthority := "kernel-existence"
          let certificate ← field `ZkcSecurity.Claims.AdmittedReceipt `modelAdmitted outerValue
          modelProof := some certificate
          let witness ← try existsWitness env certificate catch _ => pure none
          if let some (model, proof) := witness then
            let expected ← mkEq actual (← exceptOk `Zkc.Claims.ResolutionError (← exceptOk `Zkc.Claims.Incomplete model))
            if ← isDefEq (← inferType proof) expected then
              modelStatus := "admitted"
              successAuthority := "kernel-equation"
              modelValue := Json.str (toString (← ppExpr model))
              modelProof := some certificate
      -- An actual typed wrapper certificate is additional checked association,
      -- never a substitute for recomputing either admission operation.
      let certificateChecked ← if wrapped then do
          let proof ← field `ZkcSecurity.Claims.AdmittedReceipt `checked outerValue
          let expected ← mkEq checked checkedUnit
          isDefEq (← inferType proof) expected
        else pure false
      pure (Json.mkObj [("security_subject", Json.bool true), ("associated", Json.bool admittedRegistry.isSome),
        ("association", Json.str (if wrapped then "typed-certificate" else "selected-property")),
        ("certificate_checked", Json.bool (certificateChecked && modelCertificateChecked)),
        ("subject_checked", Json.bool subjectChecked),
        ("subject_result", nameJson (headName subjectResult)), ("model_status", Json.str modelStatus),
        ("model_value", modelValue), ("success_authority", Json.str successAuthority)])
    else if dependentCertificate then do
      let authority := authority.get!
      let registry := admittedRegistry.get!
      let context := modelContext.get!
      let application ← field `Zkc.Claims.Wire.Request `model request
      let certificate ← field certificateHead.get! `modelAdmission certificateValue
      let target ← mkAppM `ZkcSecurity.Claims.CanonicalModelAdmission
        #[authority, registry, context, subject, application]
      unless ← isDefEq (← inferType certificate) target do throwError "wrong selected model association indices"
      checkWithKernel certificate
      let association ← field certificateHead.get! `association certificateValue
      let checked ← field (if canonicalCertificate then `ZkcSecurity.Claims.CanonicalAdmission
        else `ZkcSecurity.Claims.AuthorExtensionAdmission) `checked association
      let actualCheck ← mkAppM `ZkcSecurity.Claims.CanonicalAuthority.check #[authority, subject, request]
      let expected ← mkEq actualCheck (← exceptOk `Zkc.Claims.ResolutionError (mkConst ``Unit.unit))
      unless ← isDefEq (← inferType checked) expected do throwError "wrong dependent subject admission indices"
      checkWithKernel checked
      pure (Json.mkObj [("security_subject", Json.bool true), ("associated", Json.bool true),
        ("association", Json.str "typed-certificate"), ("certificate_checked", Json.bool true),
        ("subject_checked", Json.bool true), ("model_status", Json.str "admitted"),
        ("success_authority", Json.str "kernel-existence")])
    else pure (Json.mkObj [("security_subject", Json.bool false)])
  let mut authorityKind := "generic"
  let mut authorityChecked := false
  -- A generic Subject does not confer authority to use a reserved security key.
  -- Keep generic core receipts usable without treating them as canonical claims.
  if (← getEnv).contains `ZkcSecurity.Claims.reservedIdentifier then
    let identifier ← field `Zkc.Claims.Wire.Request `property request
    let reserved ← whnfD (← mkAppM `ZkcSecurity.Claims.reservedIdentifier #[identifier])
    if reserved.isConstOf ``Bool.true then authorityKind := "reserved"
  if headName subjectType == some `ZkcSecurity.Claims.Subject then
    let identifier ← field `Zkc.Claims.Wire.Request `property request
    let reserved ← whnfD (← mkAppM `ZkcSecurity.Claims.reservedIdentifier #[identifier])
    authorityKind := if reserved.isConstOf ``Bool.true then "reserved" else "author"
    try
      if let some registry := admittedRegistry then
        if let some context := modelContext then
          if let some admissionProof := modelProof then
            let art := subjectArgs[subjectArgs.size - 2]!
            let _original ← field `ZkcSecurity.Endpoint.Artifacts `original art
            let application ← field `Zkc.Claims.Wire.Request `model request
            let some finite := admittedFinite | throwError "missing actual canonical finite instance"
            let uniformAuthority ← if let some authority := authority then pure authority else do
              let sampleType ← mkAppM `SampleableType #[subjectArgs[0]!]
              let inhabitedType ← mkAppM ``Inhabited #[subjectArgs[0]!]
              let mut sample ← binders.findM? fun binder => do isDefEq (← inferType binder) sampleType
              let mut inhabited ← binders.findM? fun binder => do isDefEq (← inferType binder) inhabitedType
              if let some property := selected then
                for argument in property.getAppArgs do
                  if ← isDefEq (← inferType argument) sampleType then sample := some argument
                  if ← isDefEq (← inferType argument) inhabitedType then inhabited := some argument
              if sample.isNone then
                sample := some (← mkAppOptM `ZkcSecurity.Claims.CanonicalAuthority.finiteFieldSampling
                  #[some subjectArgs[0]!, some subjectArgs[2]!, some finite])
              if inhabited.isNone then
                inhabited := some (← mkAppOptM `ZkcSecurity.Claims.CanonicalAuthority.fieldInhabited
                  #[some subjectArgs[0]!, some subjectArgs[2]!])
              let parameters := subjectArgs.extract 0 (subjectArgs.size - 2)
              mkAppOptM `ZkcSecurity.Claims.CanonicalAuthority.uniform
                (parameters.map some |>.push sample |>.push (some finite) |>.push inhabited
                  |>.push (some art) |>.push (some subjectArgs.back!))
            let _ ← authorityView uniformAuthority subject
            let modelTarget ← mkAppM `ZkcSecurity.Claims.CanonicalModelAdmission
              #[uniformAuthority, registry, context, subject, application]
            if canonicalCertificate || authorCertificate then
              let proof ← field certificateHead.get! `modelAdmission certificateValue
              unless ← isDefEq (← inferType proof) modelTarget do throwError "wrong canonical model certificate indices"
              checkWithKernel proof
            else kernelFields modelTarget `ZkcSecurity.Claims.CanonicalModelAdmission.mk (some admissionProof)
            if canonicalRegistry then
              let key ← whnfD (← mkAppM `ZkcSecurity.Claims.PropertyKey.ofIdentifier? #[identifier])
              unless key.isAppOf ``Option.some do throwError "canonical key is undefined"
              let target ← mkAppM `ZkcSecurity.Claims.CanonicalAdmission #[uniformAuthority, registry, key.appArg!, resolved]
              if canonicalCertificate then
                let proof ← field certificateHead.get! `association certificateValue
                unless ← isDefEq (← inferType proof) target do throwError "wrong canonical certificate key"
                checkWithKernel proof
              else kernelFields target `ZkcSecurity.Claims.CanonicalAdmission.mk
              authorityKind := "canonical"
              authorityChecked := true
            else if authorityKind == "author" then
              let target ← mkAppM `ZkcSecurity.Claims.AuthorExtensionAdmission #[uniformAuthority, resolved]
              if authorCertificate then
                let proof ← field certificateHead.get! `association certificateValue
                unless ← isDefEq (← inferType proof) target do throwError "wrong author certificate indices"
                checkWithKernel proof
              else kernelFields target `ZkcSecurity.Claims.AuthorExtensionAdmission.mk
              authorityChecked := true
    catch _ => pure ()
  if dependentCertificate then
    let identifier ← field `Zkc.Claims.Wire.Request `property request
    let reserved ← whnfD (← mkAppM `ZkcSecurity.Claims.reservedIdentifier #[identifier])
    authorityKind := if canonicalCertificate then "canonical" else if reserved.isConstOf ``Bool.false then "author" else "reserved"
    authorityChecked := canonicalCertificate || authorityKind == "author"
  let telescope ← receiptTelescopeJson binders subjectType request modelContext actualModel authority

  let typedArguments ← whnfD (← field `Zkc.Claims.Resolved `arguments resolved)
  let quantityKind ← if typedArguments.isAppOf ``Except.ok then do
      let argument := typedArguments.appArg!
      let argumentType ← inferType argument
      if headName argumentType == some `ZkcSecurity.Claims.SoundnessRequest then do
        let quantity ← whnfD (← field `ZkcSecurity.Claims.SoundnessRequest `quantity argument)
        pure (match headName quantity with
          | some `ZkcSecurity.Claims.SoundnessQuantity.scalar => "scalar"
          | some `ZkcSecurity.Claims.SoundnessQuantity.charged => "charged"
          | _ => "unknown")
      else if headName argumentType == some `ZkcSecurity.Claims.Domain.SoundnessArguments then do
        let quantity ← whnfD (← field `ZkcSecurity.Claims.Domain.SoundnessArguments `quantity argument)
        pure (match headName quantity with
          | some `ZkcSecurity.Claims.Domain.SoundnessQuantity.scalar => "scalar"
          | some `ZkcSecurity.Claims.Domain.SoundnessQuantity.charged => "charged"
          | _ => "unknown")
      else if dependentCertificate && view.any
          (·.shape == `ZkcSecurity.Claims.CanonicalAuthority.authoredPair) then pure "scalar"
      else if headName argumentType == some `ZkcSecurity.Claims.KnowledgeRequest then pure "guarantee"
      else pure "extension"
    else pure "extension"
  let coverage ← if dependentCertificate && view.any
      (·.shape == `ZkcSecurity.Claims.CanonicalAuthority.authoredPair) then
      pure (Json.mkObj [("mode", Json.str "honest-inputs"), ("checked", Json.bool true)])
    else if canonicalRegistry && typedArguments.isAppOf ``Except.ok then do
      let argument := typedArguments.appArg!
      let domain := view.any (·.shape == `ZkcSecurity.Claims.CanonicalAuthority.domains)
      let modelNamespace := if domain then `ZkcSecurity.Claims.Domain.SoundnessArguments
        else if consumer == "soundness@0" then `ZkcSecurity.Claims.SoundnessRequest else `ZkcSecurity.Claims.KnowledgeRequest
      let model ← field modelNamespace (if domain then `selected else `model) argument
      let form ← whnfD (← field `ZkcSecurity.Claims.Model `form model)
      let binding ← whnfD (← field `ZkcSecurity.Claims.Model `applicationBinding model)
      if binding.isAppOf ``Option.none then
        pure (Json.mkObj [("mode", Json.str "fixed-statement"),
          ("checked", Json.bool (headName form == some `ZkcSecurity.Endpoint.Form.fixed))])
      else if binding.isAppOf ``Option.some then do
        let binding := binding.appArg!
        let symbol ← literalString (← field `ZkcSecurity.Claims.ApplicationBinding `symbol binding)
        let application ← field `ZkcSecurity.Claims.ApplicationBinding `value binding
        let mode ← whnfD (← field `ZkcSecurity.Claims.ApplicationBinding `coverage binding)
        let parameter := headName mode == some `ZkcSecurity.Claims.ContextCoverage.parameter
        let wireModel ← field `Zkc.Claims.Wire.Request `model request
        let wireArguments ← field `Zkc.Claims.Wire.Application `arguments wireModel
        let named ← whnfD (← mkAppM `ZkcSecurity.Claims.named #[wireArguments, toExpr "application"])
        let referenceMatches ← if named.isAppOf ``Option.some then do
            let expression ← whnfD named.appArg!
            if expression.isAppOf `Zkc.Claims.Wire.Expr.reference then
              pure ((← literalString expression.appArg!) == symbol)
            else pure false
          else pure false
        let candidates ← binders.filterM fun binder => do
          let declaration ← binder.fvarId!.getDecl
          return declaration.userName.toString == symbol && (← isDefEq declaration.type (mkConst ``String))
        let sameBinder ← if candidates.size == 1 then isDefEq application candidates[0]! else pure false
        let contextMatches ← isDefEq (← field `ZkcSecurity.Claims.ModelContext `application modelContext.get!)
          (← field `ZkcSecurity.Claims.Model `applicationBinding model)
        let valueMatches ← isDefEq application (← field `ZkcSecurity.Claims.Model `application model)
        let fixedValue ← if parameter then pure Json.null else
          try pure (Json.str (← literalString application)) catch _ => pure Json.null
        let fixedChecked := !parameter && candidates.isEmpty && fixedValue != Json.null
        let designated ← if candidates.size == 1 then do
            let binder := candidates[0]!
            pure (Json.mkObj [("name", Json.str (← binder.fvarId!.getDecl).userName.toString),
              ("index", toJson (binders.findIdx? (· == binder)).get!)])
          else pure Json.null
        pure (Json.mkObj [("mode", Json.str (if parameter then "parameter" else "fixed")),
          ("symbol", Json.str symbol), ("value", Json.str (toString (← ppExpr application))),
          ("fixed_value", fixedValue), ("designated_binder", designated),
          ("value_is_binder", Json.bool sameBinder), ("reference_matches", Json.bool referenceMatches),
          ("context_matches", Json.bool contextMatches), ("model_value_matches", Json.bool valueMatches),
          ("checked", Json.bool (contextMatches && valueMatches && referenceMatches &&
            (headName form == some `ZkcSecurity.Endpoint.Form.adaptive) && (if parameter then sameBinder else fixedChecked)))])
      else pure (Json.mkObj [("checked", Json.bool false)])
    else pure Json.null
  let requiredLinks ← mkAppM `Zkc.Claims.Resolved.requiredLinks #[resolved]
  let length ← mkAppM ``List.length #[requiredLinks]
  let indices ← listElements (← mkAppM `List.finRange #[length])
  let mut linkGoals : Array (String × Expr) := #[]
  let mut links := #[]
  for index in indices do
    let obligation ← whnfD (← mkAppM ``List.get #[requiredLinks, index])
    unless obligation.isAppOf `Zkc.Claims.Obligation.mk do throwError "unresolved registered obligation"
    let goal := obligation.getAppArgs[2]!
    let identifier ← literalString (← field `Zkc.Claims.Obligation `identifier obligation)
    let proof ← whnfD (← mkAppM `Zkc.Claims.Receipt.linkProofs #[value, index])
    links := links.push (Json.mkObj [("index", toJson linkGoals.size), ("identifier", Json.str identifier),
      ("goal", Json.str (toString (← ppExpr goal))), ("goal_head", nameJson (headName goal)),
      ("context", Json.str (← literalString (← field `Zkc.Claims.Obligation `context obligation))),
      ("expected_responsibility_layer", Json.str (← literalString (← mkAppM `Zkc.Claims.Responsibility.tag
        #[← field `Zkc.Claims.Obligation `responsibility obligation]))),
      ("proved", Json.bool (proof.isAppOf ``Option.some))])
    linkGoals := linkGoals.push (identifier, goal)
  -- Derive expected obligations independently of the registry's chosen list.
  -- Compare the subject argument before goal reduction: closed checker equations
  -- for two distinct artifacts may otherwise normalize to similar propositions.
  let stageLinks ← if headName subjectType == some `ZkcSecurity.Claims.Subject || dependentCertificate then do
      let endpoint ← if dependentCertificate then pure (mkConst `ZkcSecurity.Endpoint.Semantics.idealMeaning)
        else whnfD subjectArgs.back!
      let (stage, covered) ← match headName endpoint with
        | some `ZkcSecurity.Endpoint.Semantics.idealMeaning => pure ("compiled-ideal", "ideal-meaning")
        | some `ZkcSecurity.Endpoint.Semantics.executableBytes => pure ("executable-bytes", "interpreted-executable-bytes")
        | _ => throwError "unresolved interpreted subject endpoint"
      let expected ← listElements (← if let some authority := authority then
          mkAppM `ZkcSecurity.Claims.CanonicalAuthority.links #[authority, subject]
        else mkAppM `ZkcSecurity.Claims.Subject.stageLinks #[subject])
      let obligations ← expected.mapM fun expression => do
        let obligation ← whnfD expression
        unless obligation.isAppOf `Zkc.Claims.Obligation.mk do throwError "unresolved expected stage obligation"
        let identifier ← literalString (← field `Zkc.Claims.Obligation `identifier obligation)
        let goal := obligation.getAppArgs[2]!
        let some goalHead := headName goal | throwError "expected stage goal has no checked schema"
        let mut comparisons := #[]
        for i in [:linkGoals.size] do
          let (actualIdentifier, actualGoal) := linkGoals[i]!
          if actualIdentifier != identifier then continue
          let application ← unfoldTo actualGoal [goalHead]
          let sameSubject ← match application with
            | some application =>
              if application.getAppArgs.isEmpty then pure false
              else isDefEq application.getAppArgs.back! semanticSubject
            | none => pure false
          -- Comparing large, closed checker goals after a failed subject
          -- match is both unnecessary and expensive. A skipped comparison
          -- is explicit; only two successful checks can discharge a link.
          let goalComparison ← if sameSubject then
              pure (Json.bool (← isDefEq actualGoal goal))
            else pure Json.null
          comparisons := comparisons.push (Json.mkObj [("index", toJson i),
            ("goal_defeq", goalComparison),
            ("subject_matches", Json.bool sameSubject)])
        return Json.mkObj [("identifier", Json.str identifier),
          ("goal", Json.str (toString (← ppExpr goal))), ("goal_head", Json.str goalHead.toString),
          ("goal_identity", Json.str (hex (structuralHash goal))),
          ("context", Json.str (← literalString (← field `Zkc.Claims.Obligation `context obligation))),
          ("expected_responsibility_layer", Json.str (← literalString (← mkAppM `Zkc.Claims.Responsibility.tag
            #[← field `Zkc.Claims.Obligation `responsibility obligation]))),
          ("matches", Json.arr comparisons)]
      let ownedAuthority ← match authority with
        | some authority => pure (some authority)
        | none => pure none
      let roles ← match ownedAuthority with
        | some authority => listElements (← mkAppM `ZkcSecurity.Claims.CanonicalAuthority.artifactRoles #[authority])
        | none =>
          let roles := if stage == "executable-bytes" then
            [("constructed-participant", "constructed_export"), ("verifier-program", "program")]
            else [("constructed-participant", "constructed_export")]
          pure (roles.toArray.map toExpr)
      let roles ← roles.mapM fun pair => do
        return Json.mkObj [("role", Json.str (← literalString (← mkAppM ``Prod.fst #[pair]))),
          ("pipeline_artifact", Json.str (← literalString (← mkAppM ``Prod.snd #[pair])))]
      let covered ← if let some authority := authority then
          literalString (← mkAppM `ZkcSecurity.Claims.CanonicalAuthority.coveredEndpoint #[authority])
        else pure covered
      pure (Json.mkObj [("recognized_subject", Json.bool true), ("stage", Json.str stage),
        ("covered_endpoint", Json.str covered), ("artifact_roles", Json.arr roles),
        ("obligations", Json.arr obligations)])
    else pure (Json.mkObj [("recognized_subject", Json.bool false), ("obligations", Json.arr #[])])
  -- These optional notes never supply or discharge receipt obligations.
  -- Keep attribution failure local: the kernel-checked fields above survive.
  let (provenance, provenanceError) ← try
    let provenance ← field `Zkc.Claims.Receipt `provenance value
    let root ← whnfD (← field `Zkc.Claims.Provenance `root provenance)
    let premises ← (← listElements (← field `Zkc.Claims.Provenance `premises provenance)).mapM fun premise => do
      return Json.mkObj [("identifier", ← identifierJson (← field `Zkc.Claims.PremiseRecord `identifier premise)),
        ("category", nameJson (headName (← whnfD (← field `Zkc.Claims.PremiseRecord `category premise))))]
    let declaredDependencies ← (← listElements (← field `Zkc.Claims.Provenance `dependencies provenance)).mapM fun item =>
      return Json.str (← literalString item)
    pure (Json.mkObj [("root", nameJson (headName root)),
      ("discharger", Json.str (← literalString (← field `Zkc.Claims.Provenance `discharger provenance))),
      ("method", ← identifierJson (← field `Zkc.Claims.Provenance `method provenance)),
      ("dependencies", Json.arr declaredDependencies), ("premises", Json.arr premises)], Json.null)
    catch error => pure (Json.null, Json.str (← error.toMessageData.toString))
  let evidenceAttribution := evidenceAttributionJson env actualProof
  let authorityShape ← match authority with
    | some actual => literalString (← mkAppM `ZkcSecurity.Claims.CanonicalAuthority.kind #[actual])
    | none => pure (if headName subjectType == some `ZkcSecurity.Claims.Subject then "uniform-verifier" else "unknown")
  let authorityProduct ← match authority with
    | some actual => literalString (← mkAppM `ZkcSecurity.Claims.CanonicalAuthority.product #[actual])
    | none => pure "certified_verifier"
  return Json.mkObj [("wire_request", ← wireRequestJson request),
    ("subject", subjectFacts),
    ("admission", admission),
    ("authority", Json.mkObj [("kind", Json.str authorityKind), ("checked", Json.bool authorityChecked),
      ("shape", Json.str authorityShape), ("product", Json.str authorityProduct)]),
    ("telescope", telescope),
    ("evidence_attribution", evidenceAttribution),
    ("property_definition", nameJson (headName property)),
    ("canonical_registry", Json.bool canonicalRegistry),
    ("registry_checks", Json.mkObj [("lookup", Json.bool lookupChecked), ("property_definition", Json.bool propertyChecked),
      ("property_export", Json.bool exportChecked), ("model_export", Json.bool modelChecked)]),
    ("capability_consumer", if canonicalRegistry then Json.str consumer else Json.null),
    ("application_coverage", coverage), ("honest_input_policy", honestInputPolicy),
    ("registered_property", registeredIdentifier), ("registered_schema", Json.str registeredSchema),
    ("quantity_kind", Json.str quantityKind),
    ("exported_capabilities", if consumer == "soundness@0" && quantityKind == "charged" then
      toJson (["capabilities.charged_reduction@0"] : List String) else toJson ([] : List String)),
    ("registry_head", nameJson (headName args[1]!)),
    ("request_head", nameJson (headName request)), ("resolved_head", nameJson (headName resolved)),
    ("evaluated_head", nameJson (headName meaning)), ("indices_checked", Json.bool true),
    ("proof_type_matches", Json.bool matched), ("proposition", Json.str (toString (← ppExpr proposition))),
    ("proposition_binders", ← bindersJson (← whnfD proposition)),
    ("root_route", Json.str actualRoot), ("discharger", nameJson (headName actualProof)),
    ("proof_dependencies", dependencyJson env (actualProof.getUsedConstants ++ outerBody.getUsedConstants)),
    ("dependencies", dependencyJson env #[info.name]),
    ("context", Json.arr (← binders.mapM fun binder => do pure (Json.str (toString (← ppExpr (← inferType binder)))))),
    ("required_links", Json.arr links),
    ("stage_links", stageLinks),
    ("provenance", provenance), ("provenance_error", provenanceError)]

/-- Pretty-printed statement and premises of one declaration, the registered
constants it reaches, the head constant and arguments of its statement and of
its value, every binder, the premise telescope of a statement that is an
instance of a registered property (unfolded once), and the named hypotheses of
an evidence value. -/
def detail (env : Environment) (registered : Std.HashSet Name) (properties : Std.HashSet Name)
    (info : ConstantInfo) : MetaM Json := do
  let statement ← ppExpr info.type
  let premiseText ← forallTelescope info.type fun binders _ => do
    binders.mapM fun binder => do
      let declaration ← binder.fvarId!.getDecl
      return Json.str (toString (← ppExpr declaration.type))
  let (typeHead, typeArguments, property, hypotheses, hypothesesError, claimData) ← forallTelescope info.type fun binders body => do
    let head := headName body
    let property ← match head with
      | some name =>
          if properties.contains name then
            match ← unfoldDefinition? body with
            | some unfolded => pure (Json.mkObj [
                ("statement", Json.str (toString (← ppExpr unfolded))),
                ("premise_telescope", Json.arr ((← premises unfolded).map premiseJson))])
            | none => pure Json.null
          else pure Json.null
      | none => pure Json.null
    let (hypotheses, hypothesesError) ← try
      let hypotheses ← match head with
        | some name =>
            if evidenceStructures.contains name then
              match info.value? (allowOpaque := true) with
              | some _ => hypothesesJson binders (mkAppN (mkConst info.name (info.levelParams.map Level.param)) binders) name
              | none => pure Json.null
            else pure Json.null
        | none => pure Json.null
      pure (hypotheses, Json.null)
      catch error => pure (Json.null, Json.str (← error.toMessageData.toString))
    let value := mkAppN (mkConst info.name (info.levelParams.map Level.param)) binders
    let claimData ← try
      if head == some `Zkc.Claims.Wire.Request then
        let identifier ← field `Zkc.Claims.Wire.Request `property value
        let kind ← if (← getEnv).contains `ZkcSecurity.Claims.reservedIdentifier then do
            let reserved ← whnfD (← mkAppM `ZkcSecurity.Claims.reservedIdentifier #[identifier])
            pure (if reserved.isConstOf ``Bool.true then "reserved" else "author")
          else pure "generic"
        pure (Json.mkObj [("wire_request", ← wireRequestJson value), ("claim_kind", Json.str kind),
          ("telescope", ← receiptTelescopeJson binders (mkConst ``Unit) value none none)])
      else if head == some `Zkc.Claims.Receipt || head == some `ZkcSecurity.Claims.AdmittedReceipt ||
          head == some `ZkcSecurity.Claims.CanonicalReceipt || head == some `ZkcSecurity.Claims.AuthorExtensionReceipt then
        pure (Json.mkObj [("receipt", ← receiptJson env info binders body value)])
      else pure Json.null
      catch error => pure (Json.mkObj [("extraction_error", Json.str (← error.toMessageData.toString))])
    return (head, ← argumentsJson body, property, hypotheses, hypothesesError, claimData)
  let (valueHead, valueArguments) ← match info.value? (allowOpaque := true) with
    | some value => lambdaTelescope value fun _ body => do return (headName body, ← argumentsJson body)
    | none => pure (none, Json.null)
  return Json.mkObj [("statement", Json.str (toString statement)),
    ("premises", Json.arr premiseText),
    ("premise_telescope", Json.arr ((← premises info.type).map premiseJson)),
    ("binders", ← bindersJson info.type),
    ("type_head", nameJson typeHead),
    ("type_arguments", typeArguments),
    ("value_head", nameJson valueHead),
    ("value_arguments", valueArguments),
    ("property", property),
    ("hypotheses", hypotheses), ("hypotheses_error", hypothesesError),
    ("claim_data", claimData),
    ("dependencies", dependencyJson env #[info.name]),
    ("registered", Json.arr ((reached env registered info.name).map (Json.str ·.toString)))]

def record (env : Environment) (registered : Std.HashSet Name) (properties : Std.HashSet Name) (name : Name)
    (info : ConstantInfo) (module : Name) (actualAxioms : Array Name) (detailed : Bool) : MetaM Json := do
  let axioms := actualAxioms.qsort Name.lt |>.map (Json.str ·.toString)
  let doc ← findSimpleDocString? env name (includeBuiltin := false)
  let mut fields : List (String × Json) := [
    ("name", Json.str (privateToUserName? name |>.getD name).toString),
    ("module", Json.str module.toString),
    ("kind", Json.str (kind info)),
    ("statement", Json.mkObj [("structural", Json.str (hex (structuralHash info.type))),
      ("explicit", Json.str (hex (explicitHash env info.type)))]),
    ("axioms", Json.arr axioms),
    ("doc", match doc with | some text => Json.str text | none => Json.null),
    ("tags", Json.arr ((tags env name info).map Json.str))]
  if info.isTheorem then
    fields := fields ++ [("premises", Json.arr ((← premises info.type).map premiseJson))]
  if detailed then
    fields := fields ++ [("detail", ← detail env registered properties info)]
  return Json.mkObj fields

def runMeta {α : Type} (env : Environment) (action : MetaM α) : IO α := do
  let context : Core.Context :=
    { fileName := "<declaration records>", fileMap := default, maxHeartbeats := 0 }
  let (result, _, _) ← action.toIO context { env }
  return result

/-- The JSON `name` of a record line, used to name differences. -/
def lineName (line : String) : String :=
  match Json.parse line with
  | .ok json => match json.getObjValAs? String "name", json.getObjValAs? String "module" with
    | .ok name, .ok module => s!"{name} ({module})"
    | _, _ => (line.take 80).toString
  | .error _ => (line.take 80).toString

/-- Name the declarations whose records differ between two outputs. -/
def differences (expected actual : Array String) : Array String := Id.run do
  let key := fun (line : String) => lineName line
  let expectedSet : Std.HashSet String := Std.HashSet.ofArray expected
  let actualSet : Std.HashSet String := Std.HashSet.ofArray actual
  let expectedKeys : Std.HashSet String := Std.HashSet.ofArray (expected.map key)
  let actualKeys : Std.HashSet String := Std.HashSet.ofArray (actual.map key)
  let mut found := #[]
  for line in actual do
    unless expectedSet.contains line do
      found := found.push ((if expectedKeys.contains (key line) then "changed: " else "added: ") ++ key line)
  for line in expected do
    unless actualSet.contains line || actualKeys.contains (key line) do
      found := found.push ("removed: " ++ key line)
  return found

end DeclarationRecords

open DeclarationRecords in
unsafe def main (arguments : List String) : IO UInt32 := do
  let options ← match parse arguments {} with
    | .ok options => pure options
    | .error message => IO.eprintln message; return 2
  let usage := "usage: DeclarationRecords [--check BASELINE] [--registry NAME] [--endpoints NAME] " ++
    "[--detail NAME]... [--trace-records] OUTPUT DIRECTORY..."
  let some output := options.positional[0]?
    | IO.eprintln usage; return 2
  let directories := options.positional.extract 1
  if directories.isEmpty then
    IO.eprintln "no directories selected"; return 2
  let mut modules := #[]
  let mut families := #[]
  for directory in directories do
    let path : System.FilePath := directory
    let found ← if path.extension == some "lean" then
        pure #[(path.withExtension "").components.foldl Name.str Name.anonymous]
      else modulesBelow path
    if found.isEmpty then
      IO.eprintln s!"no modules below {directory}"; return 2
    modules := modules ++ found
    families := families.push ((path.withExtension "").components.foldl Name.str Name.anonymous)
  let started ← IO.monoMsNow
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.qsort Name.lt |>.map fun module => { module, importAll := true }) {}
    (loadExts := true)
  let imported ← IO.monoMsNow
  IO.eprintln s!"declaration-records: import {imported - started}ms"
  let moduleOf := fun (name : Name) => Id.run do
    let some index := env.getModuleIdxFor? name | return none
    let some module := env.header.modules[index.toNat]? | return none
    return if families.any (·.isPrefixOf module.module) then some module.module else none
  let sources := providers env
  let owners := resolvedOwners env
  let indexed ← IO.monoMsNow
  IO.eprintln s!"declaration-records: providers {indexed - imported}ms"
  let mut provenanceCache : DeclarationRecords.Cache := {}
  let mut checkedAxioms : Std.HashMap Name (Array Name) := {}
  let mut auditRoots := options.details
  if let some name := options.registry then auditRoots := auditRoots.push name
  if let some name := options.endpoints then auditRoots := auditRoots.push name
  for index in [:env.header.modules.size] do
    let owner := env.header.modules[index]!.module
    unless families.any (·.isPrefixOf owner) do continue
    for info in env.header.moduleData[index]!.constants do
      auditRoots := auditRoots.push info.name
  for name in auditRoots do
    let some info := env.find? name | continue
    let (axioms, updated) ← storedAxioms env sources owners {} info provenanceCache
    provenanceCache := updated
    checkedAxioms := checkedAxioms.insert name axioms
  let audited ← IO.monoMsNow
  IO.eprintln s!"declaration-records: stored proof audit {audited - indexed}ms"
  -- A requested declaration that does not exist is reported by its consumer
  -- (an assurance report names a missing evidence instance), not here.
  for name in options.details do
    unless env.contains name do
      IO.eprintln s!"detailed declaration is not in the selected modules: {name}"
  let mut registry := Json.null
  let mut registered : Std.HashSet Name := {}
  if let some name := options.registry then
    unless env.contains name do
      IO.eprintln s!"registry table is missing: {name}"; return 1
    let table ← IO.ofExcept (env.evalConst (List (String × String × Option Name × String)) {} name)
    registry := Json.arr <| table.toArray.map fun (identifier, category, schema, statement) =>
      Json.mkObj [("identifier", Json.str identifier), ("category", Json.str category),
        ("schema", match schema with | some schema => Json.str schema.toString | none => Json.null),
        ("statement", Json.str statement)]
    for (_, _, schema, _) in table do
      if let some schema := schema then
        registered := registered.insert schema
        if let some info := env.find? schema then
          let (_, updated) ← storedAxioms env sources owners {} info provenanceCache
          provenanceCache := updated
  let mut endpoints := Json.null
  let mut endpointTheorems : Array Name := #[]
  if let some name := options.endpoints then
    unless env.contains name do
      IO.eprintln s!"endpoint table is missing: {name}"; return 1
    let table ← IO.ofExcept (env.evalConst (List (String × String × String × Name)) {} name)
    endpoints := Json.arr <| table.toArray.map fun (endpoint, property, statement, target) =>
      Json.mkObj [("endpoint", Json.str endpoint), ("property", Json.str property),
        ("statement", Json.str statement), ("theorem", Json.str target.toString)]
    for (_, _, _, target) in table do
      registered := registered.insert target
      endpointTheorems := endpointTheorems.push target
      if let some info := env.find? target then
        let (_, updated) ← storedAxioms env sources owners {} info provenanceCache
        provenanceCache := updated
  -- The registered properties: the heads of the endpoint theorems' statements.
  let mut properties : Std.HashSet Name := {}
  for target in endpointTheorems do
    if let some info := env.find? target then
      if let some head ← runMeta env (forallTelescope info.type fun _ body => pure (headName body)) then
        properties := properties.insert head
  let mut selected : Array (String × Name × Name × ConstantInfo) := #[]
  for (name, info) in env.constants.map₁.toList do
    let some module := moduleOf name | continue
    if (privateToUserName? name |>.getD name).isInternal then continue
    if (declRangeExt.find? env name).isNone then continue
    if isAuxRecursor env name || isNoConfusion env name then continue
    if info matches .recInfo _ then continue
    selected := selected.push ((privateToUserName? name |>.getD name).toString, module, name, info)
  let sorted := selected.qsort fun (left, leftModule, _, _) (right, rightModule, _, _) =>
    left < right || (left == right && leftModule.toString < rightModule.toString)
  let header := Json.mkObj [
    ("format", Json.str "zkc.declarations/0"),
    ("toolchain", Json.str Lean.versionString),
    ("axiom_provenance", Json.str "resolved-constant-info/0"),
    ("reference_provenance", Json.str "checked-stored-module/0"),
    ("families", Json.arr (families.map (Json.str ·.toString))),
    ("modules", toJson modules.size),
    ("declarations", toJson sorted.size),
    ("registry", registry),
    ("endpoints", endpoints)]
  let mut lines := #[header.compress]
  for (_, module, name, info) in sorted do
    let recordStarted ← IO.monoMsNow
    if options.traceRecords then IO.eprintln s!"declaration-records: start {name}"
    let claimDeclaration ← runMeta env (forallTelescope info.type fun _ body =>
      pure (headName body == some `Zkc.Claims.Wire.Request || headName body == some `Zkc.Claims.Receipt || headName body == some `ZkcSecurity.Claims.AdmittedReceipt ||
        headName body == some `ZkcSecurity.Claims.CanonicalReceipt || headName body == some `ZkcSecurity.Claims.AuthorExtensionReceipt ||
        (headName body).any (evidenceStructures.contains ·)))
    let detailed := options.details.contains name || endpointTheorems.contains name || claimDeclaration
    let some actualAxioms := checkedAxioms[name]?
      | throw <| IO.userError s!"selected declaration was not provenance audited: {name}"
    let json ← runMeta env (record env registered properties name info module actualAxioms detailed)
    lines := lines.push json.compress
    if options.traceRecords then
      IO.eprintln s!"declaration-records: done {name} {(← IO.monoMsNow) - recordStarted}ms"
  IO.FS.writeFile output (String.intercalate "\n" lines.toList ++ "\n")
  IO.eprintln s!"declaration-records: records and output {(← IO.monoMsNow) - audited}ms"
  IO.println s!"{sorted.size} declarations from {modules.size} modules"
  if let some baseline := options.check then
    let expected := ((← IO.FS.readFile baseline).splitOn "\n").toArray.filter (· ≠ "")
    let found := differences expected lines
    if !found.isEmpty then
      for line in found.toList.take 50 do IO.eprintln line
      IO.eprintln s!"{found.size} declaration records differ from {baseline}"
      return 1
    IO.println s!"records agree with {baseline}"
  return 0
