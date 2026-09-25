import Tools.Artifact.Descriptor

/-! Source-owned occurrence coordinates. These transformations are called only
after complete independent admission. They change sites and site references,
never SSA, operation selection, static text, or declaration order. No producer
map or native preparation view is accepted. -/

set_option autoImplicit false

namespace Tools.Artifact.Identity
open Lean (Json)
open Tools.Interactive

def array (items : List Json) : Json := .arr items.toArray
def strings (items : List String) : Json := array (items.map Json.str)

def field (json : Json) (index : Nat) : Result Json := do
  let some value := (← Decode.array json)[index]? | throw "identity-record-field"
  return value

def replace (json : Json) (index : Nat) (value : Json) : Result Json := do
  let items ← Decode.array json
  ensure (index < items.length) "identity-record-field"
  return array (items.set index value)

def recordName (json : Json) : Result Name := do Decode.name (← field json 1)

abbrev SiteMap := List (Name × Name)
abbrev DeclarationSites := List (Name × SiteMap)

/-- Missing and ambiguous aliases both fail, even when a helper is used outside
the admitted entry point. Names are looked up simultaneously in the original. -/
def resolveName (aliases : SiteMap) (name : Name) : Result Name := do
  let [(_, target)] := aliases.filter (fun p => p.1 == name)
    | throw "identity-site-reference"
  return target

structure BodyResolution where
  json : Json
  next : Nat
  aliases : SiteMap

def resolveBody : Nat → Nat → Json → Result BodyResolution
  | 0, _, _ => .error "identity-body-depth"
  | depth + 1, initial, json => do
    let mut next := initial
    let mut aliases := []
    let mut output := []
    for instruction in ← Decode.array json limits.instructions do
      let fields ← Decode.array instruction
      match fields with
      | [.str "return", _] | [.str "yield", _] => output := output ++ [instruction]
      | _ =>
        let valid := match fields with
          | [.str "op", _, _, _, _, _] | [.str "op", _, _, _, _, _, _]
          | [.str "local", _, _, _, _, _] | [.str "message", _, _, _, _, _, _]
          | [.str "call", _, _, _, _] | [.str "apply", _, _, _, _, _] | [.str "stop", _, _, _]
          | [.str "loop", _, _, _, _, _, _] | [.str "if", _, _, _, _, _, _]
          | [.str "for", _, _, _, _, _, _, _, _] => true
          | _ => false
        ensure valid "identity-instruction"
        let old ← Decode.name (← field instruction 1)
        ensure (!(aliases.any fun p => p.1 == old)) "identity-duplicate-site"
        let site := s!"site{next}"
        next := next + 1
        aliases := aliases ++ [(old, site)]
        let mut resolved ← replace instruction 1 (.str site)
        if fields.head? == some (.str "loop") then
          let nested ← resolveBody depth next (← field instruction 5)
          next := nested.next
          aliases := aliases ++ nested.aliases
          resolved ← replace resolved 5 nested.json
        if fields.head? == some (.str "if") then
          for index in [4, 5] do
            let nested ← resolveBody depth next (← field instruction index)
            next := nested.next
            aliases := aliases ++ nested.aliases
            resolved ← replace resolved index nested.json
        if fields.head? == some (.str "for") then
          let nested ← resolveBody depth next (← field instruction 7)
          next := nested.next
          aliases := aliases ++ nested.aliases
          resolved ← replace resolved 7 nested.json
        output := output ++ [resolved]
    ensure (unique (aliases.map Prod.fst)) "identity-duplicate-site"
    ensure (next ≤ limits.instructions) "identity-instruction-limit"
    return ⟨array output, next, aliases⟩

def resolveDeclarations (bodyIndex : Nat) (declarations : List Json) :
    Result (List Json × DeclarationSites) := do
  let mut records := []
  let mut maps := []
  for declaration in declarations do
    let resolved ← resolveBody limits.depth 0 (← field declaration bodyIndex)
    records := records ++ [← replace declaration bodyIndex resolved.json]
    maps := maps ++ [(← recordName declaration, resolved.aliases)]
  ensure (unique (maps.map Prod.fst)) "identity-duplicate-declaration"
  return (records, maps)

/-- The raw carrier retains strings which typed preparation may interpret (for
example generic natural literals). Normalization never re-encodes those terms. -/
structure Carrier where
  isLibrary : Bool
  definitions : List Json
  configurations : List Json
  bindings : Json
  functions : List Json
  protocols : List Json
  instances : List Json
  entries : List Json

def Carrier.decode (json : Json) : Result Carrier := do
  let (isLibrary, definitions, configurations, common) ← match ← Decode.array json with
    | [.str "zkc.library/1", definitions, configurations, common] =>
        pure (true, ← Decode.array definitions limits.definitions,
          ← Decode.array configurations limits.definitions, common)
    | .str "zkc.protocol/1" :: _ => pure (false, [], [], json)
    | _ => throw "identity-source-version"
  let [.str "zkc.protocol/1", bindings, functions, protocols, instances, entries] ← Decode.array common
    | throw "identity-source-version"
  return ⟨isLibrary, definitions, configurations, bindings,
    ← Decode.array functions limits.definitions, ← Decode.array protocols limits.definitions,
    ← Decode.array instances limits.definitions, ← Decode.array entries limits.definitions⟩

def Carrier.json (carrier : Carrier) : Json :=
  let common := Json.arr #[.str "zkc.protocol/1", carrier.bindings, array carrier.functions,
    array carrier.protocols, array carrier.instances, array carrier.entries]
  if carrier.isLibrary then .arr #[.str "zkc.library/1", array carrier.definitions,
    array carrier.configurations, common] else common

structure Resolution where
  carrier : Carrier
  functions : DeclarationSites
  definitions : DeclarationSites
  protocols : DeclarationSites

def resolveCarrier (carrier : Carrier) (library : Generic.Library) : Result Resolution := do
  let (functions, functionSites) ← resolveDeclarations 4 carrier.functions
  let (definitions, definitionSites) ← resolveDeclarations 6 carrier.definitions
  let (protocols, protocolSites) ← resolveDeclarations 7 carrier.protocols
  let configurations ← carrier.configurations.mapM fun record => do
    let declaration ← Generic.decodeConfiguration record
    let final ← library.configuration declaration.name
    let aliases ← lookup final.definition definitionSites
    let choices ← declaration.implementations.mapM fun (site, implementation) => do
      return strings [← resolveName aliases site, implementation]
    replace record 4 (array choices)
  return ⟨{ carrier with functions, definitions, protocols, configurations },
    functionSites, definitionSites, protocolSites⟩

def Resolution.localSites (resolution : Resolution) (library : Generic.Library)
    (name : Name) : Result SiteMap := do
  if let some aliases := resolution.functions.lookup name then return aliases
  if let some aliases := resolution.definitions.lookup name then return aliases
  let configuration ← library.configuration name
  lookup configuration.definition resolution.definitions

def resolveDescriptor (resolution : Resolution) (library : Generic.Library)
    (json : Json) : Result Json := do
  let [.str "zkc.construction/1", _, _, _, _, random, _, _, .str "normalized"] ← Decode.array json
    | throw "identity-descriptor"
  let [rng, draws] ← Decode.array random | throw "construction-random"
  -- Concrete names and logical origins can overlap in valid source. A single
  -- numbered selector is safe only if it preserves the raw occurrence set:
  -- forward checks detect losses; reverse checks detect unrelated additions.
  let add (index : Std.HashMap (Name × Name) (Option Name))
      (key : Name × Name) (value : Name) :=
    match index[key]? with
    | none => index.insert key (some value)
    | some old => index.insert key (if old == some value then old else none)
  let mut forward : Std.HashMap (Name × Name) (Option Name) := {}
  let mut reverse : Std.HashMap (Name × Name) (Option Name) := {}
  for function in resolution.carrier.functions do
    let name ← recordName function
    let [origin, _] ← Decode.array (← field function 5) | throw "binding-logical-origin"
    let origin ← Decode.name origin
    for (raw, coordinate) in (resolution.functions.lookup name).getD [] do
      for owner in [name, origin] do
        forward := add forward (owner, raw) coordinate
        reverse := add reverse (owner, coordinate) raw
  let draws ← (← Decode.pairs Decode.name Decode.name draws).mapM fun (name, site) => do
    let coordinate ← resolveName (← resolution.localSites library name) site
    if let some actual := forward[(name, site)]? then
      ensure (actual == some coordinate) "construction-selector-coordinates"
    if let some actual := reverse[(name, coordinate)]? then
      ensure (actual == some site) "construction-selector-coordinates"
    return strings [name, coordinate]
  replace json 5 (.arr #[rng, array draws])

/-- Receive aliases belong to the protocol selected by the named instance.
Coverage, ownership and setup-key validity are checked after this resolution. -/
def resolveConfiguration (resolution : Resolution) (source : Source) (json : Json) : Result Json := do
  let [.str "zkc.public-configuration/1", _, _, receives] ← Decode.array json
    | throw "public-configuration"
  let receives ← (← Decode.array receives).mapM fun record => do
    let [instanceName, role, site, key] ← Decode.array record | throw "artifact-receive-record"
    let binding ← source.binding (← Decode.name instanceName)
    let aliases ← lookup binding.protocol resolution.protocols
    return .arr #[instanceName, role, .str (← resolveName aliases (← Decode.name site)), key]
  replace json 3 (array receives)

end Tools.Artifact.Identity
