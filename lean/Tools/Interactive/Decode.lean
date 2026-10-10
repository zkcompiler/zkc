import Tools.Interactive.Syntax

set_option autoImplicit false

namespace Tools.Interactive.Decode
open Lean

def string : Json → Result String
  | .str value => .ok value
  | _ => .error "expected-string"

def array (json : Json) (bound : Nat := limits.array) : Result (List Json) :=
  match json with
  | .arr values => if values.size ≤ bound then .ok values.toList else .error "array-limit"
  | _ => .error "expected-array"

def asciiLetter (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
def asciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def validName (s : String) (bound : Nat := 128) : Bool :=
  s.utf8ByteSize ≤ bound && match s.toList with
  | [] => false
  | first :: rest => (asciiLetter first || first == '_') &&
      rest.all (fun c => asciiLetter c || asciiDigit c || c == '_' || c == '.' || c == '-')

def name (json : Json) (bound : Nat := 128) : Result Name := do
  let value ← string json
  ensure (validName value bound) "invalid-name"
  return value

def natural (json : Json) : Result Nat := do
  let value ← string json
  ensure (value.utf8ByteSize ≤ 78) "natural-limit"
  ensure (!value.isEmpty && value.toList.all asciiDigit) "expected-natural"
  let some n := value.toNat? | throw "expected-natural"
  ensure (toString n == value) "noncanonical-natural"
  return n

def ty (json : Json) : Result Ty := do
  let value ← string json
  if ["field", "table", "point", "round", "bool", "rng", "commitment", "proof",
      "prover_key", "verifier_key", "opening_state", "scalar", "group", "nonce",
      "groups", "transcript"].contains value then return value
  if value.startsWith "opaque:" && validName (value.drop 7).toString then return value
  if value.startsWith "capability:" && validName (value.drop 11).toString then return value
  throw "unknown-type"

def names (json : Json) : Result (List Name) := do (← array json limits.ports).mapM (fun j => name j)
def types (json : Json) : Result (List Ty) := do (← array json limits.ports).mapM ty

def pairs {α β : Type} (left : Json → Result α) (right : Json → Result β)
    (json : Json) : Result (List (α × β)) := do
  (← array json).mapM fun item => do
    match ← array item with
    | [a, b] => return (← left a, ← right b)
    | _ => throw "invalid-pair"

def parameter (json : Json) : Result Parameter := do
  if let .str _ := json then return .constant (← natural json)
  let [.str "ingress", .str spelling, mappings] ← array json | throw "interactive-family-binding"
  -- A canonical natural past the limit is out of bound however many digits it
  -- has, so the bound is not read through the length-limited natural decoder.
  ensure (!spelling.isEmpty && spelling.toList.all asciiDigit &&
    (spelling.length == 1 || spelling.front != '0')) "interactive-family-binding"
  let some bound := spelling.toNat? | throw "interactive-family-binding"
  ensure (bound ≤ limits.iterations) "interactive-family-bound"
  let selectors ← (← array mappings limits.ports).mapM fun item => do
    let [role, function, arguments] ← array item | throw "interactive-family-binding"
    let arguments ← names arguments
    ensure (unique arguments) "interactive-family-argument"
    return (⟨← name role, ← name function, arguments⟩ : FamilySelector)
  ensure (!selectors.isEmpty && unique (selectors.map FamilySelector.role)) "interactive-family-roles"
  return .ingress bound selectors

def count (json : Json) : Result Count := do
  match ← array json with
  | [.str "parameter", value] => return .parameter (← name value)
  | [.str "constant", value] => return .constant (← natural value)
  | _ => throw "invalid-count"

def reason (json : Json) : Result String := do
  let value ← string json
  ensure (["reject", "abort", "exhausted", "incomplete", "refused"].contains value) "unknown-stop"
  return value

inductive BodyKind where
  | localFunction | common | role
  deriving BEq

def body (depth : Nat) (kind : BodyKind) (json : Json)
    (readType : Json → Result Ty := ty) (allowRelease : Bool := false)
    (sourceLocal : Bool := false) : Result (List Instruction) :=
  match depth with
  | 0 => .error "body-depth-limit"
  | depth + 1 => do
    let items ← array json
    ensure (items.length ≤ limits.instructions) "instruction-limit"
    items.mapM fun item => do
      match ← array item with
      | [.str "release", values] =>
          ensure (kind == .localFunction && allowRelease) "release-context"
          return .release (← names values)
      | [.str "op", site, kernel, attributes, inputs, outputs] =>
          ensure (kind == .localFunction) "op-outside-function"
          return .op (← name site) (← string kernel) (← (← array attributes).mapM string)
            (← names inputs) (← names outputs)
      | [.str "apply", site, function, statics, inputs, outputs] =>
          ensure ((← array statics).isEmpty) "algorithm-static-arguments"
          ensure (kind == .localFunction && !allowRelease) "algorithm-call-context"
          return .call (← name site) (← name function) (← names inputs) (← names outputs)
      | [.str "local", site, owner, function, inputs, outputs] =>
          ensure (kind == .common) "common-local-outside-source"
          return .localCall (← name site) (← name owner) (← name function) (← names inputs) (← names outputs)
      | [.str "local", site, function, inputs, outputs] =>
          ensure (kind == .role) "role-local-outside-participant"
          return .localCall (← name site) "" (← name function) (← names inputs) (← names outputs)
      | [.str "message", site, schema, sender, receiver, input, output] =>
          ensure (kind == .common) "message-outside-source"
          return .message (← name site) (← name schema) (← name sender) (← name receiver)
            (← name input) (← name output)
      | [.str "send", site, schema, peer, input] =>
          ensure (kind == .role) "send-outside-participant"
          return .send (← name site) (← name schema) (← name peer) (← name input)
      | [.str "receive", site, schema, peer, output, valueType] =>
          ensure (kind == .role) "receive-outside-participant"
          return .receive (← name site) (← name schema) (← name peer) (← name output) (← readType valueType)
      | [.str "call", site, callee, inputs, outputs] =>
          ensure (kind != .localFunction) "call-in-function"
          return .call (← name site) (← name callee (if kind == .role then 512 else 128))
            (← names inputs) (← names outputs)
      | [.str "loop", site, iterations, carried, captures, nested, outputs] =>
          ensure (kind != .localFunction) "loop-in-function"
          let iterations ← if kind == .role && (match iterations with | .str _ => true | _ => false)
            then Count.constant <$> natural iterations else count iterations
          return .loop (← name site) iterations (← pairs name name carried) (← names captures)
            (← body depth kind nested readType) (← names outputs)
      | [.str "variant", site, valueType, alternative, payload, output] =>
          ensure (kind == .localFunction) "local-control-context"
          return .variant (← name site) (← readType valueType) (← name alternative) (← names payload) (← name output)
      | [.str "match", site, input, captures, arms, outputs] =>
          ensure (kind == .localFunction) "local-control-context"
          let arms ← (← array arms 32).mapM fun arm => do
            let [alternative, payload, nested] ← array arm | throw "variant-arm"
            return (← name alternative, ← names payload, ← body depth kind nested readType allowRelease sourceLocal)
          return .localMatch (← name site) (← name input) (← names captures) arms (← names outputs)
      | [.str "if", site, condition, captures, yes, no, outputs] =>
          ensure (kind == .localFunction) "local-control-context"
          return .conditional (← name site) (← name condition) (← names captures)
            (← body depth kind yes readType allowRelease sourceLocal) (← body depth kind no readType allowRelease sourceLocal) (← names outputs)
      | [.str "for", site, induction, lower, upper, carried, captures, nested, outputs] =>
          ensure (kind == .localFunction) "local-control-context"
          return .forLoop (← name site) (← name induction) (← name lower) (← name upper)
            (← pairs name name carried) (← names captures) (← body depth kind nested readType allowRelease sourceLocal) (← names outputs)
      | [.str "yield", values] =>
          return .yield (← names values)
      | [.str "return", values] => return .ret (← names values)
      | [.str "stop", site, owner, why] =>
          ensure (kind == .common || (kind == .localFunction && sourceLocal))
            "common-stop-outside-source"
          let owner ← if kind == .localFunction then do
            ensure ((← string owner).isEmpty) "local-stop-role"
            pure ""
          else name owner
          return .stop (← name site) owner (← reason why)
      | [.str "stop", site, why] =>
          ensure (kind == .role || (kind == .localFunction && !sourceLocal)) "role-stop-outside-participant"
          return .stop (← name site) "" (← reason why)
      | [.str "incomplete", site] =>
          ensure (kind == .role) "incomplete-outside-participant"
          return .incomplete (← name site)
      | _ => throw "invalid-instruction"

def function (json : Json) (allowExternal : Bool := true)
    (allowRelease : Bool := false) : Result Function := do
  match ← array json with
  | [.str "function", symbol, arguments, results, code] =>
      let code ← match code with
        | .str "external" => do
            ensure allowExternal "external-candidate-function"
            pure none
        | _ => some <$> body limits.depth .localFunction code ty allowRelease
      return ⟨← name symbol, ← pairs (fun j => name j) ty arguments, ← types results, code⟩
  | _ => throw "invalid-function"

def dependency (json : Json) : Result Dependency := do
  match ← array json with
  | [alias, definition, agreements] =>
      return ⟨← name alias, ← name definition, ← pairs name name agreements⟩
  | _ => throw "invalid-dependency"

def protocol (json : Json) (readType : Json → Result Ty := ty) : Result Protocol := do
  match ← array json with
  | [.str "protocol", symbol, roles, parameters, arguments, results, dependencies, code] =>
      let arguments ← (← array arguments).mapM fun item => do
        match ← array item with
        | [argument, role, valueType] => return Port.mk (← name argument) (← name role) (← readType valueType)
        | _ => throw "invalid-port"
      let code ← match code with
        | .str "external" => pure none
        | _ => some <$> body limits.depth .common code readType
      return ⟨← name symbol, ← names roles, ← names parameters, arguments,
        ← pairs name readType results, ← (← array dependencies).mapM dependency, code⟩
  | _ => throw "invalid-protocol"

def binding (json : Json) : Result Instance := do
  match ← array json with
  | [.str "instance", symbol, definition, parameters, dependencies, roles] =>
      return ⟨← name symbol, ← name definition, ← pairs name parameter parameters,
        ← pairs name name dependencies, ← pairs name name roles⟩
  | _ => throw "invalid-instance"

def entry (json : Json) : Result (Name × Name) := do
  match ← array json with
  | [.str "entry", symbol, selected] => return (← name symbol, ← name selected)
  | _ => throw "invalid-entry"

def participant (json : Json) (readType : Json → Result Ty := ty) : Result Participant := do
  match ← array json with
  | [.str "participant", symbol, selected, role, parameters, arguments, results, code] =>
      return ⟨← name symbol 512, ← name selected, ← name role, ← pairs (fun j => name j) parameter parameters,
        ← pairs name readType arguments, ← (← array results limits.ports).mapM readType,
        ← body limits.depth .role code readType⟩
  | _ => throw "invalid-participant"

/-- Scan before JSON parsing to reject numbers/objects and bound nesting. This
also prevents exponent expansion and deeply nested parser recursion. -/
def preflight (text : String) (byteCeiling : Nat := limits.bytes) : Result Unit := do
  ensure (text.utf8ByteSize ≤ byteCeiling) "byte-limit"
  let mut quoted := false
  let mut escaped := false
  let mut depth := 0
  for c in text.toList do
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then quoted := true
    else if c == '[' then
      depth := depth + 1
      ensure (depth ≤ limits.depth) "json-depth-limit"
    else if c == ']' then
      ensure (depth > 0) "invalid-json"
      depth := depth - 1
    else ensure (c == ',' || c == ' ' || c == '\n' || c == '\r' || c == '\t') "non-array-json-token"
  ensure (!quoted && depth == 0) "invalid-json"

def parse (text : String) : Result Json := do
  preflight text
  (Json.parse text).mapError fun _ => "invalid-json"

def read (path : System.FilePath) : IO (Result Json) :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size ≤ limits.bytes do
      let chunk ← handle.read (min 65536 (limits.bytes + 1 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    if bytes.size > limits.bytes then return .error "byte-limit"
    let some text := String.fromUTF8? bytes | return .error "invalid-utf8"
    return parse text

end Tools.Interactive.Decode
