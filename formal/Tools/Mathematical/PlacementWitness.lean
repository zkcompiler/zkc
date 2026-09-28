import Tools.Mathematical.PlacementGraph
import Tools.Mathematical.Codec
import Std.Data.HashSet

/-! Strict decoding of the finite placement witness. These records carry names
and incidence candidates; none supplies demand, typing or operation semantics.
-/

set_option autoImplicit false
namespace Tools.Mathematical.PlacementWitness
open Zkc.Source.Mathematical

abbrev Check := Except String

private def unique {α : Type} [BEq α] [Hashable α] (values : List α) : Bool := Id.run do
  let mut seen : Std.HashSet α := {}
  for value in values do
    if seen.contains value then return false
    seen := seen.insert value
  return true

def ensure (ok : Bool) (code : String := "math-placement-witness") : Check Unit :=
  if ok then pure () else throw code

def array : Raw.Attribute → Check (List Raw.Attribute)
  | .array values => return values
  | _ => throw "math-placement-witness"

def string : Raw.Attribute → Check String
  | .string value => return value
  | _ => throw "math-placement-witness"

def natural : Raw.Attribute → Check Nat
  | .natural value => return value
  | _ => throw "math-placement-witness"

def numbers (value : Raw.Attribute) : Check (List Nat) := do (← array value).mapM natural

def record (keys : List String) (value : Raw.Attribute) : Check (String → Check Raw.Attribute) := do
  let .object fields := value | throw "math-placement-witness"
  ensure (fields.length == keys.length && keys.all (fun key => fields.any (·.1 == key)))
  return fun key => match fields.find? (·.1 == key) with
    | some (_, value) => pure value
    | none => throw "math-placement-witness"

structure Target where
  regions : List Nat
  name : String
  deriving BEq, Repr

structure Component where
  source : PlacementGraph.Address
  role : Nat
  target : Target
  deriving Repr

structure Site where
  site : Nat
  target : String
  kind : String
  deriving Repr

structure Result where
  role : Nat
  sourcePort : Nat
  targetPort : Nat
  deriving BEq, Repr

structure Witness where
  sourceDigest : String
  targetDigest : String
  key : ClosedInstances.Key
  protocol : String
  instanceName : String
  roots : List (Nat × String)
  operations : List (Nat × String)
  wires : List (Nat × String)
  components : List Component
  sites : List Site
  results : List Result

private def digest (value : Raw.Attribute) : Check String := do
  let text ← string value
  ensure (text.length == 64 && text.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')))
  return text

def decode (value : Raw.Attribute) : Check Witness := do
  let field ← record ["profile", "source", "target", "instances", "roots", "operations", "wires",
    "components", "sites", "results"] value
  ensure ((← string (← field "profile")) == "zkc.math.placement.v1")
  let [instanceValue] ← array (← field "instances") | throw "math-placement-instance-subset"
  let instanceField ← record ["sourceDefinition", "targetProtocol", "targetInstance", "statics", "roles", "capabilities"] instanceValue
  let key : ClosedInstances.Key := ⟨← natural (← instanceField "sourceDefinition"),
    ← numbers (← instanceField "statics"), ← numbers (← instanceField "roles"), ← numbers (← instanceField "capabilities")⟩
  let mappings := fun table target => do
    let rows ← (← array (← field table)).mapM fun value => do
      let mapping ← record ["source", target] value
      return (← natural (← mapping "source"), ← string (← mapping target))
    ensure (unique (rows.map Prod.fst) && unique (rows.map Prod.snd))
    return rows
  let components ← (← array (← field "components")).mapM fun value => do
    let item ← record ["instance", "source", "role", "target"] value
    ensure ((← natural (← item "instance")) == 0)
    let source ← record ["definition", "regions", "binding"] (← item "source")
    ensure ((← natural (← source "definition")) == key.definition)
    let target ← record ["regions", "name", "path"] (← item "target")
    ensure ((← numbers (← target "path")).isEmpty)
    return (⟨⟨← numbers (← source "regions"), ← natural (← source "binding")⟩,
      ← natural (← item "role"), ⟨← numbers (← target "regions"), ← string (← target "name")⟩⟩ : Component)
  ensure (unique (components.map (fun c => (c.source, c.role))))
  let sites ← (← array (← field "sites")).mapM fun value => do
    let item ← record ["instance", "site", "targetSite", "kind", "callee"] value
    ensure ((← natural (← item "instance")) == 0 && (← array (← item "callee")).isEmpty)
    return (⟨← natural (← item "site"), ← string (← item "targetSite"), ← string (← item "kind")⟩ : Site)
  ensure (unique (sites.map Site.site) && unique (sites.map Site.target))
  let results ← (← array (← field "results")).mapM fun value => do
    let item ← record ["instance", "role", "sourcePort", "targetPort", "path"] value
    ensure ((← natural (← item "instance")) == 0 && (← numbers (← item "path")).isEmpty)
    return (⟨← natural (← item "role"), ← natural (← item "sourcePort"), ← natural (← item "targetPort")⟩ : Result)
  return ⟨← digest (← field "source"), ← digest (← field "target"), key,
    ← string (← instanceField "targetProtocol"), ← string (← instanceField "targetInstance"),
    ← mappings "roots" "target", ← mappings "operations" "target", ← mappings "wires" "schema",
    components, sites, results⟩

end Tools.Mathematical.PlacementWitness
