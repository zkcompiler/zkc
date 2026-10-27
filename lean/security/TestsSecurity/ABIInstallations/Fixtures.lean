module

public import Zkc.Source.Structured.UnitViews
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SubjectABI
public import ZkcSecurity.Domains.PrimeField

@[expose] public section
noncomputable section

/-! Small admitted sources and actual constructed artifacts for ABI installation
controls. These are model fixtures, not native compiler exports. Every subject
passes the ordinary source, pair, occurrence and retained-formula checks. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.ABIInstallations.Fixtures
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair

abbrev model := ringModel (ZMod 5) (ZMod 5)
def scalarDomain : String := Zkc.Source.Structured.scalarDomain
def scalarServiceContract : String := Zkc.Source.Structured.scalarServiceContract

def digest : String := "sha256:" ++ String.ofList (List.replicate 64 '0')

structure Configuration where
  dataTypes : List Ty
  publicData : Bool := true
  selectors : List Nat
  constrained : Bool := false

def Configuration.types (config : Configuration) : List Ty :=
  config.dataTypes ++ [.service scalarServiceContract]
def Configuration.publics (config : Configuration) : List Nat :=
  if config.publicData then List.range config.dataTypes.length else []
def Configuration.arguments (config : Configuration) : List Ty :=
  config.selectors.map (config.dataTypes[·]!)
def constantTrue : Block :=
  .block [.instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0])

def source (config : Configuration) : Snapshot where
  source := digest
  entry := "main"
  domains := []
  relations :=
    [{ name := "Target", visibility := .publicDef, kind := "zkc.language.formula/0",
       key := "target", revision := "0", inputs := config.arguments, outputs := [.boolean],
       purposes := config.selectors.map (fun _ => if config.publicData then "statement" else "witness"),
       formula := some "targetFormula" }] ++
    (if config.constrained then
      [{ name := "One", visibility := .publicDef, kind := "zkc.language.formula/0",
         key := "one", revision := "0", inputs := [.index], outputs := [.boolean],
         purposes := ["statement"], formula := some "oneFormula" }] else [])
  bindings := []
  definitions :=
    [.function ⟨"main", .protocol, .publicDef, config.types, [.boolean],
      some ⟨["P", "V"],
        config.dataTypes.map (fun _ => if config.publicData then ["P", "V"] else ["P"]) ++ [["V"]],
        [["V"]]⟩, [], some (.protocol ⟨"main", []⟩), constantTrue⟩,
     .function ⟨"targetFormula", .math, .privateDef, config.arguments, [.boolean], none, [], none, constantTrue⟩] ++
    (if config.constrained then
      [.function ⟨"oneFormula", .math, .privateDef, [.index], [.boolean], none, [], none,
        .block [.instruction (.indexConstant "1") [] [.index] [] "",
          .instruction .indexEqual [1, 0] [.boolean] [] ""] (.ret [0])⟩] else [])
  contracts := [⟨"main",
    [⟨.target, "claim", ⟨"Target", config.selectors.map fun index =>
      ⟨.input, index, if config.publicData then "V" else "P"⟩⟩,
      none, some ⟨.output, 0, "V"⟩⟩] ++
    (if config.constrained then [⟨.input, "one", ⟨"One", [⟨.input, 0, "V"⟩]⟩, none, none⟩] else [])⟩]
  catalogue := blsRows

def artifacts (config : Configuration) : AuthoredPair.Artifacts :=
  let policy : Policy := ⟨"main", "P", "V", 0, "suite", [config.dataTypes.length],
    config.publics, [], "zkc.framed/0", ""⟩
  let producer : Participant := {
    source := digest, candidate := digest, policy, symbol := "producer"
    inputs := config.dataTypes.map (.data ·) ++ [.transcript "suite"]
    outputs := [.transcript "suite"], instructions := [], returned := [config.dataTypes.length] }
  let validator : Participant := {
    source := digest, candidate := digest, policy, symbol := "validator"
    inputs := (if config.publicData then config.dataTypes.map (.data ·) else []) ++ [.transcript "suite"]
    outputs := [.data .boolean, .transcript "suite"]
    instructions := [⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩]
    returned := [config.publics.length + 1, config.publics.length] }
  ⟨producer, validator⟩

end TestsSecurity.ABIInstallations.Fixtures
