module

public import ZkcTools.StructuredSource.Methods.SumcheckRoot
public meta import ZkcTools.StructuredSource.Methods.SumcheckRoot
public import Tests.StructuredOriginFixture
public meta import Tests.StructuredOriginFixture
public import Zkc.Source.Structured.Occurrence

@[expose] public section

/-! Authored controls for library template association. These fixtures are not
native exports. Selection and kernel-checked complete bodies are tested as
separate boundaries; call labels and iteration coordinates remain independent. -/
set_option autoImplicit false
namespace Tests.OriginalOriginBinding
open Zkc.Source Zkc.Source.Structured
open ZkcTools.StructuredSource

def sumcheckOrigin (maximum : String := "2") : ProtocolOrigin :=
  ⟨"sumcheck::Reduce", [("F", .field "bls12-381.fr"), ("Max", .natural maximum)]⟩

def installed : List (LibraryAssociation.Installed String) := [
  ⟨⟨"test::Leaf", ["T"]⟩, fun _ => pure "leaf-library"⟩,
  ⟨⟨"test::Root", []⟩, fun _ => pure "root-library"⟩]

def checkedLeaf (symbol : String) : CheckedProtocol :=
  { StructuredOriginFixture.checkedLeaf with name := symbol }

def rootBody (symbol : String) : Region protocolDialect [] [] :=
  .letOp (.mark "label_6c656674") .nil .nil <|
  .letOp (.protocolApply (checkedLeaf symbol).signature [0] "label_6c656674") .nil .nil <|
  .letOp (.mark "label_7269676874") .nil .nil <|
  .letOp (.protocolApply (checkedLeaf symbol).signature [0] "label_7269676874") .nil .nil <|
  .ret .nil

def checkedRoot (symbol : String) : CheckedProtocol :=
  ⟨StructuredOriginFixture.checkedRoot.signature, (rootBody symbol).erase, rootBody symbol,
    (rootBody symbol).elaborate_erase⟩

def snapshot (symbol : String) : Snapshot :=
  { StructuredOriginFixture.snapshot with contracts := [⟨"main", []⟩, ⟨symbol, []⟩], definitions := [
    .function { StructuredOriginFixture.root with body := .block [
      .instruction (.protocolApply symbol ["P"]) [] [] [] "label_6c656674",
      .instruction (.protocolApply symbol ["P"]) [] [] [] "label_7269676874"] (.ret []) },
    .function StructuredOriginFixture.helper, .function { StructuredOriginFixture.leaf with name := symbol }] }

def nominalInstallation : LibraryAssociation.Installed OriginTerm :=
  ⟨⟨"test::Nominal", ["T"]⟩, fun arguments => do
    let [("T", term@(.nominal .record "test::T" []))] := arguments
      | throw "test-library-nominal-kind"
    pure term⟩

/-- A deliberately wrong library candidate with a valid structural client.
Its origin selects Sumcheck even though it has no repeat. The generator must
emit the complete-body obligation, which this candidate cannot discharge. -/
def generatorSnapshot (maximum symbol : String) : Snapshot :=
  { StructuredOriginFixture.snapshot with
    contracts := [⟨"main", []⟩, ⟨symbol, []⟩]
    definitions := [
      .function ⟨"main", .protocol, .publicDef, [.boolean], [.boolean],
        some ⟨["P", "V"], [["V"]], [["V"]]⟩, [], some (.protocol ⟨"test::Client", []⟩),
        .block [
          .instruction (.protocolApply symbol ["P", "V"]) [] [] [] "label_63616c6c",
          .instruction (.protocolApply symbol ["P", "V"]) [] [] [] "label_7365636f6e64",
          .instruction (.localCall "accept" "V") [0] [.boolean] [] "check"] (.ret [0])⟩,
      .function ⟨"accept", .local, .privateDef, [.boolean], [.boolean], none, [],
        some (.local "test::accept" []), .block [] (.ret [0])⟩,
      .function ⟨symbol, .protocol, .publicDef, [], [], some ⟨["P", "V"], [], []⟩, [],
        some (.protocol (sumcheckOrigin maximum)), .block [] (.ret [])⟩] }

def repeatSnapshot : Snapshot :=
  { StructuredOriginFixture.snapshot with definitions := [
    .function { StructuredOriginFixture.root with
      inputs := [.index], interface := some ⟨["P"], [["P"]], []⟩
      body := .block [
        .instruction (.protocolRepeat 0 2 ["P"] []) [0] []
          [.region [.index] [] (.block [
            .instruction (.protocolApply "leaf" ["P"]) [] [] [] "label_6c656674",
            .instruction (.protocolApply "leaf" ["P"]) [] [] [] "label_7269676874"] (.yield []))]
          "label_726f756e64"] (.ret []) },
    .function StructuredOriginFixture.leaf] }

def expect (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

def refusal {α : Type} (label expected : String) (result : Except String α) : IO Unit :=
  match result with
  | .error reason => expect (label ++ ": " ++ reason) (reason == expected)
  | .ok _ => throw (IO.userError (label ++ ": accepted"))

def run : IO Unit := do
  let selected := fun origin => (LibraryAssociation.select [Methods.SumcheckRoot.sumcheckLibrary] origin).map (·.maximum)
  expect "named typed static arguments" (selected (sumcheckOrigin "2") == .ok 2)
  expect "changed Max changes selection" (selected (sumcheckOrigin "7") == .ok 7)
  refusal "noncanonical Max" "library-origin-malformed" (selected (sumcheckOrigin "02"))
  refusal "wrong Max kind" "original-root-library-arguments"
    (selected ⟨"sumcheck::Reduce", [("F", .field "bls12-381.fr"), ("Max", .index)]⟩)
  refusal "changed nominal field" "original-root-library-arguments"
    (selected ⟨"sumcheck::Reduce", [("F", .field "other-field"), ("Max", .natural "2")]⟩)
  refusal "Max exceeds index ABI" "original-root-library-maximum"
    (selected (sumcheckOrigin "18446744073709551616"))
  refusal "missing parameter" "library-static-parameters"
    (selected ⟨"sumcheck::Reduce", [("F", .field "bls12-381.fr")]⟩)
  refusal "wrong parameter name" "library-static-parameters"
    (selected ⟨"sumcheck::Reduce", [("F", .field "bls12-381.fr"), ("maximum", .natural "2")]⟩)
  refusal "reordered parameters" "library-static-parameters"
    (selected ⟨"sumcheck::Reduce", [("Max", .natural "2"), ("F", .field "bls12-381.fr")]⟩)
  refusal "duplicate parameters" "library-origin-malformed"
    (selected ⟨"sumcheck::Reduce", [("F", .field "bls12-381.fr"), ("F", .field "bls12-381.fr")]⟩)
  refusal "missing installed template" "library-template-missing"
    (LibraryAssociation.select installed (sumcheckOrigin))
  refusal "ambiguous installed template" "library-template-ambiguous"
    (LibraryAssociation.select [Methods.SumcheckRoot.sumcheckLibrary, Methods.SumcheckRoot.sumcheckLibrary] (sumcheckOrigin))
  refusal "malformed template path" "library-origin-malformed"
    (selected ⟨"sumcheck:::Reduce", []⟩)
  let nominal := fun kind => LibraryAssociation.select [nominalInstallation]
    ⟨"test::Nominal", [("T", .nominal kind "test::T" [])]⟩
  expect "record kind retained" ((nominal .record).isOk)
  for kind in [OriginNominalKind.variant, .associated, .moduleType, .logicalRecord] do
    refusal "same display path, different nominal kind" "test-library-nominal-kind" (nominal kind)
  let originFor := fun definitions => LibraryAssociation.originFor
    { StructuredOriginFixture.snapshot with definitions } StructuredOriginFixture.checkedLeaf
  refusal "missing raw association" "library-origin-missing" (originFor [])
  refusal "missing origin" "library-origin-missing"
    (originFor [.function { StructuredOriginFixture.leaf with origin := none }])
  refusal "Local origin on protocol" "library-origin-malformed"
    (originFor [.function { StructuredOriginFixture.leaf with origin := some (.local "test::Leaf" []) }])
  refusal "malformed retained origin" "library-origin-malformed"
    (originFor [.function { StructuredOriginFixture.leaf with origin := some (.protocol ⟨"test::", []⟩) }])
  refusal "ambiguous raw association" "library-origin-ambiguous"
    (originFor [.function StructuredOriginFixture.leaf, .function StructuredOriginFixture.leaf])
  for symbol in ["leaf", "renamed_emitted_symbol"] do
    let program ← match check (snapshot symbol) with
      | .ok program => pure program
      | .error reason => throw (IO.userError ("raw renamed calls admit: " ++ symbol ++ ": " ++ reason))
    let associated ← match LibraryAssociation.bottomUp program.snapshot installed program.payload.protocols with
      | .ok associated => pure associated
      | .error reason => throw (IO.userError reason)
    expect "actual admitted indices" (associated.map (·.index) == [0, 1])
    expect "bottom-up exact signature edges" (associated.map (·.callees) == [[], [0, 0]])
    expect "actual admitted dependency order" (associated.map (·.signature.name) == [symbol, "main"])
    expect "renamed symbol uses same origin" (associated.head?.map (·.origin) == some StructuredOriginFixture.leafOrigin)
    expect "renamed symbol uses same installation" (associated.map (·.selected) == ["leaf-library", "root-library"])
  refusal "forward callee refuses" "library-callee-association"
    (LibraryAssociation.bottomUp StructuredOriginFixture.snapshot installed [StructuredOriginFixture.checkedRoot, StructuredOriginFixture.checkedLeaf])
  refusal "renamed symbol without callee rebind" "library-callee-association"
    (LibraryAssociation.bottomUp (snapshot "renamed") installed [checkedLeaf "renamed", StructuredOriginFixture.checkedRoot])
  refusal "changed full signature" "library-callee-association"
    (LibraryAssociation.bottomUp StructuredOriginFixture.snapshot installed
      [{ StructuredOriginFixture.checkedLeaf with roles := ["other-role"] }, StructuredOriginFixture.checkedRoot])
  refusal "duplicate exact template instance" "library-origin-ambiguous"
    (LibraryAssociation.bottomUp
      { StructuredOriginFixture.snapshot with definitions := [.function StructuredOriginFixture.leaf, .function { StructuredOriginFixture.leaf with name := "other" }] }
      installed [StructuredOriginFixture.checkedLeaf, checkedLeaf "other"])
  let candidates ← match LibraryAssociation.bottomUp StructuredOriginFixture.snapshot installed [StructuredOriginFixture.checkedLeaf] with
    | .ok candidates => pure candidates
    | .error reason => throw (IO.userError reason)
  refusal "ambiguous exact callee table" "library-callee-association"
    (LibraryAssociation.calleeIndex (candidates ++ candidates) StructuredOriginFixture.leafSignature)
  let repeated ← match check repeatSnapshot with
    | .ok program => pure program
    | .error reason => throw (IO.userError ("repeated call admission: " ++ reason))
  let repeatedAssociations ← match LibraryAssociation.bottomUp repeated.snapshot installed repeated.payload.protocols with
    | .ok associations => pure associations
    | .error reason => throw (IO.userError reason)
  expect "two labelled calls inside an admitted repeat share a template"
    (repeatedAssociations.map (·.callees) == [[], [0, 0]])
  IO.println "PASS original template selection, bottom-up associations, typed static and nominal controls"

-- Same signature and origin can select a candidate with the wrong body.
-- It cannot supply the complete-body equation required by the library binding.
def wrongBody : Region protocolDialect [] [] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant true) rfl) .nil .nil (.ret .nil)
def wrongLeaf : CheckedProtocol :=
  ⟨StructuredOriginFixture.leafSignature, wrongBody.erase, wrongBody, wrongBody.elaborate_erase⟩

def wrongSnapshot : Snapshot :=
  { StructuredOriginFixture.snapshot with definitions := [
    .function StructuredOriginFixture.root, .function StructuredOriginFixture.helper,
    .function { StructuredOriginFixture.leaf with body := .block [
      .instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret []) }] }

def changedTable : List CheckedProtocol := [wrongLeaf, StructuredOriginFixture.checkedRoot]

def boundedBody (maximum : Nat) : Region protocolDialect [.index] [] :=
  .letOp (.repeat ⟨[], [], [0], [], maximum⟩ "label_726f756e64")
    (.cons .here .nil) (.cons (.ret .nil) .nil) (.ret .nil)

example : StructuredOriginFixture.checkedLeaf.body = StructuredOriginFixture.leafBody := by kernel_rfl
example :
    ((StructuredOriginFixture.imported.program.snapshot.definitions.filterMap
      (fun | .function function => some function | _ => none)).find?
        (fun function => function.name == StructuredOriginFixture.checkedLeaf.name)).bind
      (fun function => function.origin) = some (.protocol StructuredOriginFixture.leafOrigin) := by kernel_rfl
example : True := by
  fail_if_success have : wrongLeaf.body = StructuredOriginFixture.leafBody := by kernel_rfl
  trivial

example : True := by
  fail_if_success have : (changedTable.get ⟨0, by decide⟩).body = StructuredOriginFixture.leafBody := by kernel_rfl
  trivial

example : True := by
  -- Changing a typed static argument changes the selected complete repeat body.
  fail_if_success have : boundedBody 2 = boundedBody 7 := by kernel_rfl
  trivial

-- A template is shared by both calls, while labels and dynamic coordinates
-- continue to distinguish their occurrences in the existing source interpreter.
example : qualifyProtocolSite (ProtocolContext.enter {} "label_6c656674" [0]).applicationPrefix "draw" ≠
    qualifyProtocolSite (ProtocolContext.enter {} "label_7269676874" [0]).applicationPrefix "draw" := by decide +kernel
example : (⟨"label_6c656674.draw", 0⟩ : Occurrence.Frame) ≠
    ⟨"label_6c656674.draw", 1⟩ := by decide
example : True := by
  fail_if_success have : rootBody "leaf" = rootBody "renamed" := by kernel_rfl
  trivial

#eval run

def runBodyControls : IO Unit := do
  let program ← match check wrongSnapshot with
    | .ok program => pure program
    | .error reason => throw (IO.userError ("wrong-body fixture admission: " ++ reason))
  let associations ← match LibraryAssociation.bottomUp program.snapshot installed program.payload.protocols with
    | .ok associations => pure associations
    | .error reason => throw (IO.userError reason)
  expect "same origin still selects a candidate" (associations.map (·.selected) == ["leaf-library", "root-library"])
  IO.println "PASS changed admitted body retains selection but cannot supply the kernel body equation"

def runGeneratorControls : IO Unit := do
  for (maximum, symbol) in [("2", "reduce_emitted"), ("7", "renamed_reduce")] do
    let program ← match check (generatorSnapshot maximum symbol) with
      | .ok program => pure program
      | .error reason => throw (IO.userError ("generator fixture: " ++ reason))
    let associations ← match LibraryAssociation.bottomUp program.snapshot
        [Methods.SumcheckRoot.sumcheckLibrary] (program.payload.protocols.take 1) with
      | .ok associations => pure associations
      | .error reason => throw (IO.userError ("generator association: " ++ reason))
    let [association] := associations | throw (IO.userError "generator association count")
    expect "Max comes from typed origin metadata"
      (toString association.selected.maximum == maximum)
    match Methods.SumcheckRoot.source program
        { moduleName := "TestGenerated", sourceModule := "TestSource" } with
    | .ok _ => throw (IO.userError "installed method accepted an uninstalled local law")
    | .error reason =>
      expect "uninstalled local law refuses" (reason == "original-root-local-law-uninstalled")
    let generated ← match OriginalRoot.templateSource program {
        moduleName := "TestGenerated", sourceModule := "TestSource"
        programExpression := "TestSource.program", definitionIndex := 1, role := 1
        signature := ⟨[], false, true, program.payload.definitions.map (·.helper), Bindings.keys program⟩ } with
      | .ok generated => pure generated
      | .error reason => throw (IO.userError ("generic template: " ++ reason))
    let contains := fun fragment => (generated.splitOn fragment).length > 1
    expect "complete normalized body equation remains mandatory"
      (contains "normalized := by kernel_rfl")
    expect "labelled call occurrence retained" (contains "label_63616c6c")
    expect "second occurrence of the same template retained" (contains "label_7365636f6e64")
    expect "actual callee signature retained" (contains symbol)
    expect "immutable capture and source equation remain mandatory"
      (contains "theorem capture_exact" && contains "theorem source_capture")
  IO.println "PASS typed library selection, uninstalled-law refusal and generic source templates"

#eval runBodyControls
#eval runGeneratorControls

end Tests.OriginalOriginBinding
