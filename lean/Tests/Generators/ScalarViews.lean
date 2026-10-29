import ZkcTools.StructuredSource.Bindings.RoleViews
import ZkcTools.StructuredSource.Bindings.Helpers
import Zkc.Source.Structured.Format
import ZkcExamples.Structured.SumcheckPendingBodies
/-! Source and display-name selections for scalar participant presentations,
with separate typed mathematical library associations. The generic normalizer
and RoleViews own every operation, role mask, callback, application and complete
returned frame. The kernel checks all generated equations and associations. -/
namespace Tests.Generators.ScalarViews
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcTools.StructuredSource.Bindings
open RoleViews

structure Selection where
  key : String
  sourceModule : String
  fixture : String
  names : List ProtocolNames

def sigma (inputs : List String) : List ProtocolNames :=
  [⟨"Root", "body", ["prover", "verifier"], inputs, []⟩]

def sumcheck (inputs : List String) : List ProtocolNames := [
  ⟨"Reduce", "body", ["prover", "verifier"],
    ["entries", "dimension", "width", "point", "claim", "count", "service"],
    [⟨"round", ["proverRound", "verifierRound"],
      ["index", "entries", "dimension", "width", "proverPoint", "point", "claim", "service"]⟩]⟩,
  ⟨"Root", "body", ["prover", "verifier"], inputs, []⟩]

def selections : List Selection := [
  ⟨"ChaumPedersen", "ZkcExamples.Structured.ChaumPedersenViews", "bridges/structured/fixtures/chaum-pedersen.json",
    sigma ["firstBase", "firstKey", "secondBase", "secondKey", "witness", "nonces", "challenges"]⟩,
  ⟨"Okamoto", "ZkcExamples.Structured.OkamotoViews", "bridges/structured/fixtures/okamoto.json",
    sigma ["firstBase", "secondBase", "point", "firstScalar", "secondScalar", "nonces", "challenges"]⟩,
  ⟨"SchnorrAnd", "ZkcExamples.Structured.SchnorrAndViews", "bridges/structured/fixtures/schnorr-and.json",
    sigma ["firstBase", "firstKey", "secondBase", "secondKey", "firstWitness", "secondWitness", "nonces", "challenges"]⟩,
  ⟨"SchnorrInteractive", "ZkcExamples.Structured.SchnorrInteractive", "bridges/structured/fixtures/schnorr-interactive.json",
    sigma ["base", "key", "witness", "nonces", "challenges"]⟩,
  ⟨"SumcheckSource", "ZkcExamples.Structured.SumcheckSourceViews", "bridges/structured/fixtures/sumcheck-source.json",
    sumcheck ["entries", "claim", "count", "service"]⟩,
  ⟨"SumcheckReduction", "ZkcExamples.Structured.SumcheckReduceViews", "bridges/structured/fixtures/sumcheck-reduce.json",
    sumcheck ["entries", "dimension", "claim", "count", "service"]⟩,
  ⟨"SumcheckRepacked", "ZkcExamples.Structured.SumcheckRepackedViews", "bridges/structured/fixtures/sumcheck-repacked.json",
    sumcheck ["claim", "count", "dimension", "entries", "service"]⟩]

def require (result : Except String String) : IO String :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)


/-- Mathematical library selection, checked against complete typed source.
These are body patterns, not participant execution templates. -/
def pendingPatterns : List (String × Helper × String) := [
  ("pending", SumcheckPendingBodies.pendingHelper, "SumcheckPendingBodies.pendingBody"),
  ("openClaim", SumcheckPendingBodies.openClaimHelper, "SumcheckPendingBodies.openClaimBody"),
  ("atPrefix", SumcheckPendingBodies.atPrefixHelper, "SumcheckPendingBodies.atPrefixBody")]

def librarySource (program : Program) (name : String) : Except String String := do
  let mut text := "module\n\npublic import " ++ name ++ "\npublic import ZkcExamples.Structured.SumcheckPendingLaws\n\n@[expose] public section\n\n/-! Checked associations of the mathematical library with the admitted source. -/\nnamespace " ++ name ++ "Library\nopen Zkc.Source Zkc.Source.Structured ZkcExamples.Structured\nopen " ++ name ++ "\nset_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\nvariable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"
  for (localName, helper, body) in pendingPatterns do
    let [(_, index)] := program.payload.definitions.zipIdx.filter (fun (definition, _) => definition.helper == helper)
      | throw "scalar-library-helper-selection"
    text := text ++ (← helperAssociationSource program localName index
      "(plainHelpers (F := F) (G := G) payload).closed" "(.silent _)")
    text := text ++ "theorem " ++ localName ++ "_pattern : " ++ localName ++ "Body = " ++ body ++ " := by kernel_rfl\n\n" ++
      "theorem " ++ localName ++ "_body : BodyIn payload.definitions SumcheckPendingBodies." ++ localName ++ "Helper " ++ body ++ " :=\n  ⟨" ++ localName ++ "Definition, List.get_mem _ _, rfl, by kernel_rfl⟩\n\n"
  text := text ++ "theorem claims : SumcheckPendingLaws.Bodies payload.definitions := ⟨pending_body, openClaim_body, atPrefix_body⟩\n\n" ++
    "theorem reduce_body : Reduce.bodyBody = SumcheckVerifierBodies.reduceBody Reduce.roundMaximum := by kernel_rfl\n" ++
    "theorem round_body : Reduce.roundBody = SumcheckVerifierBodies.roundBody := by kernel_rfl\n\nend " ++ name ++ "Library\n"
  pure text

def main (args : List String) : IO Unit := do
  let [directory, key] := args | throw (IO.userError "expected output directory and selection")
  let some selected := selections.find? (·.key == key)
    | throw (IO.userError "unknown scalar source selection")
  let snapshot ← match (Format.parse (← IO.FS.readFile selected.fixture) 33554432).bind Format.snapshot with
    | .ok snapshot => pure snapshot
    | .error reason => throw (IO.userError reason)
  let program ← match check snapshot with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  let name := "ZkcExamples.Structured.Generated.Scalar." ++ key
  let binding := name ++ "Bindings"
  let output : Output := {
    moduleName := binding, sourceModule := selected.sourceModule
    programExpression := selected.sourceModule ++ ".program"
    importedExpression := selected.sourceModule ++ ".imported" }
  let a ← require (source program output)
  let b ← require (callbacksSource program output)
  let c ← require (RoleViews.source program {output with moduleName := name, sourceModule := binding ++ "Callbacks"} binding selected.names)
  let sources := [
    (binding, a),
    (binding ++ "Callbacks", b),
    (name, c)]
  let sources ← if selected.names.any (fun names => !names.callbacks.isEmpty) then do
      pure (sources ++ [(name ++ "Library", ← require (librarySource program name))])
    else pure sources
  for (name, text) in sources do
    let path := System.FilePath.mk directory / (name.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path text
end Tests.Generators.ScalarViews
