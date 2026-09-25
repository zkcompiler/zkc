import Tools.Interactive.GenericReference
import Tools.Artifact.Runtime

set_option autoImplicit false

namespace Tests.VectorReference
open Tools.Interactive
open ScalarReference
open Lean (Json)

private def numbers (d : Domain) (v : Data (Scalar d)) : List Nat :=
  match v with
  | .matrix m => [m.rows, m.columns]
  | .field x => [x.val]
  | .vector xs | .polynomial xs => xs.map ZMod.val
  | .round r => [r.constant.val, r.linear.val, r.quadratic.val]
  | .boolean b => [if b then 1 else 0]
  | .index n => [n]
  | .indices ns => ns
private def run (d : Domain) (name : String) (attrs : List String) (xs : List (Data (Scalar d))) :=
  (ScalarReference.compute d name attrs xs).map (List.map (numbers d))

-- The same finite suite computes in every actual modular carrier.
private def vectorSuite (d : Domain) : Bool :=
  run d "vector.constant" [] [] == .ok [[]] &&
  run d "vector.constant" ["0", "7", toString (d.modulus - 1)] [] == .ok [[0, 7, d.modulus - 1]] &&
  run d "vector.scatter_sum" ["0"] [.vector []] == .ok [[]] &&
  run d "vector.scatter_sum" ["3"] [.vector []] == .ok [[0, 0, 0]] &&
  run d "vector.scatter_sum" ["4", "2", "0", "2"] [.vector [5, 7, 9]] == .ok [[7, 0, 14, 0]] &&
  run d "vector.scatter_sum" ["1", "0", "0"] [.vector [-1, 2]] == .ok [[1]] &&
  run d "vector.empty" [] [] == .ok [[]] &&
  run d "vector.append" [] [.vector [], .field 7] == .ok [[7]] &&
  run d "vector.splat" ["0"] [.field 4] == .ok [[]] &&
  run d "vector.splat" ["3"] [.field 4] == .ok [[4, 4, 4]] &&
  run d "vector.powers" ["4"] [.field 3] == .ok [[1, 3, 9, 27]] &&
  run d "vector.add" [] [.vector [1, 2], .vector [4, 5]] == .ok [[5, 7]] &&
  run d "vector.sub" [] [.vector [4, 5], .vector [1, 2]] == .ok [[3, 3]] &&
  run d "vector.mul" [] [.vector [1, 2], .vector [4, 5]] == .ok [[4, 10]] &&
  run d "vector.scale" [] [.vector [2, 3], .field 4] == .ok [[8, 12]] &&
  run d "vector.sum" [] [.vector []] == .ok [[0]] &&
  run d "vector.sum" [] [.vector [1, 2, 3]] == .ok [[6]] &&
  run d "vector.dot" [] [.vector [], .vector []] == .ok [[0]] &&
  run d "vector.dot" [] [.vector [2, 3], .vector [4, 5]] == .ok [[23]] &&
  run d "vector.split" [] [.vector [1, 2, 3, 4]] == .ok [[1, 2], [3, 4]] &&
  run d "vector.concat" [] [.vector [1, 2], .vector [3]] == .ok [[1, 2, 3]] &&
  run d "vector.at" ["1"] [.vector [7, 9]] == .ok [[9]] &&
  run d "vector.length_check" ["0"] [.vector []] == .ok [[1]] &&
  run d "vector.length_check" ["1"] [.vector []] == .ok [[0]] &&
  run d "vector.gather" ["2", "0", "2"] [.vector [5, 6, 7]] == .ok [[7, 5, 7]] &&
  run d "vector.gather" [] [.vector []] == .ok [[]] &&
  run d "vector.kronecker" [] [.vector [2, 3], .vector [4, 5]] == .ok [[8, 10, 12, 15]] &&
  run d "vector.kronecker" [] [.vector [], .vector [4]] == .ok [[]] &&
  run d "vector.matvec" ["2", "3", "0"] [.vector [1, 2, 3, 4, 5, 6], .vector [2, 3, 4]] == .ok [[20, 47]] &&
  run d "vector.matvec" ["2", "3", "1"] [.vector [1, 2, 3, 4, 5, 6], .vector [2, 3]] == .ok [[14, 19, 24]] &&
  run d "vector.matvec" ["2", "0", "0"] [.vector [], .vector []] == .ok [[0, 0]] &&
  run d "poly.from_coefficients" [] [.vector [1, 2, 0, 0]] == .ok [[1, 2]] &&
  run d "poly.from_coefficients" [] [.vector [0, 0]] == .ok [[]] &&
  run d "poly.coefficients" [] [.polynomial [1, 2]] == .ok [[1, 2]] &&
  run d "poly.degree_check" ["0"] [.polynomial []] == .ok [[1]] &&
  run d "poly.degree_check" ["1"] [.polynomial [1, 2, 3]] == .ok [[0]] &&
  run d "poly.univariate_evaluate" [] [.polynomial [1, 2, 3, 4], .field 2] == .ok [[49]] &&
  run d "poly.univariate_boundary" [] [.polynomial [1, 2, 3, 4]] == .ok [[11]] &&
  run d "poly.univariate_evaluate" [] [.polynomial [], .field 8] == .ok [[0]] &&
  run d "field.sub" [] [.field 0, .field 1] == .ok [[d.modulus - 1]] &&
  run d "field.neg" [] [.field 1] == .ok [[d.modulus - 1]] &&
  run d "field.inverse" [] [.field 2] == .ok [[(d.modulus + 1) / 2]]

example : vectorSuite .bls = true := by native_decide
example : vectorSuite .ristretto = true := by native_decide
example : vectorSuite .koalaBear = true := by native_decide
example : vectorSuite .bn254 = true := by native_decide

private def negativeSuite (d : Domain) : Bool :=
  run d "vector.constant" [toString d.modulus] [] == .error "noncanonical-field" &&
  run d "vector.constant" ["01"] [] == .error "noncanonical-natural" &&
  run d "vector.scatter_sum" [] [.vector []] == .error "kernel-attributes" &&
  run d "vector.scatter_sum" ["18446744073709551616"] [.vector []] == .error "kernel-attributes" &&
  run d "vector.scatter_sum" ["01"] [.vector []] == .error "noncanonical-natural" &&
  run d "vector.scatter_sum" ["1048577"] [.vector []] == .error "vector-limit" &&
  run d "vector.scatter_sum" ["2", "0"] [.vector [1, 2]] == .error "vector-shape" &&
  run d "vector.scatter_sum" ["2", "0", "1"] [.vector [1]] == .error "vector-shape" &&
  run d "vector.scatter_sum" ["0", "0"] [.vector [1]] == .error "vector-index" &&
  run d "vector.scatter_sum" ["2", "0", "2"] [.vector [1, 2]] == .error "vector-index" &&
  run d "vector.mul" [] [.vector [1], .vector []] == .error "vector-shape" &&
  run d "vector.dot" [] [.vector [], .vector [1]] == .error "vector-shape" &&
  run d "vector.split" [] [.vector []] == .error "vector-split-shape" &&
  run d "vector.split" [] [.vector [1, 2, 3]] == .error "vector-split-shape" &&
  run d "vector.at" ["0"] [.vector []] == .error "vector-index" &&
  run d "vector.gather" ["1"] [.vector [1]] == .error "vector-index" &&
  run d "vector.matvec" ["2", "2", "0"] [.vector [1, 2, 3], .vector [1, 2]] == .error "matrix-shape" &&
  run d "vector.matvec" ["2", "3", "1"] [.vector [1, 2, 3, 4, 5, 6], .vector [1, 2, 3]] == .error "matrix-shape" &&
  run d "poly.coefficients" [] [.polynomial [1, 0]] == .error "reference-scalar-value" &&
  run d "field.inverse" [] [.field 0] == .error "inverse-zero"
example : negativeSuite .bls = true := by native_decide
example : negativeSuite .ristretto = true := by native_decide
example : negativeSuite .koalaBear = true := by native_decide
example : negativeSuite .bn254 = true := by native_decide
example : (Zkc.Algebra.FiniteVectors.inverse (6 : ZMod 12)).map ZMod.val = .error "inverse-nonunit" := by native_decide
example : (Zkc.Algebra.FiniteVectors.inverse (5 : ZMod 12)).map ZMod.val = .ok 5 := by native_decide

private def wireRoundtrip (d : Domain) (kind : String) (v : Data (Scalar d)) : Result Bool := do
  let wire ← Tools.Artifact.arithmeticWire d v
  let decoded ← Tools.Artifact.decodeArithmeticWire d kind wire
  return decoded == v
example : wireRoundtrip .bls "vector" (.vector [1, 2, 3]) = .ok true := by native_decide
example : wireRoundtrip .ristretto "vector" (.vector []) = .ok true := by native_decide
example : wireRoundtrip .ristretto "polynomial" (.polynomial []) = .ok true := by native_decide
example : wireRoundtrip .ristretto "round" (.round ⟨1, 2, 3⟩) = .ok true := by native_decide
example : wireRoundtrip .koalaBear "vector" (.vector [0, 1, -1]) = .ok true := by native_decide
example : wireRoundtrip .koalaBear "round" (.round ⟨1, 2, 3⟩) = .ok true := by native_decide
example : (Tools.Artifact.arithmeticWire .koalaBear (.field (-1))).map Tools.Artifact.hex =
    .ok "5a4b435601130000007f" := by native_decide
example : (Tools.Artifact.arithmeticWire .koalaBear (.vector [1, 2])).map Tools.Artifact.hex =
    .ok "5a4b43560114020000000100000002000000" := by native_decide
example : (Tools.Artifact.arithmeticWire .koalaBear (.polynomial [])).map Tools.Artifact.hex =
    .ok "5a4b4356011500000000" := by native_decide

private def koalaDecode (kind input : String) := do
  let bytes ← Tools.Artifact.unhex input
  (Tools.Artifact.decodeArithmeticWire .koalaBear kind bytes).map (numbers .koalaBear)
example : koalaDecode "field" "5a4b435601130100007f" = .error "noncanonical-field" := by native_decide
example : koalaDecode "field" "5a4b435601130100000000" = .error "field-width" := by native_decide
example : koalaDecode "vector" "5a4b4356011401000000" = .error "scalar-vector-length" := by native_decide
example : koalaDecode "polynomial" "5a4b435601150100000000000000" = .error "polynomial-normalization" := by native_decide
example : koalaDecode "field" "5a4b4356010d01000000" = .error "wire-header" := by native_decide
example : (Tools.Artifact.arithmeticWire .ristretto (.field 1)).map Tools.Artifact.hex =
    .ok "5a4b4356010d0100000000000000000000000000000000000000000000000000000000000000" := by native_decide

private def decodeWire (kind : String) (tag : UInt8) (count : Nat) (xs : List Nat) (tail := ByteArray.empty) :=
  (Tools.Artifact.decodeArithmeticWire .ristretto kind
    ((Tools.Artifact.magic.push tag) ++ Tools.Artifact.little 4 count ++
      xs.foldl (fun b n => b ++ Tools.Artifact.little 32 n) ByteArray.empty ++ tail)).map (numbers .ristretto)
example : decodeWire "polynomial" 15 2 [1, 0] = .error "polynomial-normalization" := by native_decide
example : decodeWire "vector" 14 1 [Bindings.ristrettoModulus] = .error "noncanonical-field" := by native_decide
example : decodeWire "vector" 14 1 [1] (ByteArray.mk #[0]) = .error "scalar-vector-length" := by native_decide
example : decodeWire "vector" 14 4294967295 [] = .error "scalar-vector-length" := by native_decide
example : decodeWire "polynomial" 14 1 [1] = .error "wire-header" := by native_decide

private def location : Reference.Location := Reference.Location.plain "test" "root" "compute" "P"
private def result (outcome : Except Reference.Fault (List Reference.Value)) : String :=
  match outcome with
  | .ok values => (Reference.valuesJson values).compress
  | .error fault => fault.reason ++ ":" ++ fault.detail
private def vector (d : Domain) (xs : List (Scalar d)) : Reference.Value := Reference.Value.fromArithmetic d (.vector xs)

private def invoke (name domain : String) (attrs : List String) (xs : List Reference.Value)
    (state : Reference.State := {}) : String :=
  match TypedLocal.resolveRequest [⟨"op", name, [domain], ""⟩] "compute" "op" attrs with
  | .error e => e
  | .ok request => result ((Reference.compute location request xs).run state).1
example : invoke "vector.dot" Bindings.ristrettoScalar [] [vector .ristretto [2, 3], vector .ristretto [4, 5]] =
    "[[\"field:ristretto255.scalar\",\"23\"]]" := by native_decide
example : invoke "vector.dot" Bindings.ristrettoScalar [] [vector .ristretto [2], vector .bls [4]] =
    "refused:runtime-kernel-types" := by native_decide
example : invoke "vector.to_table" Bindings.fr [] [vector .bls []] = "refused:table-shape" := by native_decide
example : invoke "vector.to_table" Bindings.fr [] [vector .bls [9]] =
    "[[\"table:bls12-381.fr\",[\"0\",[\"9\"]]]]" := by native_decide
example : invoke "poly.equality_weights" Bindings.fr [] [.point [0, 1]] =
    "[[\"vector:bls12-381.fr\",[\"0\",\"1\",\"0\",\"0\"]]]" := by native_decide

private def rngState (budget := 4) : Reference.State :=
  { resources := [⟨"rng", "P", none, budget, .rrng [2, 3, 4], 0, 0⟩] }
private def rngRun (n budget : Nat) : String × Nat × Nat × Nat :=
  let (outcome, state) := (Reference.randomVector location .ristretto "rng" 0 n).run (rngState budget)
  match state.resources with
  | r :: _ => (result outcome, r.generation, r.draws, r.budget)
  | [] => ("missing-resource", 0, 0, 0)
example : rngRun 2 4 = ("[[\"vector:ristretto255.scalar\",[\"2\",\"3\"]],[\"rng:ristretto255.scalar\",[\"rng\",\"1\"]]]", 1, 2, 2) := by native_decide
example : rngRun 0 0 = ("[[\"vector:ristretto255.scalar\",[]],[\"rng:ristretto255.scalar\",[\"rng\",\"1\"]]]", 1, 0, 0) := by native_decide
example : rngRun 2 1 = ("exhausted:resource-budget", 0, 0, 1) := by native_decide
example : result ((Reference.randomDraw location "rng" 0 .bls).run rngState).1 =
    "refused:capability-identity" := by native_decide

private def group (tag : UInt8) (n : Nat := 0) : Reference.Value :=
  if tag == 16 then .rgroup (Tools.Artifact.magic.push 16 ++ Tools.Artifact.little 32 0)
  else .rgroups (Tools.Artifact.magic.push 17 ++ Tools.Artifact.little 4 n ++
    ByteArray.mk (Array.replicate (32 * n) 0))
private def msm (reply : List Reference.Value) : String :=
  let inputs := [vector .ristretto [2], group 17 1]
  let key := Reference.requestJson location "curve.msm" [Bindings.ristrettoGroup] [] inputs
  let state : Reference.State := { answers := Std.HashMap.ofList [(key.compress, .arr #[.str "ok", Reference.valuesJson reply])] }
  invoke "curve.msm" Bindings.ristrettoGroup [] inputs state
example : invoke "curve.msm" Bindings.ristrettoGroup [] [vector .ristretto [2], group 17 0] =
    "refused:vector-shape" := by native_decide
example : msm [.boolean true] = "refused:runtime-kernel-results" := by native_decide
example : msm [group 16] = (Reference.valuesJson [group 16]).compress := by native_decide
example : invoke "curve.msm" Bindings.ristrettoGroup [] [vector .ristretto [2], group 17 1] =
    "pending-primitive:exact-request-missing" := by native_decide
example : invoke "curve.split" Bindings.ristrettoGroup [] [group 17 0] = "refused:group-split-shape" := by native_decide

example : msm [.rgroup (Tools.Artifact.magic.push 16)] = "refused:group-length" := by native_decide
example : result ((Reference.validatePublic location (group 16) *> pure []).run {}).1 =
    "pending-primitive:exact-request-missing" := by native_decide
private def scaleEachWrongCount : String :=
  let inputs := [vector .ristretto [2], group 17 1]
  let key := Reference.requestJson location "curve.scale_each" [Bindings.ristrettoGroup] [] inputs
  let state : Reference.State := { answers := Std.HashMap.ofList [(key.compress,
    .arr #[.str "ok", Reference.valuesJson [group 17 0]])] }
  invoke "curve.scale_each" Bindings.ristrettoGroup [] inputs state
example : scaleEachWrongCount = "refused:group-count" := by native_decide

private def attributes : List String := ["Protocol", "call", "Function", "draw", "P"]
private def transcriptState : Reference.State :=
  { resources := [⟨"t", "P", none, 3, .transcript Bindings.ristrettoTranscript (ByteArray.mk #[1]) #[], 0, 0⟩] }
private def challengeBytes (bytes : ByteArray) : String := Id.run do
  let action := Reference.transcriptChallenge location attributes "t" 0 Bindings.ristrettoTranscript
  let (_, pending) := action.run transcriptState
  let some (.arr event) := pending.events.back? | return "missing-request"
  let some request := event[1]? | return "missing-request"
  let state := { transcriptState with answers := Std.HashMap.ofList [(request.compress, .arr #[.str "ok", .str (Tools.Artifact.hex bytes)])] }
  let (outcome, _) := action.run state
  match outcome with
  | .ok [value, .transcript _ "t" 1] =>
      match value.toArithmetic .ristretto with | .ok (.field x) => return toString x.val | _ => return "wrong-type"
  | .error error => return error.detail
  | _ => return "wrong-results"
example : challengeBytes (ByteArray.mk (#[1] ++ Array.replicate 63 0)) = "1" := by native_decide
example : challengeBytes (ByteArray.mk (Array.replicate 63 0 |>.push 1)) =
    toString ((256^63) % Bindings.ristrettoModulus) := by native_decide
example : challengeBytes (ByteArray.mk (Array.replicate 63 0)) = "transcript-challenge-width" := by native_decide
example : (Tools.Artifact.transcriptRequest ByteArray.empty #[] "unknown").isOk = false := by native_decide

private def reuseMask : String :=
  let action := do
    let _ ← Reference.randomVector location .ristretto "rng" 0 1
    Reference.randomVector location .ristretto "rng" 0 1
  result (action.run rngState).1
example : reuseMask = "refused:capability-stale" := by native_decide
private def nonceState : Reference.State :=
  { resources := [⟨"n", "P", none, 4, .rnonce (.committed 5), 0, 0⟩] }
example : result ((Reference.nonceResponseFor location .ristretto 3 7 "n" 0).run nonceState).1 =
    "[[\"field:ristretto255.scalar\",\"26\"]]" := by native_decide
private def reuseNonce : String :=
  let action := do
    let _ ← Reference.nonceResponseFor location .ristretto 3 7 "n" 0
    Reference.nonceResponseFor location .ristretto 3 7 "n" 1
  result (action.run nonceState).1
example : reuseNonce = "refused:nonce-stage" := by native_decide
example : result ((Reference.randomVector location .ristretto "n" 0 2).run nonceState).1 =
    "refused:capability-kind" := by native_decide

private def sourceBindings : List OperationBinding :=
  [⟨"coefficients", "poly.from_coefficients", [Bindings.ristrettoScalar], ""⟩,
   ⟨"degree", "poly.degree_check", [Bindings.ristrettoScalar], ""⟩,
   ⟨"eval", "poly.univariate_evaluate", [Bindings.ristrettoScalar], ""⟩,
   ⟨"boundary", "poly.univariate_boundary", [Bindings.ristrettoScalar], ""⟩]
private def sourceFunction : Explicit.Function :=
  ⟨⟨"Evaluate", [("coeffs", "vector:ristretto255.scalar"), ("x", "field:ristretto255.scalar")],
    ["field:ristretto255.scalar", "field:ristretto255.scalar", "bool"], some [
      .op "normalize" "coefficients" [] ["coeffs"] ["p"],
      .op "degree" "degree" ["3"] ["p"] ["bounded"],
      .op "eval" "eval" [] ["p", "x"] ["value"],
      .op "boundary" "boundary" [] ["p"] ["sum"], .ret ["value", "sum", "bounded"]]⟩, none⟩
private def sourceExecution : Result String := do
  let typed ← TypedLocal.elaborate sourceBindings sourceFunction
  return result ((Reference.executeFunction location typed [vector .ristretto [1, 2, 3, 4, 0],
    Reference.Value.fromArithmetic .ristretto (.field 2)]).run {}).1
example : sourceExecution = .ok "[[\"field:ristretto255.scalar\",\"49\"],[\"field:ristretto255.scalar\",\"11\"],[\"bool\",\"true\"]]" := by native_decide

private def artifactState : Tools.Artifact.State :=
  { cursor := ⟨ByteArray.empty, 0⟩, root := ByteArray.empty, configuration := .null, answers := #[] }
private def artifactLocation : Tools.Artifact.Location :=
  { entry := "main", binding := "root", path := [], protocol := "Protocol", role := "V", function := "Draw", operation := "draw" }
private def artifactDescriptor : Tools.Artifact.Descriptor :=
  ⟨"main", "P", "V", [], "rng", [("Draw", "draw")], 0,
    .arr #[.str "zkc.construction/1", .str "main", .str "P", .str "V", .arr #[], .arr #[], .str "0", .str Bindings.ristrettoTranscript, .str "normalized"]⟩
private def artifactSource : Source :=
  ⟨.explicit [⟨"eval", "poly.univariate_evaluate", [Bindings.ristrettoScalar], ""⟩,
    ⟨"draw", "random.draw", [Bindings.ristrettoScalar], ""⟩,
    ⟨"mask", "random.vector", [Bindings.ristrettoScalar], ""⟩], [], [], [], []⟩
private def artifactResult (outcome : Except Tools.Artifact.Failure (List Tools.Artifact.Value)) : String :=
  match outcome with
  | .error error => error.reason ++ ":" ++ error.detail
  | .ok values => match values.mapM (Tools.Artifact.Value.jsonFor) with
    | .ok values => (Json.arr values.toArray).compress | .error error => error
private def artifactEvaluation : String :=
  artifactResult ((Tools.Artifact.evaluate artifactSource artifactDescriptor artifactLocation "eval" []
    [.arithmetic .ristretto (.polynomial [1, 2, 3, 4]), .arithmetic .ristretto (.field 2)]).run artifactState).1
example : artifactEvaluation = "[[\"field:ristretto255.scalar\",\"5a4b4356010d3100000000000000000000000000000000000000000000000000000000000000\"]]" := by native_decide
-- Vector masking is a source RNG operation, outside the artifact selected-challenge profile.
example : artifactResult ((Tools.Artifact.evaluate artifactSource artifactDescriptor artifactLocation "mask" ["2"]
    [.ristrettoRng 0]).run artifactState).1 = "refused:unimplemented-validator-kernel" := by native_decide
private def artifactChallenge : String := Id.run do
  let action := Tools.Artifact.evaluate artifactSource artifactDescriptor artifactLocation "draw" [] [.ristrettoRng 0]
  let (.error pending, _) := action.run artifactState | return "missing-request"
  let state := { artifactState with answers := #[⟨pending.request,
    .arr #[.str "ok", .str (Tools.Artifact.hex (ByteArray.mk (#[1] ++ Array.replicate 63 0)))]⟩] }
  match (action.run state).1 with
  | .ok [.arithmetic .ristretto (.field x), .ristrettoRng 1] => return toString x.val
  | .error error => return error.detail
  | _ => return "wrong-results"
example : artifactChallenge = "1" := by native_decide

end Tests.VectorReference
