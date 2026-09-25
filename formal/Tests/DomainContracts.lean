import Tools.Interactive.PhysicalLocal

set_option autoImplicit false

namespace Tests.DomainContracts
open Tools.Interactive
open Bindings

private def resolve (contract domain : String) (implementation : String := "") (physical := false) :=
  Bindings.resolve physical ⟨"op", contract, [domain], implementation⟩

example : defaultRepresentation "field" ristrettoScalar = "dalek.scalar/1" := by native_decide
example : defaultRepresentation "vector" fr = "arkworks.fr-vector/1" := by native_decide
example : defaultRepresentation "vector" ristrettoScalar = "dalek.scalar-vector/1" := by native_decide
example : defaultRepresentation "table" ristrettoScalar = "" := by native_decide
example : defaultRepresentation "field" koalaBear = "plonky3.koala-bear/1" := by native_decide
example : defaultRepresentation "rng" koalaBear = "" := by native_decide
example : defaultRepresentation "table" koalaBear = "" := by native_decide
example : (resolve "vector.dot" koalaBear "plonky3/vector.dot" true).isOk = true := by native_decide
example : (resolve "vector.dot" koalaBear "arkworks/vector.dot" true).isOk = false := by native_decide
example : (resolve "vector.dot" fr "plonky3/vector.dot" true).isOk = false := by native_decide
example : (resolve "random.vector" koalaBear).isOk = false := by native_decide
example : (resolve "curve.response" koalaBear).isOk = false := by native_decide
example : (resolve "poly.product_sum" koalaBear).isOk = false := by native_decide
example : associatedIdentity koalaBear "Scalar" = .error "binding-associated-identity" := by native_decide
example : attributes false "field.constant" ["2130706433"] koalaBear =
    .error "noncanonical-field" := by native_decide
example : (valueType true "vector:ristretto255.scalar@arkworks.fr-vector/1").isOk = false := by native_decide
example : (valueType true "groups:ristretto255.group@dalek.ristretto-diagonal/1").isOk = true := by native_decide
example : (valueType true "vector:ristretto255.scalar@dalek.scalar-diagonal/1").isOk = false := by native_decide
example : associatedIdentity ristrettoGroup "Scalar" = .ok ristrettoScalar := by native_decide
example : associatedIdentity ristrettoTranscript "ChallengeField" = .ok ristrettoScalar := by native_decide
example : associatedIdentity ristrettoGroup "PointField" = .error "binding-associated-identity" := by native_decide
example : StaticSort.codec.accepts "zkcv.vector.ristretto255.scalar/1" = true := by native_decide
example : StaticSort.codec.accepts "zkcv.vector.ristretto255.scalar/2" = false := by native_decide
example : (resolve "poly.product_sum" ristrettoScalar).isOk = false := by native_decide
example : (resolve "pcs.check" ristrettoGroup).isOk = false := by native_decide
example : (resolve "field.inverse" ristrettoScalar "dalek/field.inverse").isOk = true := by native_decide
example : (resolve "field.inverse" ristrettoScalar "arkworks/field.inverse").isOk = false := by native_decide
example : (resolve "poly.univariate_evaluate" fr "arkworks-msb/poly.univariate_evaluate").isOk = false := by native_decide
example : (resolve "vector.not_installed" fr "arkworks/vector.not_installed").isOk = false := by native_decide
example : (resolve "curve.scale_each" ristrettoGroup).map (·.inputs) =
    .ok [⟨"vector", ristrettoScalar, ""⟩, ⟨"groups", ristrettoGroup, ""⟩] := by native_decide
example : (resolve "curve.vector_scale" ristrettoGroup).map (·.inputs) =
    .ok [⟨"groups", ristrettoGroup, ""⟩, ⟨"field", ristrettoScalar, ""⟩] := by native_decide
example : (resolve "vector.mul" fr "arkworks-diagonal/vector.mul" true).map (·.outputs) =
    .ok [⟨"vector", fr, "arkworks.fr-diagonal/1"⟩] := by native_decide
example : (resolve "curve.msm" ristrettoGroup "dalek-diagonal/curve.msm" true).map (·.inputs) =
    .ok [⟨"vector", ristrettoScalar, "dalek.scalar-vector/1"⟩,
      ⟨"groups", ristrettoGroup, "dalek.ristretto-diagonal/1"⟩] := by native_decide
example : (resolve "curve.msm" g1 "dalek-diagonal/curve.msm" true).isOk = false := by native_decide
example : (resolve "vector.mul" ristrettoScalar "arkworks-diagonal/vector.mul" true).isOk = false := by native_decide
example : (Bindings.resolve false ⟨"o", "transcript.observe.vector",
    [ristrettoTranscript, ristrettoScalar, codec "vector" ristrettoScalar], "dalek/transcript.observe.vector"⟩).isOk = true := by native_decide
example : (Bindings.resolve false ⟨"o", "transcript.observe.vector",
    [ristrettoTranscript, fr, codec "vector" fr], ""⟩).isOk = false := by native_decide
example : attributes false "field.constant" [toString ristrettoModulus] ristrettoScalar =
    .error "noncanonical-field" := by native_decide
example : attributes true "field.constant" [toString ristrettoModulus] = .ok () := by native_decide
example : attributes false "vector.gather" [] = .ok () := by native_decide
example : attributes false "vector.matvec" ["2", "3", "2"] = .error "kernel-attributes" := by native_decide
example : attributes false "vector.at" ["01"] = .error "noncanonical-natural" := by native_decide
example : PhysicalLocal.supported ⟨"x", "field.add", [fr], "arkworks/field.add"⟩ = true := by native_decide
example : PhysicalLocal.supported ⟨"x", "field.add", [ristrettoScalar], "dalek/field.add"⟩ = true := by native_decide
example : PhysicalLocal.supported ⟨"x", "poly.coefficients", [fr], "arkworks/poly.coefficients"⟩ = true := by native_decide

private def vectorTy := "vector:bls12-381.fr"
private def scalarTy := "field:bls12-381.fr"
private def bindings : List OperationBinding :=
  [⟨"mul", "vector.mul", [fr], ""⟩, ⟨"dot", "vector.dot", [fr], ""⟩]
private def code : List Instruction :=
  [.op "multiply" "mul" [] ["f", "v"] ["d"],
   .op "contract" "dot" [] ["w", "d"] ["z"], .ret ["z"]]
private def logical : Explicit.Function :=
  ⟨⟨"Pair", [("f", vectorTy), ("v", vectorTy), ("w", vectorTy)], [scalarTy], some code⟩, none⟩
private def candidate (body := code) : Explicit.CandidateLocals :=
  ⟨true, [⟨"mul", "vector.mul", [fr], "arkworks-diagonal/vector.mul"⟩,
    ⟨"dot", "vector.dot", [fr], "arkworks-diagonal/vector.dot"⟩],
    [⟨⟨"Pair", logical.code.arguments.map (fun (n, ty) => (n, ty ++ "@arkworks.fr-vector/1")),
      [scalarTy ++ "@arkworks.fr/1"], some body⟩, none⟩], .null, .null⟩

-- Both logical operations, their sites and intermediate correspondence survive.
example : (Generic.validateClosed logical bindings candidate "Pair").isOk = true := by native_decide
example : (Generic.validateClosed logical bindings (candidate code.tail) "Pair").isOk = false := by native_decide
example : (TypedLocal.elaborate bindings logical).isOk = true := by native_decide

private def ristrettoLogical : Explicit.Function :=
  ⟨⟨"GroupPair", [("f", "vector:ristretto255.scalar"), ("v", "groups:ristretto255.group"),
    ("w", "vector:ristretto255.scalar")], ["group:ristretto255.group"], some code⟩, none⟩
private def ristrettoBindings : List OperationBinding :=
  [⟨"mul", "curve.scale_each", [ristrettoGroup], ""⟩, ⟨"dot", "curve.msm", [ristrettoGroup], ""⟩]
private def ristrettoCandidate : Explicit.CandidateLocals :=
  ⟨true, [⟨"mul", "curve.scale_each", [ristrettoGroup], "dalek-diagonal/curve.scale_each"⟩,
    ⟨"dot", "curve.msm", [ristrettoGroup], "dalek-diagonal/curve.msm"⟩],
    [⟨⟨"GroupPair", [("f", "vector:ristretto255.scalar@dalek.scalar-vector/1"),
      ("v", "groups:ristretto255.group@dalek.ristretto-vector/1"),
      ("w", "vector:ristretto255.scalar@dalek.scalar-vector/1")],
      ["group:ristretto255.group@dalek.ristretto/1"], some code⟩, none⟩], .null, .null⟩
example : (Generic.validateClosed ristrettoLogical ristrettoBindings ristrettoCandidate "GroupPair").isOk = true := by native_decide

private def sharedCode : List Instruction :=
  [.op "multiply" "mul" [] ["f", "v"] ["d"],
   .op "contract" "dot" [] ["w", "d"] ["z"],
   .op "contract_again" "dot" [] ["f", "d"] ["z2"], .ret ["z", "z2"]]
private def shared (function : Explicit.Function) : Explicit.Function :=
  { function with code := { function.code with
      results := function.code.results ++ function.code.results, body := some sharedCode } }
private def sharedCandidate (candidate : Explicit.CandidateLocals) : Explicit.CandidateLocals :=
  { candidate with functions := candidate.functions.map shared }

-- The same immutable product has two compatible consumers in each installed
-- domain. Both source operation sites and the reused SSA name survive.
example : (Generic.validateClosed (shared logical) bindings
    (sharedCandidate candidate) "Pair").isOk = true := by native_decide
example : (Generic.validateClosed (shared ristrettoLogical) ristrettoBindings
    (sharedCandidate ristrettoCandidate) "GroupPair").isOk = true := by native_decide

private def formation (body : List Instruction) : Result Unit :=
  PhysicalFormation.check candidate.bindings { (candidate.functions.headD logical).code with body := some body }
example : formation [
    .op "multiply" "mul" [] ["f", "v"] ["d"],
    .op "contract" "dot" [] ["d", "w"] ["z"], .ret ["z"]] =
    .error "binding-operation-signature" := by native_decide
example : formation [
    .op "multiply" "mul" [] ["f", "v"] ["d"],
    .op "nested" "mul" [] ["f", "d"] ["e"],
    .op "contract" "dot" [] ["w", "e"] ["z"], .ret ["z"]] =
    .error "binding-operation-signature" := by native_decide
-- One valid contraction does not excuse a second ineligible use.
example : formation [
    .op "multiply" "mul" [] ["f", "v"] ["d"],
    .op "contract" "dot" [] ["w", "d"] ["z"],
    .op "bad" "mul" [] ["f", "d"] ["e"], .ret ["z"]] =
    .error "binding-operation-signature" := by native_decide
example : formation [
    .op "multiply" "mul" [] ["f", "v"] ["d"],
    .op "unused" "mul" [] ["f", "v"] ["e"],
    .op "contract" "dot" [] ["w", "d"] ["z"], .ret ["z"]] =
    .error "diagonal-unused" := by native_decide
example : formation [
    .op "multiply" "mul" [] ["f", "v"] ["d"],
    .loop "escape" (.constant 1) [] ["d"] [.yield []] [], .ret []] =
    .error "invalid-function-body" := by native_decide

private def escaped : Function := { (candidate.functions.headD logical).code with
  results := [vectorTy ++ "@arkworks.fr-diagonal/1"]
  body := some [.op "multiply" "mul" [] ["f", "v"] ["d"], .ret ["d"]] }
example : PhysicalFormation.check candidate.bindings escaped =
    .error "diagonal-boundary" := by native_decide
private def borrowed : Function := { (candidate.functions.headD logical).code with
  arguments := [("w", vectorTy ++ "@arkworks.fr-vector/1"),
    ("d", vectorTy ++ "@arkworks.fr-diagonal/1")]
  body := some [.op "contract" "dot" [] ["w", "d"] ["z"], .ret ["z"]] }
example : PhysicalFormation.check candidate.bindings borrowed =
    .error "diagonal-boundary" := by native_decide
example : PhysicalFormation.check ristrettoCandidate.bindings (candidate.functions.headD logical).code =
    .error "binding-operation-signature" := by native_decide
example : PhysicalLocal.supported ⟨"x", "vector.mul", [fr], "arkworks-diagonal/vector.mul"⟩ = false := by native_decide
example : PhysicalLocal.supported ⟨"x", "curve.msm", [ristrettoGroup], "dalek-diagonal/curve.msm"⟩ = false := by native_decide

private def specializedConstant : Result (List Instruction) := do
  let definition : Generic.Definition :=
    ⟨"Constant", [("F", .field)], [.relation "PrimeField" [.root "F"]], [],
      [⟨"field", some (.root "F")⟩],
      [⟨"c", "field.constant", [.root "F"], [toString (ristrettoModulus + 9)], [], ["x"], false⟩], ["x"], []⟩
  let checked ← Generic.checkDefinition definition
  let (function, _) ← Generic.specialize ⟨"R", "Constant", [("F", ristrettoScalar)], []⟩ checked
  return function.code.body.getD []

example : (specializedConstant.toOption == some [
    .op "c" "reference_binding_0" ["9"] [] ["x"], .ret ["x"]]) = true := by native_decide

end Tests.DomainContracts

-- The independent checker admits the mathematical dense binding. This is not
-- a theorem about native leakage or a grant to a runtime role.
example : Tools.Interactive.Bindings.resolve true
    ⟨"m", "curve.msm", [Tools.Interactive.Bindings.ristrettoGroup], "dalek-vartime/curve.msm"⟩ =
    Tools.Interactive.Bindings.resolve true
    ⟨"m", "curve.msm", [Tools.Interactive.Bindings.ristrettoGroup], "dalek/curve.msm"⟩ := by native_decide
example : (Tools.Interactive.Bindings.resolve true
    ⟨"m", "curve.msm", [Tools.Interactive.Bindings.g1], "dalek-vartime/curve.msm"⟩).isOk = false := by native_decide
example : (Tools.Interactive.Bindings.resolve true
    ⟨"m", "curve.scale_each", [Tools.Interactive.Bindings.ristrettoGroup], "dalek-vartime/curve.msm"⟩).isOk = false := by native_decide
