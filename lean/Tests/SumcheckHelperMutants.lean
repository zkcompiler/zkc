module

public import ZkcExamples.Structured.SumcheckSourceContracts

@[expose] public section
namespace Tests.SumcheckHelperMutants
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open PrimitiveLibrary MapPrefixBodies SumcheckHelperBodies SumcheckHelperLaws
/-- A test-only candidate; complete source admission is never inferred from this constructor. -/
def checkedBody (helper : Helper) (body : Region dialect helper.inputs helper.outputs) :
    CheckedDefinition :=
  ⟨helper.name, helper.kind, helper.inputs, helper.outputs,
    body.erase, body, body.elaborate_erase⟩

/-! Same-name, same-signature bodies used by semantic lookup controls. -/
def sumsSwappedBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke halvesHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

def checkTableIgnoreClaimBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke tableHelper) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke prefixHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.invoke valuesRealizationHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.exec (.fieldEqual "bls12-381.fr")) (.cons .here (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def checkFalseAcceptBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.booleanConstant true) .nil .nil <|
  .ret (.cons .here .nil)

def checkAcceptMalformedBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke shapeHelper) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))) (.cons checkTrueBody (.cons checkFalseAcceptBody .nil)) <|
  .ret (.cons .here .nil)


def sumsSwappedDefinition := checkedBody sumsHelper sumsSwappedBody
def checkAcceptMalformedDefinition := checkedBody checkHelper checkAcceptMalformedBody
def checkTableIgnoreClaimDefinition := checkedBody checkTableHelper checkTableIgnoreClaimBody

def checkPermutedBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean] :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke shapeHelper) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))) (.cons checkTrueBody (.cons checkFalseBody .nil)) <|
  .ret (.cons .here .nil)


def checkPermutedDefinition := checkedBody checkHelper checkPermutedBody



variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
theorem sums_swapped_expansion (table : Meanings F G) (xs : List F) (dimension columns : Nat) :
    sumsSwappedBody.denote (meaning F G table) (inputs xs dimension columns).get =
      (invoke table halvesHelper (inputs xs dimension columns)).bind fun halves =>
        .done (messageResult (halves.get (.there .here)).sum (halves.get .here).sum) := by
  simp only [sumsSwappedBody, inputs, messageResult, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons, Values.get,
    prepend_empty, prepend_one, prepend_two, prepend_three, Environment.prepend,
    Environment.push, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
    Primitive.evaluate, primitiveOutcome, ← List.sum_eq_foldl]

  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
theorem check_permuted_expansion (table : Meanings F G) (xs point : List F) (claim : F) :
    checkPermutedBody.denote (meaning F G table) (checkInputs xs point claim).get =
      if point.length < indexLimit then
        (invoke table shapeHelper (inputs xs point.length 1)).bind fun valid =>
          if valid.get .here then invoke table checkTableHelper (checkInputs point xs claim)
          else .done (boolResult false)
      else .halt .exhausted := by
  simp only [checkPermutedBody, checkTrueBody, checkFalseBody, checkInputs, inputs, boolResult,
    Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get,
    prepend_empty, prepend_one, prepend_two, prepend_three, Environment.prepend,
    Environment.push, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
    Primitive.evaluate]
  split
  · simp only [primitiveOutcome, PIR.Process.bind, show 1 < indexLimit by decide +kernel,
      ite_true, Values.get_cons, Values.get, Environment.push, Evaluation.invokeCallback]
    congr 1
    funext valid
    cases valid with
    | cons b rest =>
      cases rest
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        PIR.Process.bind, Values.get_cons, Values.get, Environment.prepend, Environment.push,
        singleton_eta, PIR.Process.bind_done]
      rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
theorem check_accept_malformed_expansion (table : Meanings F G) (xs point : List F) (claim : F) :
    checkAcceptMalformedBody.denote (meaning F G table) (checkInputs xs point claim).get =
      if point.length < indexLimit then
        (invoke table shapeHelper (inputs xs point.length 1)).bind fun valid =>
          if valid.get .here then invoke table checkTableHelper (checkInputs xs point claim)
          else .done (boolResult true)
      else .halt .exhausted := by
  simp only [checkAcceptMalformedBody, checkTrueBody, checkFalseAcceptBody, checkInputs, inputs, boolResult,
    Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get,
    prepend_empty, prepend_one, prepend_two, prepend_three, Environment.prepend,
    Environment.push, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
    Primitive.evaluate]
  split
  · simp only [primitiveOutcome, PIR.Process.bind, show 1 < indexLimit by decide +kernel,
      ite_true, Values.get_cons, Values.get, Environment.push, Evaluation.invokeCallback]
    congr 1
    funext valid
    cases valid with
    | cons b rest =>
      cases rest
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        PIR.Process.bind, Values.get_cons, Values.get, Environment.prepend, Environment.push,
        singleton_eta, PIR.Process.bind_done]
      rfl
  · rfl

set_option linter.unusedSimpArgs false in
theorem check_ignore_claim_expansion (table : Meanings F G) (xs point : List F) (claim : F) :
    checkTableIgnoreClaimBody.denote (meaning F G table) (checkInputs xs point claim).get =
      if point.length < indexLimit then
        (invoke table tableHelper (inputs xs point.length 1)).bind fun constructed =>
        (invoke table prefixHelper (constructed.append (.cons point .nil))).bind fun residual =>
        (invoke table valuesRealizationHelper residual).bind fun values =>
        .done (boolResult (decide ((values.get .here).sum = (values.get .here).sum)))
      else .halt .exhausted := by
  simp only [checkTableIgnoreClaimBody, checkInputs, inputs, boolResult, Region.denote, meaning,
    Evaluation.meaning, Evaluation.operation, Operands.eval, Regions.denote,
    Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate]
  split
  · simp only [primitiveOutcome, PIR.Process.bind, show 1 < indexLimit by decide +kernel,
      ite_true, Values.get_cons, Values.get, Environment.push, ← List.sum_eq_foldl]
    congr 1
    funext constructed
    cases constructed with
    | cons xs rest =>
      cases rest with
      | cons n rest =>
        cases rest with
        | cons w rest =>
          cases rest
          congr 1
          funext residual
          cases residual with
          | cons xs rest =>
            cases rest with
            | cons n rest =>
              cases rest with
              | cons w rest => cases rest; rfl
  · rfl

end Tests.SumcheckHelperMutants
