import Tests.HelperReferenceLaws

/-! A reference selects mathematical behavior at reached calls in the existing
region traversal. Equal nominal types cannot identify operands or captures. -/
set_option autoImplicit false
namespace Tests.ReferenceOccurrences
open Zkc.Source Zkc.Source.Structured
open Tests.ConnectionHelperCertificate Tests.HelperReferenceLaws

private abbrev meaning (model : DomainModel) (changed := false) :=
  meaningOn model (closedMeaningsOn model (scalarProgram changed).payload.definitions)

private def twice : Region dialect [field, field, field] [field, field, field] :=
  .letOp (.invoke (scalarLeaf false).helper) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.invoke (scalarLeaf false).helper)
    (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)))

theorem two_calls (model : DomainModel) (a b c : model.Field "bls12-381.fr") :
    twice.denote (meaning model) (Values.cons a (.cons b (.cons c .nil)) : Values model.Value [field, field, field]).get =
      .done (.cons (c - (a - b)) (.cons (a - b) (.cons b .nil))) := by
  derive_reference_process [difference model] using (scalarProgram false).payload.linked

private def once : Region dialect scalarInputs [field] :=
  .letOp (.invoke (scalarLeaf false).helper) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

theorem conditional_call (model : DomainModel) (a b : model.Field "bls12-381.fr") (same : a = b) :
    once.denote (meaning model) (Values.cons a (.cons b .nil) : Values model.Value scalarInputs).get = .done (.cons (0 : model.Field "bls12-381.fr") .nil) := by
  derive_reference_process [equalDifference model] using (scalarProgram false).payload.linked

example (model : DomainModel) (_a _b : model.Field "bls12-381.fr") : True := by
  fail_if_success
    have : once.denote (meaning model) (Values.cons _a (.cons _b .nil) : Values model.Value scalarInputs).get = .done (.cons (0 : model.Field "bls12-381.fr") .nil) := by
      derive_reference_process [equalDifference model] using (scalarProgram false).payload.linked
  -- Even _a definitionally true conclusion requires the requested installation.
  fail_if_success
    have : once.denote (meaning model) (Values.cons _a (.cons _b .nil) : Values model.Value scalarInputs).get = .done (.cons (_a - _b) .nil) := by
      derive_reference_process [] using (scalarProgram false).payload.linked
  fail_if_success
    have : once.denote (meaning model true) (Values.cons _a (.cons _b .nil) : Values model.Value scalarInputs).get = .done (.cons (_a + _b) .nil) := by
      derive_reference_process [difference model] using (scalarProgram true).payload.linked
  trivial

example (model : DomainModel) (_a _b _c : model.Field "bls12-381.fr") : True := by
  fail_if_success
    have : twice.denote (meaning model) (Values.cons _a (.cons _b (.cons _c .nil)) : Values model.Value [field, field, field]).get =
        .done (.cons ((_a - _b) - _c) (.cons (_a - _b) (.cons _b .nil))) := by
      derive_reference_process [difference model] using (scalarProgram false).payload.linked
  trivial

/-- A stopped lexical body never tries to select a reference in its suffix. -/
example (model : DomainModel) (a b : model.Field "bls12-381.fr") :
    (Region.bind (Region.stop (out := []) .reject) once).denote (meaning model)
      (Values.cons a (.cons b .nil) : Values model.Value scalarInputs).get = .halt .reject := by
  derive_reference_process [] using (scalarProgram false).payload.linked

end Tests.ReferenceOccurrences
