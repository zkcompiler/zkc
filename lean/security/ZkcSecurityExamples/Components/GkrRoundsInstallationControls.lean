module

public import ZkcSecurity.Bindings.Gkr.RoundsProcessInstallation
public import Zkc.Source.Structured.BodyBindings
public import Zkc.Source.Structured.UnitViews
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Compact independently admitted clients of the retained GKR helper installation.
The second client actually performs a second restriction. Admission and exact
body association are checked separately from the mathematical equations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace ZkcSecurity.Examples.Components.GkrRoundsInstallationControls
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Bindings.Gkr
open GkrRoundsHelpers GkrRoundsProcesses
open ZkcExamples.Structured.SumcheckHelperLaws (prepend_empty prepend_one)
noncomputable section

abbrev scalar : Ty := .field "bls12-381.fr"
abbrev vector : Ty := .vector "bls12-381.fr"

/-- The same complete scalar reference body, expressed in source syntax. -/
def interpolation : Function where
  name := interpolationHelper.name
  kind := .math
  visibility := .privateDef
  inputs := [scalar, scalar, scalar]
  outputs := [scalar]
  interface := none
  preconditions := []
  origin := none
  body := .block [
    .instruction (.fieldSubtract "bls12-381.fr") [1, 0] [scalar] [] "",
    .instruction (.fieldMultiply "bls12-381.fr") [0, 3] [scalar] [] "",
    .instruction (.fieldAdd "bls12-381.fr") [2, 0] [scalar] [] ""
  ] (.ret [0])

def interpolationCallback : Function where
  name := interpolationCallbackHelper.name
  kind := .local
  visibility := .privateDef
  inputs := [scalar, scalar, vector, vector, scalar]
  outputs := [scalar]
  interface := none
  preconditions := []
  origin := some (.local interpolationCallbackHelper.name [])
  body := .block [
    .instruction (.apply interpolationRealizationHelper.name) [0, 1, 4] [scalar] [] "body"
  ] (.ret [0])

def factorRestriction : Function where
  name := factorRestrictionHelper.name
  kind := .local
  visibility := .privateDef
  inputs := [vector, scalar]
  outputs := [vector]
  interface := none
  preconditions := []
  origin := some (.local factorRestrictionHelper.name [])
  body := .block [
    .instruction (.exec "exec.apply" "split" []) [0] [vector, vector] [] "s0",
    .instruction (.apply interpolationsHelper.name) [0, 1, 3] [vector] [] "s4"
  ] (.ret [0])

def interpolationDomain : Domain :=
  ⟨interpolationsCollection.domain.name, [vector, vector], [.elements 0, .elements 1, .zip [1, 0]], 0⟩

def library : List Definition :=
  [.function interpolation,
    .realization ⟨interpolationRealizationHelper.name, [scalar, scalar, scalar], [scalar],
      interpolationHelper.name⟩,
    .function interpolationCallback,
    .collect ⟨interpolationsHelper.name, .privateDef, [vector, vector, scalar], [vector],
      interpolationDomain.name, interpolationCallbackHelper.name, ""⟩,
    .function factorRestriction]

def application (twice : Bool) : Function where
  name := "restrict_values"
  kind := .local
  visibility := .privateDef
  inputs := [vector, scalar, scalar]
  outputs := [vector]
  interface := none
  preconditions := []
  origin := some (.local "restrict_values" [])
  body := .block
    ([.instruction (.apply factorRestrictionHelper.name) [0, 1] [vector] [] "first"] ++
      if twice then
        [.instruction (.apply factorRestrictionHelper.name) [0, 3] [vector] [] "second"]
      else []) (.ret [0])

def root : Function where
  name := "restriction_client"
  kind := .protocol
  visibility := .publicDef
  inputs := [vector, scalar, scalar]
  outputs := [vector]
  interface := some ⟨["P", "V"], [["P"], ["P"], ["P"]], [["P"]]⟩
  preconditions := []
  origin := some (.protocol ⟨"restriction_client", []⟩)
  body := .block
    [.instruction (.localCall "restrict_values" "P") [0, 1, 2] [vector] [] "restrict"] (.ret [0])

def snapshot (twice : Bool) : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := root.name
  domains := [interpolationDomain]
  relations := []
  bindings := [⟨"split", "vector.split", ["bls12-381.fr"], "", none⟩]
  definitions := library ++ [.function (application twice), .function root]
  contracts := [⟨root.name, []⟩]
  catalogue := blsCatalogue

abbrev applicationHelper : Helper := ⟨"restrict_values", .local, [vector, scalar, scalar], [vector]⟩

def applicationBody (twice : Bool) : Region dialect applicationHelper.inputs applicationHelper.outputs :=
  .letOp (.mark "first") .nil .nil <|
  .letOp (.invoke factorRestrictionHelper) (.cons .here (.cons (.there .here) .nil)) .nil <|
  if twice then
    .letOp (.mark "second") .nil .nil <|
    .letOp (.invoke factorRestrictionHelper)
      (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
    .ret (.cons .here .nil)
  else .ret (.cons .here .nil)

abbrev rootSignature : ProtocolSignature :=
  ⟨"restriction_client", ["P", "V"], [vector, scalar, scalar], [vector], [[0], [0], [0]], [[0]]⟩

def rootBody : Region protocolDialect rootSignature.inputs rootSignature.outputs :=
  .letOp (.mark "restrict") .nil .nil <|
  .letOp (.localCall applicationHelper rfl 0 "restrict")
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

namespace Single
structured_views (snapshot false) helpers
  [interpolation := (interpolationHelper, interpolationBody),
   interpolationRealization := (interpolationRealizationHelper, interpolationRealizationBody),
   interpolationCallback := (interpolationCallbackHelper, interpolationCallbackBody),
   interpolations := (interpolationsHelper, interpolationsBody),
   factorRestriction := (factorRestrictionHelper, factorRestrictionBody),
   application := (applicationHelper, applicationBody false)]
  protocols [root := (rootSignature, rootBody)]
end Single

namespace Double
structured_views (snapshot true) helpers
  [interpolation := (interpolationHelper, interpolationBody),
   interpolationRealization := (interpolationRealizationHelper, interpolationRealizationBody),
   interpolationCallback := (interpolationCallbackHelper, interpolationCallbackBody),
   interpolations := (interpolationsHelper, interpolationsBody),
   factorRestriction := (factorRestrictionHelper, factorRestrictionBody),
   application := (applicationHelper, applicationBody true)]
  protocols [root := (rootSignature, rootBody)]
end Double

/-- A type-correct mutation of a reached transitive dependency. Admission is
allowed; the original mathematical installation must reject its association. -/
def changedInterpolation : Function :=
  { interpolation with body := (.block [
    .instruction (.fieldSubtract "bls12-381.fr") [1, 0] [scalar] [] "",
    .instruction (.fieldMultiply "bls12-381.fr") [0, 3] [scalar] [] "",
    .instruction (.fieldAdd "bls12-381.fr") [3, 0] [scalar] [] ""
  ] (.ret [0])) }

def changedInterpolationBody : Region dialect interpolationHelper.inputs interpolationHelper.outputs :=
  .letOp (.fieldSubtract "bls12-381.fr")
    (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr")
    (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr")
    (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def changedDependency : Snapshot :=
  { (snapshot false) with definitions :=
      ((Definition.function changedInterpolation) ::
        library.tail ++ [.function (application false), .function root]) }

namespace ChangedDependency
structured_views changedDependency helpers
  [interpolation := (interpolationHelper, changedInterpolationBody),
   interpolationRealization := (interpolationRealizationHelper, interpolationRealizationBody),
   interpolationCallback := (interpolationCallbackHelper, interpolationCallbackBody),
   interpolations := (interpolationsHelper, interpolationsBody),
   factorRestriction := (factorRestrictionHelper, factorRestrictionBody),
   application := (applicationHelper, applicationBody false)]
  protocols [root := (rootSignature, rootBody)]
end ChangedDependency

/-- The immediate wrapper still associates, but cannot hide its changed callee. -/
example : BodyIn ChangedDependency.unit.definitions factorRestrictionHelper factorRestrictionBody := by
  bind_structured_bodies

example : True := by
  fail_if_success
    have wrong : RoundsHelperInstallation.RestrictionBodies ChangedDependency.unit.definitions := by
      bind_structured_bodies
  trivial

abbrev single : Program := Single.program
abbrev double : Program := Double.program

theorem single_admitted : check (snapshot false) = .ok single := Single.kernel_admission
theorem double_admitted : check (snapshot true) = .ok double := Double.kernel_admission

theorem single_bodies : RoundsHelperInstallation.RestrictionBodies single.payload.definitions := by
  bind_structured_bodies

theorem double_bodies : RoundsHelperInstallation.RestrictionBodies double.payload.definitions := by
  bind_structured_bodies

theorem single_application :
    BodyIn single.payload.definitions applicationHelper (applicationBody false) := by
  bind_structured_bodies

theorem double_application :
    BodyIn double.payload.definitions applicationHelper (applicationBody true) := by
  bind_structured_bodies

/-- Same helper ABI, different used body: the second call is not dead data. -/
example : (applicationBody false).erase ≠ (applicationBody true).erase := by
  intro same
  have lengths := congrArg (fun raw : RawRegion Ty Op => raw.operations.length) same
  change 2 = 4 at lengths
  omega

/-- An unchanged signature cannot associate the first client's body with the
second client's actual declaration. The association search must refuse it. -/
example : True := by
  fail_if_success
    have wrong : BodyIn double.payload.definitions applicationHelper (applicationBody false) := by
      bind_structured_bodies
  trivial

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Reuse the installed restriction law through each actual complete caller.
The equation retains both sequential calls and every possible stop. -/
theorem application_equation {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) (bodies : RoundsHelperInstallation.RestrictionBodies definitions)
    (twice : Bool) (associated : BodyIn definitions applicationHelper (applicationBody twice))
    (xs : List F) (first second : F) :
    invoke (RoundsHelperInstallation.table (G := G) definitions) applicationHelper
      (.cons xs (.cons first (.cons second .nil))) =
      (RoundsProcessInstallation.fix definitions xs first).bind fun result =>
        if twice then RoundsProcessInstallation.fix definitions (result.get .here) second
        else .done result := by
  obtain ⟨definition, member, signature, exactRaw⟩ := associated
  rw [Evaluation.definitions_invoke_body_view_as (.silent _)
    definitions linked definition member applicationHelper signature (applicationBody twice) exactRaw]
  cases twice with
  | false =>
    simp only [applicationBody, Bool.false_eq_true, ↓reduceIte, Region.denote,
      Evaluation.meaning, Evaluation.operation, Operands.eval, Regions.denote,
      Values.get_cons, prepend_empty, prepend_one, Environment.push,
      SiteObservations.silent, PIR.Process.bind]
    change (invoke (RoundsHelperInstallation.table definitions) factorRestrictionHelper
      (.cons xs (.cons first .nil))).bind
      (fun (result : Values (assignment F G) [vector]) =>
        (PIR.Process.done (.cons (result.get .here) .nil) :
          PIR.Process (participantInterface F G) (Values (assignment F G) [vector]))) = _
    rw [RoundsProcessInstallation.fix_equation linked bodies]
    congr 1
    funext result
    cases result with | cons result rest => cases rest; rfl
  | true =>
    simp only [applicationBody, ↓reduceIte, Region.denote,
      Evaluation.meaning, Evaluation.operation, Operands.eval, Regions.denote,
      Values.get_cons, prepend_empty, prepend_one, Environment.push,
      SiteObservations.silent, PIR.Process.bind]
    change (invoke (RoundsHelperInstallation.table definitions) factorRestrictionHelper
      (.cons xs (.cons first .nil))).bind (fun (result : Values (assignment F G) [vector]) =>
      (invoke (RoundsHelperInstallation.table definitions) factorRestrictionHelper
        (.cons (result.get .here) (.cons second .nil))).bind
          (fun (result : Values (assignment F G) [vector]) =>
        (PIR.Process.done (.cons (result.get .here) .nil) :
          PIR.Process (participantInterface F G) (Values (assignment F G) [vector])))) = _
    rw [RoundsProcessInstallation.fix_equation linked bodies]
    congr 1
    funext result
    rw [RoundsProcessInstallation.fix_equation linked bodies]
    have eta : (fun result : Values (assignment F G) [vector] =>
        (PIR.Process.done (.cons (result.get .here) .nil) :
          PIR.Process (participantInterface F G) (Values (assignment F G) [vector]))) =
        PIR.Process.done := by
      funext result
      cases result with | cons result rest => cases rest; rfl
    rw [eta, PIR.Process.bind_done]

/-- The first admitted client consumes the first challenge only. -/
theorem single_equation (xs : List F) (first second : F) :
    invoke (RoundsHelperInstallation.table (G := G) single.payload.definitions) applicationHelper
      (.cons xs (.cons first (.cons second .nil))) =
      RoundsProcessInstallation.fix single.payload.definitions xs first := by
  simpa only [Bool.false_eq_true, ↓reduceIte, PIR.Process.bind_done] using
    application_equation single.payload.linked single_bodies false single_application xs first second

/-- The second admitted client consumes the second challenge in a reached call. -/
theorem double_equation (xs : List F) (first second : F) :
    invoke (RoundsHelperInstallation.table (G := G) double.payload.definitions) applicationHelper
      (.cons xs (.cons first (.cons second .nil))) =
      (RoundsProcessInstallation.fix double.payload.definitions xs first).bind fun result =>
        RoundsProcessInstallation.fix double.payload.definitions (result.get .here) second := by
  simpa only [↓reduceIte] using
    application_equation double.payload.linked double_bodies true double_application xs first second

/-- A stopped first call never reaches the second challenge's restriction. -/
theorem double_empty (first second : F) :
    invoke (RoundsHelperInstallation.table (G := G) double.payload.definitions) applicationHelper
      (.cons [] (.cons first (.cons second .nil))) = .halt .refused := by
  rw [double_equation, RoundsProcessInstallation.fix_all double.payload.linked double_bodies]
  rfl

abbrev ControlField := ZMod 5

example : invoke
    (RoundsHelperInstallation.table (F := ControlField) (G := ControlField) single.payload.definitions)
    applicationHelper (.cons [1, 2, 3, 4] (.cons 0 (.cons 1 .nil))) =
      .done (.cons [1, 2] .nil) := by
  rw [single_equation, RoundsProcessInstallation.fix_all single.payload.linked single_bodies]
  norm_num [Zkc.Polynomial.Multilinear.restrictValues, indexLimit]

example : invoke
    (RoundsHelperInstallation.table (F := ControlField) (G := ControlField) double.payload.definitions)
    applicationHelper (.cons [1, 2, 3, 4] (.cons 0 (.cons 1 .nil))) =
      .done (.cons [2] .nil) := by
  rw [double_equation, RoundsProcessInstallation.fix_all double.payload.linked double_bodies]
  norm_num [Zkc.Polynomial.Multilinear.restrictValues, indexLimit, PIR.Process.bind, Values.get]
  rw [RoundsProcessInstallation.fix_all double.payload.linked double_bodies]
  norm_num [Zkc.Polynomial.Multilinear.restrictValues, indexLimit]

/-- The second call is reached and refuses a singleton produced by the first. -/
example : invoke
    (RoundsHelperInstallation.table (F := ControlField) (G := ControlField) double.payload.definitions)
    applicationHelper (.cons [1, 2] (.cons 0 (.cons 1 .nil))) = .halt .refused := by
  rw [double_equation, RoundsProcessInstallation.fix_all double.payload.linked double_bodies]
  norm_num [Zkc.Polynomial.Multilinear.restrictValues, indexLimit, PIR.Process.bind, Values.get]
  rw [RoundsProcessInstallation.fix_all double.payload.linked double_bodies]
  rfl

example : Participant.owned 0 0
    (invoke (RoundsHelperInstallation.table (F := ControlField) (G := ControlField)
      single.payload.definitions) factorRestrictionHelper)
    (.cons none (.cons (some 1) .nil)) = .halt .incomplete := by
  rw [RoundsProcessInstallation.owned_fix single.payload.linked single_bodies]
  rfl

example : Participant.owned 1 0
    (invoke (RoundsHelperInstallation.table (F := ControlField) (G := ControlField)
      double.payload.definitions) factorRestrictionHelper)
    (.cons none (.cons none .nil)) = .done (.cons none .nil) := by
  rw [RoundsProcessInstallation.owned_fix double.payload.linked double_bodies]
  rfl

end
end ZkcSecurity.Examples.Components.GkrRoundsInstallationControls
