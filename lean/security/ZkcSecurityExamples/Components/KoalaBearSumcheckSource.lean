module

public import ZkcSecurityExamples.Components.KoalaBearSumcheckGenerated.RoundProducer
public import ZkcSecurityExamples.Components.KoalaBearSumcheckGenerated.RoundVerifier
public import ZkcSecurityExamples.Components.KoalaBearSumcheckGenerated.RootProducer
public import ZkcSecurityExamples.Components.KoalaBearSumcheckGenerated.RootVerifier
public import ZkcSecurityExamples.Components.KoalaBearSumcheckRelations
public import ZkcSecurityExamples.Components.KoalaBearSumcheckCarry
public import Zkc.Semantics.ExactRefinement
public import ZkcSecurity.Bindings.Models.KoalaBearModel

@[expose] public section

/-! Actual exported source, admitted by the generic phased reader. The generated
templates fix complete bodies, ordered operands and immutable captures. Only
mathematical embedding results are supplied here, against the actual helper table. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckSource
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open Zkc.Source.Structured.Bindings
open ZkcSecurity.Domains.KoalaBearModel

local instance : DecidableEq (model.Field octicIdentity) := model.fieldDecEq octicIdentity
local instance : DecidableEq Octic := model.fieldDecEq octicIdentity

abbrev base : Ty := .field baseIdentity
abbrev service : Ty := .service randomService
abbrev program := KoalaBearSumcheckGenerated.Inputs.program
abbrev definition := KoalaBearSumcheckGenerated.RoundVerifier.definition
abbrev declaration := definition.signature
abbrev signature := KoalaBearSumcheckGenerated.RoundVerifier.signature
abbrev tables := KoalaBearSumcheckGenerated.RoundVerifier.helperTables model
abbrev verifierTemplate := KoalaBearSumcheckGenerated.RoundVerifier.template
abbrev producerTemplate := KoalaBearSumcheckGenerated.RoundProducer.template

/-- Exact helper body association, independent of its generated name. -/
theorem embedding_body : KoalaBearSumcheckGenerated.Inputs.helper1Body =
    (.letOp (.mark "s0") .nil .nil <|
     .letOp (.fieldEmbed octicIdentity baseIdentity) (.cons .here .nil) .nil <|
     .ret (.cons .here .nil)) := by kernel_rfl

def results : LawResults model signature.laws where
  result := Fin.cases
    (fun args => .cons (model.embed octicIdentity baseIdentity (args.get .here)) .nil)
    (fun entry => entry.elim0)

theorem helper_laws {inputs : List Ty} (input : Values (Component model.Value) inputs) :
    LawsHold tables results input := by
  intro entry
  have zero : entry = ⟨0, by decide⟩ := Fin.eq_zero entry
  subst entry
  intro args _ values same
  cases args with
  | cons a args =>
    cases args
    change some (.cons (model.embed octicIdentity baseIdentity a) .nil) = some values at same
    cases same
    rfl

/-- Root's actual immutable application coordinate. -/
def roundContext : ProtocolContext := ({} : ProtocolContext).enter "label_726f756e64" [0, 1]
theorem round_distinct (role : Nat) (bounded : role < 2) : RosterDistinct roundContext role 2 := by
  intro other otherBound different same
  have roles : role = 0 ∨ role = 1 := by omega
  have others : other = 0 ∨ other = 1 := by omega
  rcases roles with rfl | rfl <;> rcases others with rfl | rfl <;>
    simp_all [roundContext, ProtocolContext.enter, roleSubstitution]

def site (label : String) : String := qualifyProtocolSite roundContext.applicationPrefix label

def source (role : Nat) (ctx : ProtocolContext)
    (input : Values (Component model.Value) declaration.inputs) :=
  invokeProtocol (program.payload.plainProtocolTableOn model) definition.signature ctx (ctx.roles role) input

theorem verifier_binding (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component model.Value) declaration.inputs) :
    source 1 ctx input = verifierTemplate.view model tables [] results (fun entry => entry.elim0) ctx input := by
  rw [source, KoalaBearSumcheckGenerated.RoundVerifier.source_capture]
  exact verifierTemplate.binding model tables [] results (fun entry => entry.elim0) ctx distinct input
    (helper_laws _) (fun entry => entry.elim0)

theorem producer_binding (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component model.Value) declaration.inputs) :
    source 0 ctx input = producerTemplate.view model tables [] results (fun entry => entry.elim0) ctx input := by
  rw [source, KoalaBearSumcheckGenerated.RoundProducer.source_capture]
  exact producerTemplate.binding model tables [] results (fun entry => entry.elim0) ctx distinct input
    (helper_laws _) (fun entry => entry.elim0)


def rawVerifier (priorPoint : List Octic) (claim : Octic) (handle : Nat) :=
  source 1 roundContext (.cons none (.cons none (.cons (some priorPoint)
    (.cons (some claim) (.cons (some handle) .nil)))))

def verifier (priorPoint : List Octic) (claim : Octic) (handle : Nat) :
    PIR.Process (Interface model) (Values (Component model.Value) [extension, extension]) :=
  (rawVerifier priorPoint claim handle).bind (decodeEvaluation priorPoint)

def verifierView (claim : Octic) (handle : Nat) :
    PIR.Process (Interface model) (Values (Component model.Value) [extension, extension]) :=
  .call (.receive extension (site "label_6c6f77_0") 0) fun (low : Octic) =>
  .call (.receive extension (site "label_68696768_0") 0) fun (high : Octic) =>
  if low + high = claim then
    .call (.query (site "label_6368616c6c656e6765") octicIdentity (.cons handle .nil)) fun (challenge : Octic) =>
    .call (.send (ty := extension) (site "label_64656c6976657279_0") 0 challenge) fun _ =>
    .done (.cons (some (low + (high - low) * challenge)) (.cons (some challenge) .nil))
  else .halt .reject

/-- The actual flattened continuation carries the sampled point and scalar. -/
def rawVerifierView (priorPoint : List Octic) (claim : Octic) (handle : Nat) :
    PIR.Process (Interface model) (Values (Component model.Value) declaration.outputs) :=
  .call (.receive extension (site "label_6c6f77_0") 0) fun (low : Octic) =>
  .call (.receive extension (site "label_68696768_0") 0) fun (high : Octic) =>
  if low + high = claim then
    .call (.query (site "label_6368616c6c656e6765") octicIdentity (.cons handle .nil)) fun (r : Octic) =>
    .call (.send (ty := extension) (site "label_64656c6976657279_0") 0 r) fun _ =>
    .done (.cons (some (priorPoint ++ [r])) (.cons (some (low + (high - low) * r)) .nil))
  else .halt .reject

theorem rawVerifier_equation (priorPoint : List Octic) (claim : Octic) (handle : Nat) :
    rawVerifier priorPoint claim handle = rawVerifierView priorPoint claim handle := by
  unfold rawVerifier
  apply (verifier_binding roundContext (round_distinct _ (by decide)) _).trans
  apply PIR.Process.call_congr
  intro low
  change Octic at low
  apply PIR.Process.call_congr
  intro high
  change Octic at high
  apply (PIR.Process.bind_ite _ _ _ _).trans
  change (if low + high = claim then _ else _) = (if low + high = claim then _ else _)
  by_cases boundary : low + high = claim
  · simp only [ite_eq_left boundary]
    apply PIR.Process.call_congr
    intro challenge
    apply PIR.Process.call_congr
    intro delivered
    kernel_rfl
  · simp only [ite_eq_right boundary, PIR.Process.bind]

theorem verifier_equation (priorPoint : List Octic) (claim : Octic) (handle : Nat) :
    verifier priorPoint claim handle = verifierView claim handle := by
  rw [verifier, rawVerifier_equation]
  apply PIR.Process.call_congr
  intro low
  apply PIR.Process.call_congr
  intro high
  apply (PIR.Process.bind_ite _ _ _ _).trans
  split
  · apply PIR.Process.call_congr
    intro challenge
    apply PIR.Process.call_congr
    intro delivered
    exact decodeEvaluation_complete priorPoint challenge _
  · rfl

def producer (a b : Base) :
    PIR.Process (Interface model) (Values (Component model.Value) declaration.outputs) :=
  source 0 roundContext (.cons (some a) (.cons (some b) (.cons none (.cons none (.cons none .nil)))))

def producerView (a b : Base) :
    PIR.Process (Interface model) (Values (Component model.Value) declaration.outputs) :=
  .call (.send (ty := extension) (site "label_6c6f77_0") 1 (ZkcSecurity.Domains.KoalaBear.embed a)) fun _ =>
  .call (.send (ty := extension) (site "label_68696768_0") 1 (ZkcSecurity.Domains.KoalaBear.embed b)) fun _ =>
  .call (.receive extension (site "label_64656c6976657279_0") 1) fun _ =>
  .done (.cons none (.cons none .nil))

theorem producer_equation (a b : Base) : producer a b = producerView a b := by
  exact (producer_binding roundContext (round_distinct _ (by decide)) _).trans (by kernel_rfl)

end ZkcSecurity.Examples.Components.KoalaBearSumcheckSource
