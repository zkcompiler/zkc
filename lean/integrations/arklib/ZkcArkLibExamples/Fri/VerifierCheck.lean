module

public import ZkcArkLibExamples.Fri.VerifierQueries
public import ZkcExamples.Structured.FriCheckAdmission

@[expose] public section

/-! A returned Check invocation has passed the source admission guards,
checked all eight sampled positions and returned the corresponding cells.
Earlier stops bypass all later queries. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.VerifierCheck
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceBodies FriSourceViews
open FriCheckPositions (querySite queryOccurrence queryOnSpine)
open VerifierPath (State charged)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open Std.Do.Internal (Ensures)
variable {Aux E : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

private theorem body_split (context : ProtocolContext)
    (inputs : Values (FriBinding.Value model) protocol3Signature.inputs) :
    let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
    protocol3Body.denote meaning inputs.get =
      (FriCheckAdmission.admissionBody.denote meaning inputs.get).bind fun live ↦
        querySite.region.denote meaning live.get := by
  dsimp only
  rw [← FriCheckAdmission.admissionBody_exact]
  exact queryOccurrence.denote_prefix ((verifierAlgebra model).meaning (verifierTable model) context 1) queryOnSpine inputs.get

private theorem visibleScope (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (separate : 1 ≠ context.roles 0) (scopes : List (List Nat))
    (used : ∀ s ∈ scopes, s = [0] ∨ s = [1] ∨ s = [0, 1]) :
    ∀ s ∈ scopes, (s.map context.roles).contains 1 = s.contains 1 := by
  intro s member
  rcases used s member with rfl | rfl | rfl <;> simp [receiver, separate]

/-- The hypothesis about words concerns actual immutable publications.
No loop environment, operand selection, or read schedule is supplied. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (handles : FriBindingExecution.Handles) (layers : handles.layers.length = 3) (folds : handles.folds.length = 3)
    (shift : Octic) (nonzero : shift ≠ 0) (positions : Fin 8 → Fin 32) (word : Fin 32 → Octic)
    (beta : Octic) (rest : Layers Octic 4 2) (one : rest.coefficients.length = 1)
    (state : State Aux) (role : state.oracle.self = 1)
    (pub : VerifierQueries.Publication state.oracle handles.initial handles.layers handles.folds word beta shift rest) :
    let inputs := FriCheckAdmission.arguments (model := model) handles shift rest.coefficients (List.ofFn positions)
    let cells := (List.finRange 8).map fun i ↦ word (positions i)
    let output := Values.cons (OracleProtocol.concrete model .boolean true) (VerifierQueries.packed cells)
    Ensures (fun record ↦ ∀ returned, record.outcome = .returned returned →
      Phases.accepts RetainedDomain.root 0 (.fold word beta rest) shift positions = true ∧
      returned = output ∧ record.state.oracle = charged state.oracle 96)
      ((invokeProtocol (verifierTable model) protocol3Signature context 1 inputs).runM
        (VerifierPath.handler network choose) state) := by
  dsimp only
  let inputs := FriCheckAdmission.arguments (model := model) handles shift rest.coefficients (List.ofFn positions)
  let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
  let cells := (List.finRange 8).map fun i ↦ word (positions i)
  let output : Values (FriBinding.Value model) protocol3Signature.outputs :=
    .cons (OracleProtocol.concrete model .boolean true) (VerifierQueries.packed cells)
  let accepts := Phases.accepts RetainedDomain.root 0 (.fold word beta rest) shift positions
  let good := fun (record : PIR.Execution (State Aux) (OracleProtocol.Event E) (Values (FriBinding.Value model) protocol3Signature.outputs)) ↦
    ∀ returned, record.outcome = .returned returned → accepts = true ∧ returned = output ∧ record.state.oracle = charged state.oracle 96
  have fits : rest.coefficients.length < indexLimit := one ▸ (by decide)
  have admission := FriCheckAdmission.installed checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
    (PublishedWords.publishM choose) state.oracle context receiver separate role handles shift rest.coefficients
    (List.ofFn positions) List.length_ofFn layers folds one pub.initial.registry pub.initial.lookup
    pub.initial.visible pub.initial.registryRows state rfl
  have raw : Ensures good ((protocol3Body.denote meaning inputs.get).runM (VerifierPath.handler network choose) state) := by
    rw [body_split]
    refine (congrArg (fun run ↦ Ensures good run) (PIR.runM_bind (VerifierPath.handler network choose)
      (FriCheckAdmission.admissionBody.denote meaning inputs.get) (fun live ↦ querySite.region.denote meaning live.get) state)).mpr ?_
    apply admission.bind
    rintro ⟨out, current, events⟩ ⟨same, projected⟩
    cases out with
    | stopped why => exact Zkc.MonadicPostcondition.pure _ _ (by intro _ eq; cases eq)
    | returned live =>
      have selection := projected live rfl
      have chosen : Operands.eval live.get querySite.operands = .cons (OracleProtocol.concrete model .index 8)
          ((VerifierQueries.packed []).append (VerifierQueries.captures handles.initial handles.layers handles.folds rest shift positions)) := by
        refine selection.trans ?_
        unfold FriCheckAdmission.selected VerifierQueries.captures VerifierQueries.samples
        rw [List.map_ofFn]
        rfl
      have checked := VerifierQueries.installed network choose (n := 4) (r := 2) (by decide) (by decide +kernel)
        (by decide +kernel) shift nonzero positions word beta rest fits 0 one context receiver live.get
        handles.initial handles.layers handles.folds chosen current (same ▸ role) (same ▸ pub)
      apply Zkc.MonadicPostcondition.map checked _
      rintro ⟨outcome, after, trace⟩ result returned returns
      change outcome = .returned returned at returns
      change (if accepts then outcome = .returned output ∧ after.oracle = charged current.oracle 96 else outcome = .stopped .reject)
        ∨ outcome = .stopped .refused at result
      rw [same] at result
      cases pass : accepts <;> simp [pass, returns] at result
      exact ⟨rfl, PIR.Outcome.returned.inj result.1, result.2⟩
  have inputMask : maskValues 1 (context.mapScopes protocol3Signature.inputScopes) inputs = inputs :=
    (maskValues_mapScopes context 1 1 _ inputs (visibleScope context receiver separate _ (by decide +kernel))).trans rfl
  have invoke := (verifierAlgebra model).invokePresented unit.protocolsLinked protocol3Definition protocol3_member
    context 1 inputs (protocol3Body.denote meaning inputs.get)
      (congrArg (fun v : Values (FriBinding.Value model) protocol3Signature.inputs ↦ protocol3Body.denote meaning v.get) inputMask)
  change Ensures good ((invokeProtocol (verifierTable model) protocol3Signature context 1 inputs).runM (VerifierPath.handler network choose) state)
  refine (congrArg (fun p : PIR.Process (OracleProtocol.Interface model) (Values (FriBinding.Value model) protocol3Signature.outputs) ↦
    Ensures good (p.runM (VerifierPath.handler network choose) state)) invoke).mpr ?_
  refine (congrArg (fun run ↦ Ensures good run) (PIR.runM_bind (VerifierPath.handler network choose)
    (protocol3Body.denote meaning inputs.get) (fun out ↦ .done (maskValues 1 (context.mapScopes protocol3Signature.outputScopes) out)) state)).mpr ?_
  apply raw.bind
  rintro ⟨out, current, events⟩ post
  cases out with
  | stopped why => exact Zkc.MonadicPostcondition.pure _ _ (by intro _ eq; cases eq)
  | returned actual =>
    obtain ⟨pass, rfl, store⟩ := post actual rfl
    have masked := (maskValues_mapScopes context 1 1 protocol3Signature.outputScopes output
      (visibleScope context receiver separate _ (by decide +kernel))).trans (show maskValues 1 protocol3Signature.outputScopes output = output from rfl)
    simp only [PIR.Execution.followM, PIR.Process.runM, pure_bind, List.append_nil]
    apply Zkc.MonadicPostcondition.pure
    intro value eq
    change PIR.Outcome.returned (maskValues 1 (context.mapScopes protocol3Signature.outputScopes) output) = .returned value at eq
    exact ⟨pass, (PIR.Outcome.returned.inj eq).symm.trans masked, store⟩

end ZkcSecurity.ArkLib.Fri.VerifierCheck
