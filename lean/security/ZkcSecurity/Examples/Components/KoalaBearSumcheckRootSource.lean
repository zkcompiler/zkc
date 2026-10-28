module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheckSource

@[expose] public section

/-! The actual root template calls the admitted Round and performs a terminal
opening against its public two-entry table. Callee routing is a nominal-model
instance of the existing template rule, retaining complete optional ABIs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckSource
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open Zkc.Source.Structured.Bindings
open ZkcSecurity.Domains.KoalaBearModel
open ZkcSecurity.Domains.KoalaBear (embed)

local instance : DecidableEq (model.Field baseIdentity) := model.fieldDecEq baseIdentity

local instance : DecidableEq (model.Field octicIdentity) := model.fieldDecEq octicIdentity
local instance : DecidableEq Octic := model.fieldDecEq octicIdentity

/-- A reusable nominal endpoint adapter: the actual return mask is idempotent.
No field uniformization, successful-run premise or missing-value default. -/
theorem nominal_output_mask (selected : CheckedProtocol) (domain : DomainModel)
    (helpers : Tables domain) (capture : ProtocolTable domain.Value (Interface domain))
    (ctx : ProtocolContext) (self : Nat)
    (input : Values (Component domain.Value) selected.inputs) :
    selected.denoteWithOn domain (.silent _) (participantActionsOn domain.toCarriers)
      helpers capture .silent ctx self input =
    (selected.denoteWithOn domain (.silent _) (participantActionsOn domain.toCarriers)
      helpers capture .silent ctx self input).bind
      (fun out => .done (maskValues self (ctx.mapScopes selected.outputScopes) out)) := by
  unfold CheckedProtocol.denoteWithOn
  rw [PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext out
  exact congrArg PIR.Process.done (maskValues_idempotent self (ctx.mapScopes selected.outputScopes) out).symm

def calleeKeys (role : Nat) : List CalleeKey :=
  [⟨declaration, role, optionalPattern declaration.inputs, []⟩]

def calleeProcesses (role : Nat) : CalleeProcesses model (calleeKeys role) :=
  Fin.cases (fun ctx binders =>
    source role ctx ((optionalPattern declaration.inputs).environment model binders))
    (fun entry => entry.elim0)

/-- Exact captured lookup and mask laws close the template's callee obligation.
This adapter works at arbitrary application coordinates and optional inputs. -/
theorem callee_laws (role : Nat) (capture : ProtocolTable model.Value (Interface model))
    (lookup : invokeProtocol capture declaration =
      invokeProtocol (program.payload.plainProtocolTableOn model) declaration)
    {inputs : List Ty} (input : Values (Component model.Value) inputs) :
    CalleesHold capture (calleeProcesses role) input := by
  intro entry ctx binders others pinned distinct
  have zero : entry = ⟨0, by simp [calleeKeys]⟩ := Fin.eq_zero entry
  subst entry
  change Binders model (optionalPattern declaration.inputs).scope at binders
  change Values (Component model.Value) (optionalPattern declaration.inputs).absentTypes at others
  change RosterDistinct ctx role 2 at distinct
  change invokeProtocol capture declaration ctx (ctx.roles role)
      ((optionalPattern declaration.inputs).fill model binders others) =
    (source role ctx ((optionalPattern declaration.inputs).environment model binders)).bind
      (fun out => .done (staticMask role out declaration.outputScopes
        (Operands.identity declaration.outputs)))
  rw [optional_fill, lookup]
  have bounded : ∀ scope ∈ declaration.outputScopes, ∀ other ∈ scope, other < 2 := by
    change ∀ scope ∈ ([[1], [1]] : List (List Nat)), ∀ other ∈ scope, other < 2
    simp
  have masks (out : Values (Component model.Value) declaration.outputs) :=
    mask_context ctx role 2 distinct declaration.outputScopes bounded out
  unfold source
  rw [KoalaBearSumcheckGenerated.RoundVerifier.source_capture]
  conv_rhs => arg 2; ext out; rw [staticMask_identity, ← masks]
  exact nominal_output_mask definition model tables [] ctx (ctx.roles role) _

theorem root_capture_lookup :
    invokeProtocol (KoalaBearSumcheckGenerated.RootVerifier.capture model) declaration =
      invokeProtocol (program.payload.plainProtocolTableOn model) declaration := by
  rw [KoalaBearSumcheckGenerated.RoundVerifier.source_capture]
  kernel_rfl

def rootSource (role : Nat)
    (input : Values (Component model.Value) KoalaBearSumcheckGenerated.RootVerifier.definition.inputs) :=
  invokeProtocol (program.payload.plainProtocolTableOn model)
    KoalaBearSumcheckGenerated.RootVerifier.definition.signature {} role input

/-- Complete total input policy, including all missing-field branches. -/
theorem root_verifier_binding
    (input : Values (Component model.Value) KoalaBearSumcheckGenerated.RootVerifier.definition.inputs) :
    rootSource 1 input = KoalaBearSumcheckGenerated.RootVerifier.template.view model tables
      (KoalaBearSumcheckGenerated.RootVerifier.capture model) results (calleeProcesses 1) {} input := by
  rw [rootSource, KoalaBearSumcheckGenerated.RootVerifier.source_capture]
  exact KoalaBearSumcheckGenerated.RootVerifier.template.binding model tables (KoalaBearSumcheckGenerated.RootVerifier.capture model)
    results (calleeProcesses 1) {} (RosterDistinct.root 1 2) input
    (helper_laws _) (callee_laws 1 _ root_capture_lookup _)

theorem root_producer_binding
    (input : Values (Component model.Value) KoalaBearSumcheckGenerated.RootVerifier.definition.inputs) :
    rootSource 0 input = KoalaBearSumcheckGenerated.RootProducer.template.view model tables
      (KoalaBearSumcheckGenerated.RootProducer.capture model) results (calleeProcesses 0) {} input := by
  rw [rootSource, KoalaBearSumcheckGenerated.RootProducer.source_capture]
  exact KoalaBearSumcheckGenerated.RootProducer.template.binding model tables (KoalaBearSumcheckGenerated.RootProducer.capture model)
    results (calleeProcesses 0) {} (RosterDistinct.root 0 2) input
    (helper_laws _) (callee_laws 0 _ root_capture_lookup _)

/-- The output decoder is strict about both octic values. Missing results yield
an absent decision, which never counts as acceptance. -/
def terminal (a b : Base) (out : Values (Component model.Value) [extension, extension]) :
    PIR.Process (Interface model) (Values (Component model.Value) [.boolean]) :=
  match out.get (.there .here) with
  | none => .done (.cons none .nil)
  | some point =>
    match out.get .here with
    | none => .done (.cons none .nil)
    | some residual => by
      change Octic at residual point
      exact .done (.cons (some (decide (residual = embed a + (embed b - embed a) * point))) .nil)

theorem terminal_complete (a b : Base) (residual point : Octic) :
    terminal a b (.cons (some residual) (.cons (some point) .nil)) =
      .done (.cons (some (decide (residual = embed a + (embed b - embed a) * point))) .nil) := rfl

def rootVerifier (a b claim : Base) (handle : Nat) :=
  rootSource 1 (.cons (some a) (.cons (some b) (.cons (some claim) (.cons (some handle) .nil))))

def rootProducer (a b : Base) :=
  rootSource 0 (.cons (some a) (.cons (some b) (.cons none (.cons none .nil))))

/-- The root invokes the actual local terminal helper on the sealed carry. -/
def terminalCarry (a b : Base) (out : Values (Component model.Value) declaration.outputs) :=
  Participant.owned 1 1 (invoke tables.closed
    ⟨"s14h6d697865645f73756d636865636b5h636865636b", .local,
      [base, base, .vector octicIdentity, extension], [.boolean]⟩)
    (.cons (some a) (.cons (some b) out))

theorem terminalCarry_complete (a b : Base) (point value : Octic) :
    terminalCarry a b (.cons (some [point]) (.cons (some value) .nil)) =
      .done (.cons (some (decide (value = embed a + (embed b - embed a) * point))) .nil) := by
  have evaluated : terminalCarry a b (.cons (some [point]) (.cons (some value) .nil)) =
      .done (.cons (some (decide (value = embed a + (embed b - embed a) * (0 + point)))) .nil) := by
    kernel_rfl
  simpa only [zero_add] using evaluated

theorem root_verifier_equation (a b claim : Base) (handle : Nat) :
    rootVerifier a b claim handle = (verifier [] (embed claim) handle).bind (terminal a b) := by
  unfold rootVerifier
  rw [root_verifier_binding]
  have presented : KoalaBearSumcheckGenerated.RootVerifier.template.view model tables
      (KoalaBearSumcheckGenerated.RootVerifier.capture model) results (calleeProcesses 1) {}
      (.cons (some a) (.cons (some b) (.cons (some claim) (.cons (some handle) .nil)))) =
    (source 1 roundContext (.cons (some a) (.cons (some b) (.cons (some [])
      (.cons (some (embed claim)) (.cons (some handle) .nil)))))).bind
      (fun out => (terminalCarry a b out).bind (fun result => .done (maskValues 1 [[1]] result))) := by
    have exposed : KoalaBearSumcheckGenerated.RootVerifier.template.view model tables
        (KoalaBearSumcheckGenerated.RootVerifier.capture model) results (calleeProcesses 1) {}
        (.cons (some a) (.cons (some b) (.cons (some claim) (.cons (some handle) .nil)))) =
      ((source 1 roundContext (.cons (some a) (.cons (some b) (.cons (some [])
        (.cons (some (embed claim)) (.cons (some handle) .nil)))))).bind fun out =>
          (terminalCarry a b (.cons (out.get .here) (.cons (out.get (.there .here)) .nil))).bind
            (fun result => .done (.cons (result.get .here) .nil))).bind
          (fun result => .done (maskValues 1 [[1]] result)) := by
      kernel_rfl
    rw [exposed]
    rw [PIR.Process.bind_assoc]
    apply congrArg (PIR.Process.bind (source 1 roundContext
      (.cons (some a) (.cons (some b) (.cons (some [])
        (.cons (some (embed claim)) (.cons (some handle) .nil)))))))
    funext out
    cases out with
    | cons point rest =>
      cases rest with
      | cons value rest =>
        cases rest
        change ((terminalCarry a b (.cons point (.cons value .nil))).bind _).bind _ = _
        rw [PIR.Process.bind_assoc]
        apply congrArg (PIR.Process.bind (terminalCarry a b (.cons point (.cons value .nil))))
        funext result
        cases result with
        | cons decision rest => cases rest; rfl
  rw [presented]
  have same : source 1 roundContext (.cons (some a) (.cons (some b) (.cons (some [])
      (.cons (some (embed claim)) (.cons (some handle) .nil))))) = rawVerifier [] (embed claim) handle := by
    unfold rawVerifier
    rw [verifier_binding roundContext (round_distinct _ (by decide)),
      verifier_binding roundContext (round_distinct _ (by decide))]
    kernel_rfl
  rw [same, rawVerifier_equation, verifier_equation]
  apply PIR.Process.call_congr
  intro low
  change Octic at low
  apply PIR.Process.call_congr
  intro high
  change Octic at high
  by_cases boundary : low + high = embed claim
  · simp only [boundary, ↓reduceIte, PIR.Process.bind]
    apply PIR.Process.call_congr
    intro r
    change Octic at r
    apply PIR.Process.call_congr
    intro delivered
    change ((terminalCarry a b (.cons (some [r]) (.cons (some (low + (high - low) * r)) .nil))).bind
      (fun result => .done (maskValues 1 [[1]] result))) = _
    rw [terminalCarry_complete]
    rfl
  · simp only [boundary, ↓reduceIte, PIR.Process.bind]

theorem root_producer_equation (a b : Base) :
    rootProducer a b = (producer a b).bind (fun _ => .done (.cons none .nil)) := by
  unfold rootProducer
  apply (root_producer_binding _).trans
  kernel_rfl

/-- The actual target selects V's ordered inputs and the Boolean root output;
the selected native relation points to the helper whose body is evaluated below. -/
theorem target_association :
    ((program.snapshot.contracts.find? (fun contract =>
      contract.owner == KoalaBearSumcheckGenerated.RootVerifier.definition.name)).map (·.clauses) =
      some [⟨.target, "sum",
        ⟨(program.snapshot.relations.get ⟨0, by decide⟩).name,
          [⟨.input, 0, "role00000001", false⟩, ⟨.input, 1, "role00000001", false⟩, ⟨.input, 2, "role00000001", false⟩]⟩,
        none, some ⟨.output, 0, "role00000001", false⟩⟩]) ∧
    (program.snapshot.relations.get ⟨0, by decide⟩).formula =
      some KoalaBearSumcheckGenerated.Inputs.helper0Helper.name := by
  constructor <;> kernel_rfl

/-- The native target formula has this exact meaning on actual V inputs. -/
def sumRelation (a b claim : Base) : Prop := claim = a + b

theorem sumRelation_embedded (a b claim : Base) :
    sumRelation a b claim ↔ embed claim = ([a, b].map embed).sum := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← map_add]
  exact embed.injective.eq_iff.symm

theorem source_relation (a b claim : Base) :
    invoke tables.closed KoalaBearSumcheckGenerated.Inputs.helper0Helper
      (.cons a (.cons b (.cons claim .nil))) =
    .done (.cons (decide (claim = a + b)) .nil) := by
  kernel_rfl

end ZkcSecurity.Examples.Components.KoalaBearSumcheckSource
