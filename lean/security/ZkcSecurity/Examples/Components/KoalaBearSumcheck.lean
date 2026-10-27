module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheckSource
public import ZkcSecurity.Families.Sumcheck.EmbeddingPrefix
public import ZkcSecurity.Families.Sumcheck.Contract
public import Zkc.Construction.DomainTranscript

@[expose] public section

/-! The same degree-one Sumcheck contract, realized with a base table and an
octic challenge prefix. The actual checked verifier has no ghost-table input.
One full Process equation supplies both property consumers. The generated source
is shared with the complete root and its terminal opening. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Domains.KoalaBear (Base Octic q embed)
open ZkcSecurity.Domains.KoalaBearModel (model baseIdentity octicIdentity randomService)
open Zkc.Polynomial Zkc.Polynomial.Multilinear

local instance : DecidableEq (model.Field octicIdentity) := model.fieldDecEq octicIdentity


abbrev State (Frame : Type) := EmbeddingPrefix.State Base Octic Frame
abbrev I := participantInterfaceOn model.toCarriers
variable {Frame : Type}

noncomputable def program : Program I Nat (State Frame) (Message.endpoints Octic) where
  claim state := state.scalar
  receive _ _ :=
    .call (.receive (.field octicIdentity) (KoalaBearSumcheckSource.site "label_6c6f77_0") 0) fun low =>
    .call (.receive (.field octicIdentity) (KoalaBearSumcheckSource.site "label_68696768_0") 0) fun high =>
    .done (some (low, high))
  query handle _ _ := .query (KoalaBearSumcheckSource.site "label_6368616c6c656e6765") octicIdentity (.cons handle .nil)
  challenge _ _ _ reply := reply
  deliver _ _ _ challenge :=
    .call (.send (ty := .field octicIdentity) (KoalaBearSumcheckSource.site "label_64656c6976657279_0") 0 challenge) fun _ => .done ()
  advance _ state message challenge := state.advance message challenge

noncomputable def layout : TableComponent.Layout (program (Frame := Frame)) where
  entries := EmbeddingPrefix.State.entries embed
  shape := EmbeddingPrefix.State.entries_shape embed
  advance _ state message challenge := state.advance_entries embed message challenge
  claim _ _ _ _ := rfl

noncomputable abbrev representation := (layout (Frame := Frame)).representation

/-- Readback changes the logical prefix and keeps the complete caller frame.
Absent returned fields refuse rather than inserting zeros. -/
def readback {n : Nat} (state : State Frame (n + 1))
    (output : Values (Component model.Value) [.field octicIdentity, .field octicIdentity]) :
    PIR.Process I (State Frame n) :=
  match output with
  | .cons (some residual) (.cons (some challenge) .nil) =>
    .done { state.advance (0, 0) challenge with scalar := residual }
  | _ => .halt .incomplete

/-- Complete returned fields have their exact logical interpretation. -/
theorem readback_complete {n : Nat} (state : State Frame (n + 1)) (value r : Octic) :
    readback state (.cons (some value) (.cons (some r) .nil)) =
      .done { state.advance (0, 0) r with scalar := value } := rfl

def actual {n : Nat} (runtime : Nat × State Frame (n + 1)) : PIR.Process I (State Frame n) :=
  (KoalaBearSumcheckSource.verifier runtime.2.point runtime.2.scalar runtime.1).bind (readback runtime.2)

/-- Universally quantified received endpoints, challenge replies and stops.
The ghost base table is used only by the final logical readback. -/
theorem binding {n : Nat} (runtime : Nat × State Frame (n + 1)) :
    actual runtime = program.remaining 1 runtime.1 runtime.2 := by
  rw [actual, KoalaBearSumcheckSource.verifier_equation]
  apply PIR.Process.call_congr
  intro low
  change Octic at low
  apply PIR.Process.call_congr
  intro high
  change Octic at high
  apply (PIR.Process.bind_ite _ _ _ _).trans
  change ((if low + high = runtime.2.scalar then
    .call (.query (KoalaBearSumcheckSource.site "label_6368616c6c656e6765") octicIdentity (.cons runtime.1 .nil)) (fun (r : Octic) =>
    .call (.send (ty := .field octicIdentity) (KoalaBearSumcheckSource.site "label_64656c6976657279_0") 0 r) (fun _ =>
    readback runtime.2 (.cons (some (low + (high - low) * r)) (.cons (some r) .nil))))
    else .halt .reject) : PIR.Process I (State Frame n)) =
    ((if low + high = runtime.2.scalar then
    .call (.query (KoalaBearSumcheckSource.site "label_6368616c6c656e6765") octicIdentity (.cons runtime.1 .nil)) (fun (r : Octic) =>
    .call (.send (ty := .field octicIdentity) (KoalaBearSumcheckSource.site "label_64656c6976657279_0") 0 r) (fun _ =>
    .done (runtime.2.advance (low, high) r))) else .halt .reject) : PIR.Process I (State Frame n))
  by_cases boundary : low + high = runtime.2.scalar
  · simp only [ite_eq_left boundary]
    apply PIR.Process.call_congr
    intro challenge
    apply PIR.Process.call_congr
    intro delivered
    change PIR.Process.done _ = PIR.Process.done _
    apply congrArg (fun state : State Frame n => PIR.Process.done (I := I) state)
    exact EmbeddingPrefix.State.readback_advance runtime.2 low high challenge
  · simp only [ite_eq_right boundary]

/-- Both consumers below pass this exact binding to the unchanged contract. -/
def soundness {E P : Type} {Raw : E → Type}
    (absorb : Zkc.Transcript.Interface I E P Raw) [∀ event, SampleableType (Raw event)]
    (queries : QueryInterface (program (Frame := Frame)) absorb)
    (charge : List E → E → ENNReal)
    (sampling : queries.ConditionalBound representation 1 1 charge) (n : Nat) :
    Zkc.Obligations.SoundnessContract (Contract.component (representation (Frame := Frame)) n 1 actual)
      absorb (ZkcSecurity.Obligations.boundedEscape charge) :=
  Contract.soundness representation Message.endpoints_laws TableReference.laws absorb queries
    charge sampling n 1 actual binding

theorem honest {H O : Type} (handler : PIR.Handler I H O)
    (invariant : Nat → {k : Nat} → Nat → State Frame k → H → Prop)
    (ready : Nat → {k : Nat} → Nat → State Frame (k + 1) → (Octic × Octic) → H → Prop)
    (execution : HonestRunLaws program handler invariant ready)
    (messages : HonestMessageLaw representation ready) (n : Nat)
    (runtime : Nat × State Frame (n + 1)) (state : H)
    (yes : representation.Yes runtime.2) (initial : invariant 1 runtime.1 runtime.2 state) :
    ∃ result final events,
      (actual runtime).run handler state = ⟨.returned result, final, events⟩ ∧
      representation.Yes result ∧ invariant 0 runtime.1 result final :=
  Contract.honest representation Message.endpoints_laws TableReference.laws handler invariant ready
    execution messages n 1 actual binding runtime state yes initial

/-- An initial claim is about the embedded base sum, with no base challenge. -/
theorem initial_yes (values : List Base) (n : Nat) (frame : Frame)
    (shape : values.length = 2 ^ n) :
    representation.Yes (EmbeddingPrefix.State.initial values n (embed values.sum) frame shape) := by
  rw [TableComponent.Layout.yes_iff]
  exact (EmbeddingPrefix.State.initial_sum embed values n _ frame shape).symm

/-- The terminal claim refers to extension-field evaluation of the original
base table. The table is supplied as a mathematical readback witness only. -/
theorem terminal_yes_iff (state : State Frame 0)
    (table : Table Base (0 + state.point.length))
    (decoded : ofList? (0 + state.point.length) state.original = some table) :
    representation.Yes state ↔ state.scalar =
      extension (0 + state.point.length) (Embedding.table embed table)
        (coordinates (0 + state.point.length) state.point) := by
  rw [TableComponent.Layout.yes_iff]
  change state.scalar = (state.entries embed).sum ↔ _
  rw [EmbeddingPrefix.State.terminal_total embed state table decoded]

/-- Frame preservation has no truth/falsity premise. -/
theorem preserves_frame (interaction : PIR.Interaction I) (n : Nat)
    (runtime : Nat × State Frame (n + 1)) (phase : interaction.Phase) :
    PIR.Boundary.Returns interaction (fun result _ => result.frame = runtime.2.frame)
      (actual runtime) phase :=
  Contract.preserves (program := program (Frame := Frame)) interaction
    (fun {k} (state : State Frame k) => state.frame = runtime.2.frame)
    (fun _ _ same _ _ => same) n 1 actual binding runtime phase rfl

end ZkcSecurity.Examples.Components.KoalaBearSumcheck
