module

public import ZkcExamples.Structured.SchnorrInteractive
public import ZkcExamples.Structured.SchnorrHelpersData
public import ZkcExamples.Structured.SchnorrReorderedData
public import ZkcExamples.Structured.SchnorrEarlyChallengeData

@[expose] public section

/-! Actual original-stage source forms retain their named bodies. The shared
contract follows from open-process equations. Early challenge is admitted as a
different program, and its changed first action refutes that contract equation. -/
namespace ZkcExamples.Structured.SchnorrVariants
open Zkc.Source Zkc.Source.Structured

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option smartUnfolding false

inductive Form where
  | original | helpers | reordered

def helpersProgram : Program := (check SchnorrHelpersData.snapshot).toOption.get (by decide +kernel)
def reorderedProgram : Program := (check SchnorrReorderedData.snapshot).toOption.get (by decide +kernel)
def earlyProgram : Program := (check SchnorrEarlyChallengeData.snapshot).toOption.get (by decide +kernel)

theorem helpers_admitted : check SchnorrHelpersData.snapshot = .ok helpersProgram := rfl
theorem reordered_admitted : check SchnorrReorderedData.snapshot = .ok reorderedProgram := rfl
theorem early_admitted : check SchnorrEarlyChallengeData.snapshot = .ok earlyProgram := rfl

def helpersImported : Imported SchnorrHelpersData.snapshot := ⟨helpersProgram, helpers_admitted⟩
def reorderedImported : Imported SchnorrReorderedData.snapshot := ⟨reorderedProgram, reordered_admitted⟩
def earlyImported : Imported SchnorrEarlyChallengeData.snapshot := ⟨earlyProgram, early_admitted⟩

theorem helpers_exact_subject : helpersProgram.snapshot = SchnorrHelpersData.snapshot := rfl
theorem reordered_exact_subject : reorderedProgram.snapshot = SchnorrReorderedData.snapshot := rfl
theorem early_exact_subject : earlyProgram.snapshot = SchnorrEarlyChallengeData.snapshot := rfl

def program : Form → Program
  | .original => SchnorrInteractive.program
  | .helpers => helpersProgram
  | .reordered => reorderedProgram

abbrev wiring := SchnorrInteractive.wiring

def responseHelper : Helper :=
  ⟨"s13h7363686e6f72725f666f726d738h726573706f6e7365", .math,
    [.field scalarDomain, .field scalarDomain, .field scalarDomain], [.field scalarDomain]⟩

def equationHelper : Helper :=
  ⟨"s13h7363686e6f72725f666f726d738h6571756174696f6e", .math,
    [.group groupDomain, .group groupDomain, .group groupDomain,
      .field scalarDomain, .field scalarDomain], [.boolean]⟩

theorem retained_named_calls : helpersProgram.payload.entry.helpers = [responseHelper, equationHelper] := rfl

theorem retained_helper_count : helpersProgram.payload.definitions.length = 2 := rfl

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Full-table named closure equations quantify over independent actual values. -/
theorem response_equation (nonce challenge secret : F) :
    invoke (helpersProgram.payload.tables F G).closed responseHelper
      (.cons nonce (.cons challenge (.cons secret .nil))) =
        .done (.cons (nonce + challenge * secret) .nil) := rfl

theorem equation_equation (base key commitment : G) (challenge answer : F) :
    invoke (helpersProgram.payload.tables F G).closed equationHelper
      (.cons base (.cons key (.cons commitment (.cons challenge (.cons answer .nil))))) =
        .done (.cons (decide (answer • base = commitment + challenge • key)) .nil) := rfl

theorem response_component_equation (nonce challenge secret : F) :
    invoke (helpersProgram.payload.tables F G).components responseHelper
      (.cons (some nonce) (.cons (some challenge) (.cons (some secret) .nil))) =
        .done (.cons (some (nonce + challenge * secret)) .nil) := rfl

def helpersProcess (base key : G) (service : Nat) :
    PIR.Proc (participantInterface F G) (Option Bool) :=
  (helpersProgram.participant F G 1 (SchnorrInteractive.verifierInputs base key service)).bind
    fun values => .done (values.get .here)

def reorderedProcess (base key : G) (service : Nat) :
    PIR.Proc (participantInterface F G) (Option Bool) :=
  (reorderedProgram.participant F G 1 (SchnorrInteractive.verifierInputs base key service)).bind
    fun values => .done (values.get .here)

def process : Form → G → G → Nat → PIR.Proc (participantInterface F G) (Option Bool)
  | .original => SchnorrInteractive.process
  | .helpers => helpersProcess
  | .reordered => reorderedProcess

theorem helpers_equation (base key : G) (service : Nat) :
    process (F := F) .helpers base key service =
      (Zkc.Protocols.Schnorr.Common.experiment wiring base key service).interpret CommonAdapter.embed := rfl

theorem reordered_equation (base key : G) (service : Nat) :
    process (F := F) .reordered base key service =
      (Zkc.Protocols.Schnorr.Common.experiment wiring base key service).interpret CommonAdapter.embed := by
  apply PIR.Proc.call_congr
  intro commitment
  apply PIR.Proc.call_congr
  intro challenge
  change F at challenge
  apply PIR.Proc.call_congr
  intro acknowledgement
  apply PIR.Proc.call_congr
  intro answer
  change F at answer
  change PIR.Proc.done (some (decide (answer • base = challenge • key + commitment))) =
    PIR.Proc.done (some (decide (answer • base = commitment + challenge • key)))
  rw [add_comm (challenge • key) commitment]

def verifier (form : Form) : Zkc.Protocols.Schnorr.Common.Verifier F G := fun base key service =>
  (process form base key service).interpret CommonAdapter.project

theorem correspondence (form : Form) (base key : G) (service : Nat) :
    verifier (F := F) form base key service = Zkc.Protocols.Schnorr.Common.experiment wiring base key service := by
  have equation : process (F := F) form base key service =
      (Zkc.Protocols.Schnorr.Common.experiment wiring base key service).interpret CommonAdapter.embed := by
    cases form with
    | original => exact SchnorrInteractive.process_equation base key service
    | helpers => exact helpers_equation base key service
    | reordered => exact reordered_equation base key service
  rw [verifier, equation, CommonAdapter.project_embed]

theorem contract (form : Form) :
    Zkc.Protocols.Schnorr.Common.VerifierContract wiring (verifier (F := F) (G := G) form) :=
  ⟨fun base key service => ⟨correspondence form base key service⟩⟩

abbrev run (form : Form) := Zkc.Protocols.Schnorr.Common.run (verifier (F := F) (G := G) form)

theorem perfect_completeness (form : Form) (base : G) (secret nonce challenge : F) (service : Nat) :
    (run form base (secret • base) service ⟨nonce • base, fun c => nonce + c * secret⟩ challenge).outcome =
      .returned (some true) :=
  (contract form).perfect_completeness base secret nonce challenge service

theorem special_soundness (form : Form) (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F) (distinct : first ≠ second)
    (acceptFirst : (run form base key service prover first).outcome = .returned (some true))
    (acceptSecond : (run form base key service prover second).outcome = .returned (some true)) :
    ((prover.response first - prover.response second) / (first - second)) • base = key :=
  (contract form).special_soundness base key service prover first second distinct acceptFirst acceptSecond

def earlyVerifier (base key : G) (service : Nat) :
    PIR.Proc (CommonAdapter.commonInterface F G) (Option Bool) :=
  ((earlyProgram.participant F G 1 (SchnorrInteractive.verifierInputs base key service)).bind
    fun values => .done (values.get .here)).interpret CommonAdapter.project

/-- The actual counterexample's query is reached before the commitment receive. -/
theorem early_equation (base key : G) (service : Nat) :
    earlyVerifier (F := F) base key service =
      .call (.query wiring.challengeSite scalarDomain (.cons service .nil)) fun (challenge : F) =>
      .call (.receive (.group groupDomain) wiring.commitmentSite 0) fun (commitment : G) =>
      .call (.send (ty := .field scalarDomain) wiring.deliverySite 0 challenge) fun _ =>
      .call (.receive (.field scalarDomain) wiring.responseSite 0) fun (answer : F) =>
      .done (some (decide (answer • base = commitment + challenge • key))) := rfl

private def beginsWithReceive {A : Type} : PIR.Proc (CommonAdapter.commonInterface F G) A → Bool
  | .call (.receive ..) _ => true
  | _ => false

theorem early_not_corresponding (base key : G) (service : Nat) :
    earlyVerifier (F := F) base key service ≠ Zkc.Protocols.Schnorr.Common.experiment wiring base key service := by
  intro same
  have first := congrArg beginsWithReceive same
  change false = true at first
  exact Bool.noConfusion first

theorem early_no_contract :
    ¬ Zkc.Protocols.Schnorr.Common.VerifierContract wiring (earlyVerifier (F := F) (G := G)) := by
  intro claimed
  exact early_not_corresponding (F := F) (0 : G) 0 0 (claimed.realizes 0 0 0).process_eq

end ZkcExamples.Structured.SchnorrVariants
