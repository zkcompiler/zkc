module


public import ZkcExamples.Structured.SchnorrInteractiveData
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.NativePrograms.Schnorr

@[expose] public section

/-! Actual original-stage library Interactive Schnorr, including its dormant
formula and relation declaration. The verifier equation is over arbitrary F/G
and independent typed replies. Relation/formula binding is not inferred. -/
namespace ZkcExamples.Structured.SchnorrInteractive
open Zkc.Source Zkc.Source.Structured

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option smartUnfolding false

def program : Program := (check SchnorrInteractiveData.snapshot).toOption.get (by decide +kernel)

theorem admitted : check SchnorrInteractiveData.snapshot = .ok program := by rfl

def imported : Imported SchnorrInteractiveData.snapshot := ⟨program, admitted⟩

theorem exact_subject : imported.program.snapshot = SchnorrInteractiveData.snapshot := imported.exactSubject

theorem retained_relation : program.snapshot.relations.length = 1 := rfl

theorem retained_dormant_helper : program.payload.definitions.length = 1 := rfl

theorem root_outside_helpers : program.payload.definitions.all (·.name != program.snapshot.entry) = true := by
  decide +kernel

abbrev wiring := ZkcExamples.NativePrograms.Schnorr.wiring

/-- The retained formula is an ordinary named Math helper. This handle says
nothing about an authored association with the separate relation declaration. -/
def formula : Helper :=
  ⟨"zkf_6d5ed5928b9bea74d6d7736ea8056c9f06e280ffdc4dbcaf2e00bf4f639c1873", .math,
    [.group groupDomain, .group groupDomain, .field scalarDomain], [.boolean]⟩

theorem formula_present : formula ∈ program.payload.definitions.map CheckedDefinition.helper := by
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Exact full-table equation for the dormant named body, for arbitrary values. -/
theorem formula_equation (base key : G) (secret : F) :
    invoke (program.payload.tables F G).closed formula
      (.cons base (.cons key (.cons secret .nil))) =
        .done (.cons (decide (key = secret • base)) .nil) := by
  rfl

/-- Optional interpretation of the same retained body uses its real operands. -/
theorem formula_component_equation (base key : G) (secret : F) :
    invoke (program.payload.tables F G).components formula
      (.cons (some base) (.cons (some key) (.cons (some secret) .nil))) =
        .done (.cons (some (decide (key = secret • base))) .nil) := by
  rfl

def verifierInputs (base key : G) (challengeService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some base) (.cons (some key) (.cons none (.cons none (.cons (some challengeService) .nil))))

/-- This is the actual checked root's participant process, with the singleton
result unpacked. Unowned secret/service inputs are absent, never fabricated. -/
def process (base key : G) (challengeService : Nat) :
    PIR.Proc (participantInterface F G) (Option Bool) :=
  (program.participant F G 1 (verifierInputs base key challengeService)).bind fun outputs =>
    .done (outputs.get .here)

/-- Every continuation consumes the real reply. This equation contains no
honest-message or equal-role-copy premise. -/
theorem process_equation (base key : G) (challengeService : Nat) :
    process (F := F) base key challengeService =
      (Zkc.Protocols.Schnorr.Common.experiment wiring base key challengeService).interpret
        CommonAdapter.embed := by
  rfl

/-- Positional site retained for the nonce draw in this exact imported subject. -/
def nonceSite : String := "s0"

def proverInputs (base key : G) (secret : F) (nonceService : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some base) (.cons (some key) (.cons (some secret)
    (.cons (some nonceService) (.cons none .nil))))

def proverProcess (base key : G) (secret : F) (nonceService : Nat) :
    PIR.Proc (participantInterface F G) (Option Bool) :=
  (program.participant F G 0 (proverInputs base key secret nonceService)).bind fun outputs =>
    .done (outputs.get .here)

/-- The prover consumes an independent challenge reply and has no verifier
output. Its local key copy is not identified with the verifier's key. -/
theorem prover_equation (base key : G) (secret : F) (nonceService : Nat) :
    proverProcess base key secret nonceService =
      .call (.query nonceSite scalarDomain (.cons nonceService .nil)) (fun (nonce : F) =>
      .call (.send (ty := .group groupDomain) wiring.commitmentSite 1 (nonce • base)) (fun _ =>
      .call (.receive (.field scalarDomain) wiring.deliverySite 1) (fun (challenge : F) =>
      .call (.send (ty := .field scalarDomain) wiring.responseSite 1 (nonce + challenge * secret))
        (fun _ => .done none)))) := by
  rfl

def verifier : Zkc.Protocols.Schnorr.Common.Verifier F G := fun base key service =>
  (process base key service).interpret CommonAdapter.project

theorem verifier_correspondence (base key : G) (service : Nat) :
    verifier (F := F) base key service =
      Zkc.Protocols.Schnorr.Common.experiment wiring base key service := by
  rw [verifier, process_equation, CommonAdapter.project_embed]

theorem contract : Zkc.Protocols.Schnorr.Common.VerifierContract wiring (verifier (F := F) (G := G)) :=
  ⟨fun base key service => ⟨verifier_correspondence base key service⟩⟩

abbrev run := Zkc.Protocols.Schnorr.Common.run (verifier (F := F) (G := G))

theorem accepted_iff (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (challenge : F) :
    (run base key service prover challenge).outcome = .returned (some true) ↔
      prover.response challenge • base = prover.commitment + challenge • key :=
  contract.accepted_iff base key service prover challenge

theorem perfect_completeness (base : G) (secret nonce challenge : F) (service : Nat) :
    (run base (secret • base) service ⟨nonce • base, fun c => nonce + c * secret⟩ challenge).outcome =
      .returned (some true) :=
  contract.perfect_completeness base secret nonce challenge service

theorem special_soundness (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F)
    (distinct : first ≠ second)
    (acceptFirst : (run base key service prover first).outcome = .returned (some true))
    (acceptSecond : (run base key service prover second).outcome = .returned (some true)) :
    ((prover.response first - prover.response second) / (first - second)) • base = key :=
  contract.special_soundness base key service prover first second distinct acceptFirst acceptSecond

end ZkcExamples.Structured.SchnorrInteractive
