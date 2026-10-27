module

public import Zkc.Executable.DomainNativeByteTransport
public import ZkcExamples.Executable.SumcheckHelpers
public import ZkcExamples.Executable.SchnorrProofProgramData
public import ZkcExamples.Construction.SchnorrArtifact
public import Zkc.Executable.Installed
public import ZkcExamples.Executable.SumcheckProofProgramData
public import ZkcExamples.Construction.SumcheckArtifact

@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
namespace Tests.DomainNativeScope
open Zkc.Construction Zkc.Executable Zkc.Executable.DomainVM
open Zkc.Source

abbrev entryScope := nativeEntryScope

abbrev schnorrValidator := ZkcExamples.Executable.SchnorrProofProgramData.validator
abbrev sumcheckValidator := ZkcExamples.Executable.SumcheckProofProgramData.validator
def schnorrLowered : Lowered :=
  (checkLowering installed ZkcExamples.Construction.SchnorrProof.participant schnorrValidator).toOption.get (by decide +kernel)
def sumcheckLowered : Lowered :=
  (checkLowering installed ZkcExamples.Construction.SumcheckProof.participant sumcheckValidator).toOption.get (by decide +kernel)

theorem schnorr_checked :
    (checkNativeCode ZkcExamples.Construction.SchnorrProof.program
      ZkcExamples.Construction.SchnorrProof.context
      schnorrLowered.code
      (entryScope schnorrValidator)).isSome = true := by
  decide +kernel

theorem sumcheck_checked :
    (checkNativeCode ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context
      sumcheckLowered.code
      (entryScope sumcheckValidator)).isSome = true := by
  decide +kernel

def schnorrFinal : NativeScope :=
  (checkNativeCode ZkcExamples.Construction.SchnorrProof.program
    ZkcExamples.Construction.SchnorrProof.context schnorrLowered.code
    (entryScope schnorrValidator)).get schnorr_checked

def sumcheckFinal : NativeScope :=
  (checkNativeCode ZkcExamples.Construction.SumcheckProof.program
    ZkcExamples.Construction.SumcheckProof.context sumcheckLowered.code
    (entryScope sumcheckValidator)).get sumcheck_checked

theorem schnorr_admitted :
    checkNativeLowering ZkcExamples.Construction.SchnorrProof.program
      ZkcExamples.Construction.SchnorrProof.context installed
      ZkcExamples.Construction.SchnorrProof.participant schnorrValidator =
      .ok (schnorrLowered, schnorrFinal) := by kernel_rfl

theorem sumcheck_admitted :
    checkNativeLowering ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context installed
      ZkcExamples.Construction.SumcheckProof.participant sumcheckValidator =
      .ok (sumcheckLowered, sumcheckFinal) := by kernel_rfl

theorem sumcheck_has_loop :
    sumcheckLowered.plan.any (fun | .loop .. => true | _ => false) = true := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

-- Both controls instantiate the generic semantic certificate on actual
-- lowered artifacts and arbitrary admitted inputs, not a desired equation.
theorem schnorr_all_replies (data : List (Value F G)) (initial : History F G)
    (bytes : List UInt8) (key : Origin → Origin) (admitted : schnorrValidator.admits data = true) :
    ∃ nominal, Uniform.DomainAdapter.embedValues data = some nominal ∧
      Reached ZkcExamples.Construction.SchnorrProof.context.suite key initial data
        (entryScope schnorrValidator).reading (Zkc.Executable.initial schnorrValidator data initial bytes)
        (nominal ++ [.transcript ZkcExamples.Construction.SchnorrProof.context.suite []])
        (data ++ [.transcript initial]) ∧
      PIR.Yields schnorrFinal.Holds
        (Domain.evaluate (Structured.ringModel F G) ZkcExamples.Construction.SchnorrProof.program
          ZkcExamples.Construction.SchnorrProof.context (Code.instructions schnorrLowered.code)
          (nominal ++ [.transcript ZkcExamples.Construction.SchnorrProof.context.suite []])) :=
  checkNativeLowering_preserves _ _ _ _ _ _ _ schnorr_admitted data initial bytes key admitted

theorem sumcheck_all_replies (data : List (Value F G)) (initial : History F G)
    (bytes : List UInt8) (key : Origin → Origin) (admitted : sumcheckValidator.admits data = true) :
    ∃ nominal, Uniform.DomainAdapter.embedValues data = some nominal ∧
      Reached ZkcExamples.Construction.SumcheckProof.context.suite key initial data
        (entryScope sumcheckValidator).reading (Zkc.Executable.initial sumcheckValidator data initial bytes)
        (nominal ++ [.transcript ZkcExamples.Construction.SumcheckProof.context.suite []])
        (data ++ [.transcript initial]) ∧
      PIR.Yields sumcheckFinal.Holds
        (Domain.evaluate (Structured.ringModel F G) ZkcExamples.Construction.SumcheckProof.program
          ZkcExamples.Construction.SumcheckProof.context (Code.instructions sumcheckLowered.code)
          (nominal ++ [.transcript ZkcExamples.Construction.SumcheckProof.context.suite []])) :=
  checkNativeLowering_preserves _ _ _ _ _ _ _ sumcheck_admitted data initial bytes key admitted


variable {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem schnorrPrepared : ∀ name ∈ Instruction.helperList ZkcExamples.Construction.SchnorrProof.participant.instructions,
    Prepared installed schnorrValidator (Domain.helperTable (Structured.ringModel F G) ZkcExamples.Construction.SchnorrProof.program) name := by
  have empty : Instruction.helperList ZkcExamples.Construction.SchnorrProof.participant.instructions = [] := by decide +kernel
  simp [empty]

private theorem sumcheckPrepared : ∀ name ∈ Instruction.helperList ZkcExamples.Construction.SumcheckProof.participant.instructions,
    Prepared installed sumcheckValidator (Domain.helperTable (Structured.ringModel F G) ZkcExamples.Construction.SumcheckProof.program) name := by
  rw [Uniform.DomainAdapter.helperTable_eq]
  have names : Instruction.helperList ZkcExamples.Construction.SumcheckProof.participant.instructions =
      [ZkcExamples.Structured.SumcheckHelperBodies.emptyHelper.name,
        ZkcExamples.Structured.SumcheckHelperBodies.appendHelper.name,
        ZkcExamples.Structured.SumcheckHelperBodies.checkHelper.name] := by decide +kernel
  rw [names]
  exact ZkcExamples.Executable.SumcheckHelpers.prepared

theorem schnorr_native_correspondence (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (data : List (Value F G)) (initial : History F G) (bytes : List UInt8)
    (admitted : schnorrValidator.admits data = true) :
    ∃ nominal, Uniform.DomainAdapter.embedValues data = some nominal ∧
      Run.observe <$> execute installed schnorrValidator ZkcExamples.Construction.SchnorrProof.context challenge decode budget data initial bytes =
        nativeObservation ZkcExamples.Construction.SchnorrProof.context.suite Origin.withoutCoordinates initial <$>
          DomainVM.metered ZkcExamples.Construction.SchnorrProof.program ZkcExamples.Construction.SchnorrProof.context
            Origin.withoutCoordinates initial challenge (helperCost installed schnorrValidator) budget schnorrLowered
            (nominal ++ [.transcript ZkcExamples.Construction.SchnorrProof.context.suite []])
            (decodeProof decode (Plan.types data schnorrLowered.plan) bytes) := by
  obtain ⟨_, entry, _⟩ := checkNativeLowering_checks _ _ _ _ _ _ _ schnorr_admitted
  obtain ⟨nominal, embedded, _, _⟩ := nativeEntry_reached _ _ entry data initial bytes Origin.withoutCoordinates admitted
  exact ⟨nominal, embedded, checked_execute_metered _ _ _ challenge _ _ _ decode budget schnorrPrepared _ _ schnorr_admitted data bytes admitted nominal embedded⟩

theorem sumcheck_native_correspondence (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (data : List (Value F G)) (initial : History F G) (bytes : List UInt8)
    (admitted : sumcheckValidator.admits data = true) :
    ∃ nominal, Uniform.DomainAdapter.embedValues data = some nominal ∧
      Run.observe <$> execute installed sumcheckValidator ZkcExamples.Construction.SumcheckProof.context challenge decode budget data initial bytes =
        nativeObservation ZkcExamples.Construction.SumcheckProof.context.suite Origin.withoutCoordinates initial <$>
          DomainVM.metered ZkcExamples.Construction.SumcheckProof.program ZkcExamples.Construction.SumcheckProof.context
            Origin.withoutCoordinates initial challenge (helperCost installed sumcheckValidator) budget sumcheckLowered
            (nominal ++ [.transcript ZkcExamples.Construction.SumcheckProof.context.suite []])
            (decodeProof decode (Plan.types data sumcheckLowered.plan) bytes) := by
  obtain ⟨_, entry, _⟩ := checkNativeLowering_checks _ _ _ _ _ _ _ sumcheck_admitted
  obtain ⟨nominal, embedded, _, _⟩ := nativeEntry_reached _ _ entry data initial bytes Origin.withoutCoordinates admitted
  exact ⟨nominal, embedded, checked_execute_metered _ _ _ challenge _ _ _ decode budget sumcheckPrepared _ _ sumcheck_admitted data bytes admitted nominal embedded⟩

abbrev program := ZkcExamples.Construction.SchnorrProof.program
abbrev context := ZkcExamples.Construction.SchnorrProof.context

def messageScope (depth : Nat) : NativeScope :=
  ⟨[.transcript context.suite, .data .boolean, .indices depth], 0⟩
def message : Template :=
  ⟨context.entry, [], ["message", context.entry, "m", "m", "P", "V"]⟩

theorem wrong_operands_rejected :
    nativeResults program context ⟨[.data .boolean, .data .boolean], 0⟩
      .indicesAppend [0, 1] = none := by decide +kernel

theorem wrong_schema_rejected :
    checkNativeItem program context
      (.step ⟨.receive "site" "other-schema" "P" .boolean, [], [.data .boolean], []⟩ 1)
      (messageScope 0) = none := by decide +kernel

theorem nonempty_receive_body_rejected :
    checkNativeItem program context
      (.step ⟨.receive "site" "site" "P" .boolean, [], [.data .boolean],
        [⟨.indicesEmpty, [], [.indices], []⟩]⟩ 1) (messageScope 0) = none := by decide +kernel

theorem wrong_origin_rejected :
    nativeResults program context (messageScope 0)
      (.observe context.suite { message with entry := "wrong-entry" }) [0, 1, 2] = none := by decide +kernel

theorem wrong_path_kind_rejected :
    nativeResults program context (messageScope 0)
      (.observe context.suite { message with steps := [⟨"unsupported", "protocol", "site"⟩] })
      [0, 1, 2] = none := by decide +kernel

theorem wrong_depth_rejected :
    nativeResults program context (messageScope 1) (.observe context.suite message)
      [0, 1, 2] = none := by decide +kernel

end Tests.DomainNativeScope
