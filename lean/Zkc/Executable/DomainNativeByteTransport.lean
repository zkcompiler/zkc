module

public import Zkc.Executable.DomainNativeExecution
public import Zkc.Executable.DomainNormalization

@[expose] public section
/-! Reusable byte pruning and sufficient-budget APIs at the actual lowered
Domain Process. Normalization to the exported participant composes after this
boundary. Unsupported whole-tuple readback can only reject acceptance. -/
set_option autoImplicit false
namespace Zkc.Executable
open Zkc.Construction

theorem Prunes.map_or_reject {m : Type → Type} [Monad m] [LawfulMonad m] {A B : Type}
    {rejects : A → Prop} {rejects' : B → Prop} {first second : m A}
    (pruned : Prunes rejects first second) (f g : A → B)
    (reject : ∀ value, rejects value → rejects' (f value))
    (compare : ∀ value, f value = g value ∨ rejects' (f value)) :
    Prunes rejects' (f <$> first) (g <$> second) := by
  induction pruned with
  | refl computation =>
    rw [← bind_pure_comp, ← bind_pure_comp]
    apply Prunes.bind computation _ _
    intro value
    rcases compare value with same | refused
    · rw [same]; exact .refl _
    · exact .stop _ refused _
  | stop value rejected computation =>
    rw [map_pure]
    exact .stop _ (reject value rejected) _
  | bind computation left right step ih =>
    rw [map_bind, map_bind]
    exact .bind _ _ _ ih

namespace DomainVM
open Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

def nominalSelected (position : Nat) (values : Environment F G) : Bool :=
  match values[position]? with
  | some (.data (.boolean decision)) => decision
  | _ => false

def nominalAcceptance (position : Nat) (result : PIR.Outcome (Environment F G) × Proof F G) : Bool :=
  match result.1 with
  | .returned values => result.2.isEmpty && nominalSelected position values
  | .stopped _ => false

private theorem selected_readback (suite : String) (key : Origin → Origin) (initial : History F G)
    {env : Environment F G} {scalar : List (Value F G)} (erases : Erases suite key initial env scalar)
    (position : Nat) : selectedTrue scalar position = nominalSelected position env := by
  have found := erases.get position
  unfold selectedTrue nominalSelected
  cases nominal : env[position]? with
  | none => simp [nominal] at found; simp [found]
  | some value =>
    simp only [nominal, Option.bind_some] at found
    rw [found]
    cases value with
    | indices => rfl
    | transcript actual history =>
      by_cases same : actual = suite
      · cases mapped : DomainAdapter.readbackHistory key history <;> simp [DomainAdapter.readbackValue, same, mapped]
      · simp [DomainAdapter.readbackValue, same]
    | data payload =>
      rcases payload with ⟨ty, supported, contents⟩
      cases ty <;> try rfl
      cases contents <;> rfl

theorem byteAcceptance_readback_or_reject (suite : String) (key : Origin → Origin) (initial : History F G)
    (position : Nat) (result : PIR.Outcome (Environment F G) × Proof F G) :
    byteAcceptance position (nativeObservation suite key initial result) = nominalAcceptance position result ∨
      byteAcceptance position (nativeObservation suite key initial result) = false := by
  rcases result with ⟨outcome, unread⟩
  cases outcome with
  | stopped => exact Or.inl rfl
  | returned values =>
    cases erased : DomainAdapter.readbackValues suite key initial values with
    | none => right; simp [byteAcceptance, nativeObservation, DomainAdapter.readbackOutcome, erased, Executable.observation]
    | some scalar =>
      left
      simp only [byteAcceptance, nativeObservation, DomainAdapter.readbackOutcome, erased, Executable.observation,
        nominalAcceptance]
      rw [selected_readback suite key initial erased position]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The target is canonical evaluation of the actual lowered Code and its real
returned references, with selected nominal acceptance and complete unread
status. It retains arbitrary-byte decoding and preceding scalar oracle actions. -/
theorem checked_validate_prunes
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (participant : Participant) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (prepared : ∀ name ∈ Instruction.helperList participant.instructions,
      Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name)
    (lowered : Lowered) (final : NativeScope)
    (checked : checkNativeLowering program context vocabulary participant validator = .ok (lowered, final))
    (binding : List UInt8) (position : Nat) (data : List (Value F G)) (bytes : List UInt8)
    (admitted : validator.admits data = true)
    (nominal : Environment F G) (embedded : DomainAdapter.embedValues data = some nominal) :
    Prunes (fun decision => decision = false)
      (Executable.validate vocabulary validator context challenge decode budget binding position data initial bytes)
      (nominalAcceptance position <$>
        DomainAdapter.run Origin.withoutCoordinates initial challenge
          (observation program context (Code.instructions lowered.code) lowered.returned
            (nominal ++ [.transcript context.suite []]))
          (decodeProof decode (Plan.types data lowered.plan) (bytes.drop 40))) := by
  rw [checked_validate_metered program context initial challenge vocabulary participant validator decode budget prepared lowered final checked binding position data bytes admitted nominal embedded]
  split
  · apply (metered_prunes_observation program context Origin.withoutCoordinates initial challenge (helperCost vocabulary validator) budget lowered _ _).map_or_reject
      (byteAcceptance position ∘ nativeObservation context.suite Origin.withoutCoordinates initial) (nominalAcceptance position)
    · intro result stopped
      obtain ⟨reason, outcome⟩ := stopped
      rcases result with ⟨result, unread⟩
      simp only at outcome
      subst result
      rfl
    · exact byteAcceptance_readback_or_reject context.suite Origin.withoutCoordinates initial position
  · exact Prunes.stop (m := m) (rejects := fun decision : Bool => decision = false) false rfl _

/-- At a sufficient budget the complete native observation is exact, even for
malformed bytes or later semantic rejection. Sufficient is a resource predicate
on actual canonical Process continuations; it contains no execution equality. -/
theorem checked_execute_sufficient
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (participant : Participant) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (prepared : ∀ name ∈ Instruction.helperList participant.instructions,
      Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name)
    (lowered : Lowered) (final : NativeScope)
    (checked : checkNativeLowering program context vocabulary participant validator = .ok (lowered, final))
    (data : List (Value F G)) (bytes : List UInt8) (admitted : validator.admits data = true)
    (nominal : Environment F G) (embedded : DomainAdapter.embedValues data = some nominal)
    (fits : Sufficient program context (helperCost vocabulary validator) budget lowered
      (nominal ++ [.transcript context.suite []]) (decodeProof decode (Plan.types data lowered.plan) bytes)) :
    Run.observe <$> execute vocabulary validator context challenge decode budget data initial bytes =
      nativeObservation context.suite Origin.withoutCoordinates initial <$>
        DomainAdapter.run Origin.withoutCoordinates initial challenge
          (observation program context (Code.instructions lowered.code) lowered.returned (nominal ++ [.transcript context.suite []]))
          (decodeProof decode (Plan.types data lowered.plan) bytes) := by
  rw [checked_execute_metered program context initial challenge vocabulary participant validator decode budget prepared lowered final checked data bytes admitted nominal embedded,
    run_observation, metered_sufficient program context (helperCost vocabulary validator) budget Origin.withoutCoordinates initial challenge lowered _ _ fits]
  rfl

/-- A static Code total discharges the resource condition without restricting
inputs, decoded messages, scalar replies or later semantic rejection. -/
theorem checked_execute_static
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (participant : Participant) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (prepared : ∀ name ∈ Instruction.helperList participant.instructions,
      Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name)
    (lowered : Lowered) (final : NativeScope)
    (checked : checkNativeLowering program context vocabulary participant validator = .ok (lowered, final))
    (data : List (Value F G)) (bytes : List UInt8) (admitted : validator.admits data = true)
    (nominal : Environment F G) (embedded : DomainAdapter.embedValues data = some nominal)
    (total : Nat) (static : lowered.total? = some total) (fits : total ≤ budget) :
    Run.observe <$> execute vocabulary validator context challenge decode budget data initial bytes =
      nativeObservation context.suite Origin.withoutCoordinates initial <$>
        DomainAdapter.run Origin.withoutCoordinates initial challenge
          (observation program context (Code.instructions lowered.code) lowered.returned
            (nominal ++ [.transcript context.suite []]))
          (decodeProof decode (Plan.types data lowered.plan) bytes) := by
  rw [checked_execute_metered program context initial challenge vocabulary participant validator decode budget prepared lowered final checked data bytes admitted nominal embedded,
    metered_static_observation program context Origin.withoutCoordinates initial challenge
      (helperCost vocabulary validator) budget static fits]

/-- Exact host validation at a sufficient budget. The false sentinel, selected
returned Boolean, complete unread status and the actual 40-byte header are all
retained. Local codec laws can subsequently replace the decoded framed proof. -/
theorem checked_validate_sufficient
    (program : Structured.Program) (context : Context) (initial : History F G)
    (challenge : History F G → m F) (vocabulary : Vocabulary) (participant : Participant) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (prepared : ∀ name ∈ Instruction.helperList participant.instructions,
      Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name)
    (lowered : Lowered) (final : NativeScope)
    (checked : checkNativeLowering program context vocabulary participant validator = .ok (lowered, final))
    (binding : List UInt8) (position : Nat) (data : List (Value F G)) (bytes : List UInt8)
    (admitted : validator.admits data = true)
    (nominal : Environment F G) (embedded : DomainAdapter.embedValues data = some nominal)
    (fits : Sufficient program context (helperCost vocabulary validator) budget lowered
      (nominal ++ [.transcript context.suite []])
      (decodeProof decode (Plan.types data lowered.plan) (bytes.drop 40))) :
    Executable.validate vocabulary validator context challenge decode budget binding position data initial bytes =
      if bytes.take 40 = magic ++ binding then
        (byteAcceptance position ∘ nativeObservation context.suite Origin.withoutCoordinates initial) <$>
          DomainAdapter.run Origin.withoutCoordinates initial challenge
            (observation program context (Code.instructions lowered.code) lowered.returned
              (nominal ++ [.transcript context.suite []]))
            (decodeProof decode (Plan.types data lowered.plan) (bytes.drop 40))
      else pure false := by
  have lifted := validate_of_execute_observation vocabulary validator context challenge decode budget binding position data initial bytes _
    (checked_execute_sufficient program context initial challenge vocabulary participant validator decode budget prepared lowered final checked data (bytes.drop 40) admitted nominal embedded fits)
  convert lifted using 1; simp only [Functor.map_map, Function.comp_def]

end DomainVM
end Zkc.Executable
