module

public import Zkc.Executable.DomainNativeByteTransport

@[expose] public section
/-! Short static Code budgets cannot return. Mapping the final result retains
all preceding oracle actions; the theorem never equates an effectful rejection
with a pure constant. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G A R B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem map_runK (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (f g : PIR.Outcome R × Proof F G → B)
    (stops : ∀ reason unread, f (.stopped reason, unread) = g (.stopped reason, unread))
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A) (proof : Proof F G)
    (next : A → Proof F G → m (PIR.Outcome R × Proof F G))
    (returns : ∀ value unread, f <$> next value unread = g <$> next value unread) :
    f <$> DomainAdapter.runK key initial challenge process proof next =
      g <$> DomainAdapter.runK key initial challenge process proof next := by
  induction process generalizing proof with
  | done => exact returns _ _
  | halt => simp [DomainAdapter.runK, stops]
  | call operation continuation ih =>
    cases operation with
    | receive ty site schema peer =>
      cases proof with
      | nil => simp [DomainAdapter.runK, stops]
      | cons payload unread =>
        simp only [DomainAdapter.runK]
        cases Value.decode ty (.data payload) with
        | none => simp [stops]
        | some value => exact ih value unread
    | send | observe | checkpoint => exact ih () proof
    | localService => simp [DomainAdapter.runK, stops]
    | query history origin =>
      simp only [DomainAdapter.runK]
      split
      · rw [map_bind, map_bind]
        congr 1
        funext answer
        cases answer with
        | stopped => simp [stops]
        | returned value => exact ih value proof
      · simp [stops]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context) (key : Origin → Origin)
  (initial : History F G) (challenge : History F G → m F)
  (cost : String → List (Value F G) → Nat) (budget : Nat)
  (f g : PIR.Outcome R × Proof F G → B)
  (stops : ∀ reason unread, f (.stopped reason, unread) = g (.stopped reason, unread))

include stops in
private theorem map_staticCode :
    ∀ (code : List Code) {total : Nat}, Code.static code = some total →
      ∀ (env : Environment F G) (proof : Proof F G) (used : Nat)
        (next : Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G)),
        (∀ final unread, f <$> next final unread (used + total) = g <$> next final unread (used + total)) →
        f <$> meteredK program context key initial challenge cost budget code env proof used next =
          g <$> meteredK program context key initial challenge cost budget code env proof used next
  | [], total, static, env, proof, used, next, returns => by
    simp only [Code.static, Option.some.injEq] at static
    subst total
    simpa only [meteredK, Nat.add_zero] using returns env proof
  | .charge count :: rest, total, static, env, proof, used, next, returns => by
    simp only [Code.static] at static
    cases tail : Code.static rest with
    | none => simp [tail] at static
    | some remaining =>
      simp only [tail, Option.map_some, Option.some.injEq] at static
      subst total
      simp only [meteredK, meteredStep]
      split
      · exact map_staticCode rest tail _ _ _ next (by simpa only [Nat.add_assoc] using returns)
      · simp [stops]
  | .step instruction charged :: rest, total, static, env, proof, used, next, returns => by
    simp only [Code.static] at static
    cases tail : Code.static rest with
    | none => simp [tail] at static
    | some remaining =>
      simp only [tail, Option.map_some, Option.some.injEq] at static
      subst total
      simp only [meteredK, meteredStep]
      split
      · apply map_runK key initial challenge f g stops
        intro final unread
        exact map_staticCode rest tail _ _ _ next (by simpa only [Nat.add_assoc] using returns)
      · simp [stops]
  | .helper _ :: _, _, static, _, _, _, _, _ => by simp [Code.static] at static
  | .loop .. :: _, _, static, _, _, _, _, _ => by simp [Code.static] at static

/-- Any result projection agreeing on stops is indistinguishable below the
static threshold, while keeping the entire monadic action prefix. -/
theorem metered_short_maps
    (f g : PIR.Outcome (Environment F G) × Proof F G → B)
    (stops : ∀ reason unread, f (.stopped reason, unread) = g (.stopped reason, unread))
    {lowered : Lowered} {total : Nat}
    (static : lowered.total? = some total) (short : budget < total)
    (env : Environment F G) (proof : Proof F G) :
    f <$> metered program context key initial challenge cost budget lowered env proof =
      g <$> metered program context key initial challenge cost budget lowered env proof := by
  unfold Lowered.total? at static
  cases codeStatic : Code.static lowered.code with
  | none => simp [codeStatic] at static
  | some charges =>
    simp only [codeStatic, Option.map_some, Option.some.injEq] at static
    subst total
    unfold metered
    apply map_staticCode program context key initial challenge cost budget f g stops lowered.code codeStatic
    intro final unread
    simp only [Nat.zero_add, show ¬ charges + 1 ≤ budget by omega, ite_false, map_pure, stops]

/-- Native host rejection below a static threshold or on a bad header, without
removing any challenge computation that precedes exhaustion. -/
theorem checked_validate_rejects_static
    (vocabulary : Vocabulary) (participant : Participant) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (prepared : ∀ name ∈ Instruction.helperList participant.instructions,
      Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name)
    (lowered : Lowered) (final : NativeScope)
    (checked : checkNativeLowering program context vocabulary participant validator = .ok (lowered, final))
    (total : Nat) (static : lowered.total? = some total)
    (binding : List UInt8) (position : Nat) (data : List (Value F G)) (bytes : List UInt8)
    (admitted : validator.admits data = true)
    (nominal : Environment F G) (embedded : DomainAdapter.embedValues data = some nominal)
    (short : budget < total ∨ bytes.take 40 ≠ magic ++ binding) :
    Executable.validate vocabulary validator context challenge decode budget binding position data initial bytes =
      (fun _ => false) <$> Executable.validate vocabulary validator context challenge decode budget binding position data initial bytes := by
  rw [checked_validate_metered program context initial challenge vocabulary participant validator decode budget
    prepared lowered final checked binding position data bytes admitted nominal embedded]
  split
  · rename_i header
    rw [Functor.map_map]
    exact metered_short_maps program context Origin.withoutCoordinates initial challenge
      (helperCost vocabulary validator) budget
      (byteAcceptance position ∘ nativeObservation context.suite Origin.withoutCoordinates initial)
      (fun _ => false) (fun _ _ => rfl) static (short.resolve_right (fun bad => bad header)) _ _
  · simp

end Zkc.Executable.DomainVM
