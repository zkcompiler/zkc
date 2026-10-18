module

public import ZkcExamples.Executable.SchnorrProofProgramData
public import ZkcExamples.Construction.SchnorrProof
public import Zkc.Executable.Soundness
public import Zkc.Executable.Installed

@[expose] public section

/-! The executable Schnorr proof verifier.

`SchnorrProofProgramData` is the validator participant of the `zkc.program/0`
candidate that the native deployment of `example::Proof` carries and the
runtime admits. The lowering rule accepts it against the constructed validator
that the composed transcript-construction and participant projection check
accepted (`accepted`): it reads back as exactly those instructions, with a
complete run charging 25 instructions, the runtime's measured threshold. With
the composed rules' theorem for this Entry
(`ZkcExamples.Construction.SchnorrProof.compiled_transform`, an instance of
`Zkc.Construction.compiled_transform` with no Entry-specific equation about the
compiled program), the
executable's meaning at any budget of at least 25, under the Entry's checked
occurrence context, is the Fiat–Shamir transform of the original Proof Entry's
verifier, on the proof its message bytes decode to, for every decoder and
challenge function (`executable_transform`). Host validation of proof bytes is
then the ideal validator's acceptance of the decoded proof
(`executable_validate`); below 25 instructions, or with another framing header,
it rejects on every path (`executable_rejects`).
-/

namespace ZkcExamples.Executable.SchnorrProof
open Zkc.Construction Zkc.Executable
open ZkcExamples.Construction

abbrev validator : Validator := SchnorrProofProgramData.validator

set_option maxRecDepth 20000 in
/-- The reading of the executable validator. -/
def lowered : Lowered :=
  (checkLowering installed SchnorrProof.participant validator).toOption.get (by decide +kernel)

theorem ok_of_isSome {ε α : Type} :
    ∀ (result : Except ε α) (present : result.toOption.isSome = true),
      result = .ok (result.toOption.get present)
  | .ok _, _ => rfl
  | .error _, present => by simp [Except.toOption] at present

/-- The per-compile lowering rule accepts the actual executable validator. -/
theorem accepted : checkLowering installed SchnorrProof.participant validator = .ok lowered :=
  ok_of_isSome _ _

set_option maxRecDepth 20000 in
/-- A complete run charges 25 instructions. -/
theorem total : lowered.total = 25 := by decide +kernel

set_option maxRecDepth 20000 in
/-- The receive types: the commitment in G1, then the response in the scalar field. -/
theorem receives : lowered.receives =
    [⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩, ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩] := by
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the validator's data inputs, base then statement. -/
theorem admitted (base key : G) : validator.admits (SchnorrProof.inputs (F := F) base key) = true := by
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem observation_mapOutcome {α β : Type} (f : α → β) (outcome : PIR.Outcome α) (complete : Bool) :
    (mapOutcome f (observation outcome complete).1, (observation outcome complete).2) =
      observation (mapOutcome f outcome) complete := by
  cases outcome <;> rfl

/-- At any budget of at least 25, the executable validator, under the ideal
transcript model with any challenge function in any lawful monad and any
decoder, is the Fiat–Shamir transform of the original Proof Entry's verifier on
the proof its message bytes decode to: equal acceptance outcomes and stops,
equal reading of the whole proof on a normal return, and the same challenge
interaction. -/
theorem executable_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    {budget : Nat} (sufficient : 25 ≤ budget) (base key : G) (handle : Nat) (initial : History F G)
    (bytes : List UInt8) :
    (fun result => (mapOutcome SchnorrProof.acceptance result.observe.1, result.observe.2)) <$>
        execute installed validator SchnorrProof.context challenge decode budget (SchnorrProof.inputs base key)
          initial bytes =
      (fun result => observation result.1 result.2.isEmpty) <$> transform SchnorrProof.context challenge
        (SchnorrProof.verifier base key handle) initial (decodeProof decode lowered.receives bytes) := by
  obtain ⟨read, code, returned, -⟩ := checkLowering_sound accepted
  have ideal_eq := execute_ideal installed validator SchnorrProof.context challenge SchnorrProof.table decode
    budget read (total ▸ sufficient) (SchnorrProof.inputs base key) initial bytes (admitted base key)
  rw [code, returned] at ideal_eq
  have compiled := SchnorrProof.compiled_transform challenge base key handle initial
    (decodeProof decode lowered.receives bytes)
  have observed : (fun result => (mapOutcome SchnorrProof.acceptance result.observe.1, result.observe.2)) <$>
        execute installed validator SchnorrProof.context challenge decode budget
          (SchnorrProof.inputs base key) initial bytes =
      (fun observed => (mapOutcome SchnorrProof.acceptance observed.1, observed.2)) <$>
        (Run.observe <$> execute installed validator SchnorrProof.context challenge decode budget
          (SchnorrProof.inputs base key) initial bytes) := by
    rw [Functor.map_map]
  have pointwise : ∀ result : PIR.Outcome (List (Value F G)) × Proof F G,
      (mapOutcome SchnorrProof.acceptance (idealObservation result).1, (idealObservation result).2) =
        observation (mapOutcome SchnorrProof.acceptance result.1, result.2).1
          (mapOutcome SchnorrProof.acceptance result.1, result.2).2.isEmpty := fun result =>
    observation_mapOutcome _ _ _
  rw [observed, ideal_eq, ← compiled, Functor.map_map, Functor.map_map]
  simp only [pointwise]

/-- With the expected framing header and a budget of at least 25, host
validation of the proof bytes is the ideal validator's acceptance of the proof
the messages decode to. -/
theorem executable_validate {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    {budget : Nat} (sufficient : 25 ≤ budget) (binding : List UInt8) (base key : G)
    (initial : History F G) (bytes : List UInt8) (header : bytes.take 40 = magic ++ binding) :
    validate installed validator SchnorrProof.context challenge decode budget binding
        SchnorrProof.acceptancePosition (SchnorrProof.inputs base key) initial bytes =
      (fun result => Accepts SchnorrProof.acceptancePosition (idealObservation result)) <$>
        ideal SchnorrProof.context challenge SchnorrProof.table SchnorrProof.participant.returned
          SchnorrProof.participant.instructions
          ((SchnorrProof.inputs base key).map .data ++ [.transcript initial])
          (decodeProof decode lowered.receives (bytes.drop 40)) := by
  obtain ⟨read, code, returned, -⟩ := checkLowering_sound accepted
  rw [← code, ← returned]
  exact validate_ideal installed validator SchnorrProof.context challenge SchnorrProof.table decode budget read
    (total ▸ sufficient) binding SchnorrProof.acceptancePosition _ initial bytes (admitted base key) header

/-- Below 25 instructions, or with another framing header, host validation
rejects on every path. -/
theorem executable_rejects {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    {budget : Nat} (binding : List UInt8) (base key : G) (initial : History F G) (bytes : List UInt8)
    (short : budget < 25 ∨ bytes.take 40 ≠ magic ++ binding) :
    validate installed validator SchnorrProof.context challenge decode budget binding
        SchnorrProof.acceptancePosition (SchnorrProof.inputs base key) initial bytes =
      (fun _ => false) <$> validate installed validator SchnorrProof.context challenge decode budget binding
        SchnorrProof.acceptancePosition (SchnorrProof.inputs base key) initial bytes :=
  validate_rejects installed validator SchnorrProof.context challenge decode budget
    (checkLowering_sound accepted).1 binding SchnorrProof.acceptancePosition _ initial bytes (admitted base key)
    (total ▸ short)

end ZkcExamples.Executable.SchnorrProof
