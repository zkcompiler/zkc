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
accepted (`accepted`): it reads back as exactly those instructions, without
loops or helper calls, with a complete run charging 25 instructions, the
runtime's measured threshold. With the composed rules' theorem for this Entry
(`ZkcExamples.Construction.SchnorrProof.compiled_transform`, an instance of
`Zkc.Construction.compiled_transform` with no Entry-specific equation about the
compiled program), the executable's meaning at any budget of at least 25, under
the Entry's checked occurrence context, is the Fiat–Shamir transform of the
original Proof Entry's verifier, on the proof its message bytes decode to, for
every decoder and challenge function (`executable_transform`). Host validation
of proof bytes is then the ideal validator's acceptance of the decoded proof
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

/-- The per-compile lowering rule accepts the actual executable validator. -/
theorem accepted : checkLowering installed SchnorrProof.participant validator = .ok lowered :=
  ok_of_isSome _ _

/-- The constructed validator calls no helper. -/
theorem helpers : Instruction.helpers SchnorrProof.participant.instructions = [] := by
  rw [← Instruction.helperList_eq]
  decide +kernel

set_option maxRecDepth 20000 in
/-- A complete run charges 25 instructions. -/
theorem total : lowered.total? = some 25 := by decide +kernel

/-- The receive types: the commitment in G1, then the response in the scalar field. -/
abbrev receives : List PhysicalType :=
  [⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩, ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩]

set_option maxRecDepth 20000 in
theorem plan_static : Plan.static lowered.plan = some receives := by decide +kernel

theorem plan_types {F G : Type} (data : List (Value F G)) : Plan.types data lowered.plan = receives :=
  Plan.types_static data plan_static

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- No helper needs preparation. -/
theorem prepared : ∀ name ∈ Instruction.helpers SchnorrProof.participant.instructions,
    Prepared installed validator (SchnorrProof.table (F := F) (G := G)) name := by
  simp [helpers]

/-- The data inputs of the executable: base then statement. -/
abbrev data (base key : G) : List (Value F G) := (SchnorrProof.inputs (F := F) base key).map .data

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the validator's data inputs. -/
theorem admitted (base key : G) : validator.admits (data (F := F) base key) = true := by
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
        execute installed validator SchnorrProof.context challenge decode budget (data base key)
          initial bytes =
      (fun result => observation result.1 result.2.isEmpty) <$> transform SchnorrProof.context challenge
        (SchnorrProof.verifier base key handle) initial (decodeProof decode receives bytes) := by
  obtain ⟨read, code, returned, -⟩ := checkLowering_sound accepted
  have ideal_eq := execute_ideal installed validator SchnorrProof.context challenge SchnorrProof.table decode
    budget _ prepared read total sufficient (data base key) initial bytes (admitted base key)
  rw [code, returned, plan_types] at ideal_eq
  have compiled := SchnorrProof.compiled_transform challenge base key handle initial
    (decodeProof decode receives bytes)
  have observed : (fun result => (mapOutcome SchnorrProof.acceptance result.observe.1, result.observe.2)) <$>
        execute installed validator SchnorrProof.context challenge decode budget
          (data base key) initial bytes =
      (fun observed => (mapOutcome SchnorrProof.acceptance observed.1, observed.2)) <$>
        (Run.observe <$> execute installed validator SchnorrProof.context challenge decode budget
          (data base key) initial bytes) := by
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
        SchnorrProof.acceptancePosition (data base key) initial bytes =
      (fun result => Accepts SchnorrProof.acceptancePosition (idealObservation result)) <$>
        ideal SchnorrProof.context challenge SchnorrProof.table SchnorrProof.participant.returned
          SchnorrProof.participant.instructions
          ((SchnorrProof.inputs base key).map .data ++ [.transcript initial])
          (decodeProof decode receives (bytes.drop 40)) := by
  obtain ⟨read, code, returned, -⟩ := checkLowering_sound accepted
  rw [← code, ← returned, ← plan_types (data base key)]
  exact validate_ideal installed validator SchnorrProof.context challenge SchnorrProof.table decode budget _
    prepared read total sufficient binding SchnorrProof.acceptancePosition _ initial bytes (admitted base key)
    header

/-- Below 25 instructions, or with another framing header, host validation
rejects on every path. -/
theorem executable_rejects {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    {budget : Nat} (binding : List UInt8) (base key : G) (initial : History F G) (bytes : List UInt8)
    (short : budget < 25 ∨ bytes.take 40 ≠ magic ++ binding) :
    validate installed validator SchnorrProof.context challenge decode budget binding
        SchnorrProof.acceptancePosition (data base key) initial bytes =
      (fun _ => false) <$> validate installed validator SchnorrProof.context challenge decode budget binding
        SchnorrProof.acceptancePosition (data base key) initial bytes :=
  validate_rejects installed validator SchnorrProof.context challenge SchnorrProof.table decode budget _
    prepared (checkLowering_sound accepted).1 total binding SchnorrProof.acceptancePosition _ initial bytes
    (admitted base key) short

end ZkcExamples.Executable.SchnorrProof
