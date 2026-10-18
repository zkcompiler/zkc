module

public import ZkcSecurity.Examples.GkrFiatShamir
public import ZkcExamples.Construction.GkrProofReading

@[expose] public section

/-! Fiat–Shamir soundness of the compiled GKR proof Entry.

The subject is the compiler's constructed validator for the GKR example's
`example::Proof` Entry (`ZkcExamples.Construction.GkrProofParticipant.participant`),
which the composed transcript-construction and participant projection check
accepts (`ZkcExamples.Construction.GkrProof.compiled`). Its meaning is the ideal
interpretation of the exported operations (`Zkc.Construction.ideal`) under the
Entry's checked occurrence context, with helper calls read by the original's
checked helpers, on the circuit's input values, the claimed outputs, the stacked
wiring tables, the number of layers, the number of selector coordinates and the
width, the initial transcript and the proof's messages. The verifier accepts
when the acceptance output the policy selects is true (`compiledVerifier`).

Two proved links compose:

* Vertical. For every challenge function the compiled meaning is the
  Fiat–Shamir transform of the interactive reading of the exported instructions
  (`GkrProof.spec_transform`, from the transcript-construction rule's
  soundness). The participant projection rule also accepts the export, so the
  same meaning is the transform of the original GKR validator
  (`GkrProof.compiled_transform`).
* Horizontal. On a well-formed statement the interactive reading is the plain
  GKR verifier (`GkrProof.reading`), whose transform has a round-by-round
  certificate (`ZkcSecurity.Examples.GkrFiatShamir.soundness`).

A statement is well-formed (`WellFormed`) when the input values and claimed
outputs decode to tables of the width, every layer's block of the stacked add
and mul tables decodes to that layer's wiring, the stacked tables have
`2 ^ selector` blocks of `2 ^ (3 width)` values, every layer has a block, and the
width and the number of layers are within the Entry's maxima. `soundness`
bounds the probability that the compiled verifier accepts claimed outputs other
than the circuit's, for a fixed well-formed statement and initial transcript, in
a random oracle on all typed histories, by
`(Q + width + layers (2 width + 1)) max 2 width / |F|`. Acceptance here ignores
unread proof messages; no executable meaning of this Entry is covered.
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.CompiledGkrFiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr
open scoped ENNReal

variable {F G : Type}

/-- A statement whose raw public inputs decode to the circuit the plain verifier
reads: input and output tables of the width, and for every layer the add and
mul blocks of the stacked wiring tables. -/
structure WellFormed [CommRing F] (inputs outputs add mul : List F) (layers selector width : Nat)
    (inputsTable outputsTable : Table F width) (addTables mulTables : Nat → Wiring F width) : Prop where
  inputsDecoded : ofList? width inputs = some inputsTable
  outputsDecoded : ofList? width outputs = some outputsTable
  addShape : add.length = 2 ^ selector * 2 ^ (width + width + width)
  mulShape : mul.length = 2 ^ selector * 2 ^ (width + width + width)
  addBound : add.length < indexLimit
  mulBound : mul.length < indexLimit
  addDecoded : ∀ layer < layers, ofList? (width + width + width)
    (GkrSourceLaws.block add layer (2 ^ (width + width + width))) = some (addTables layer)
  mulDecoded : ∀ layer < layers, ofList? (width + width + width)
    (GkrSourceLaws.block mul layer (2 ^ (width + width + width))) = some (mulTables layer)
  selectorBound : layers ≤ 2 ^ selector
  widthBound : width ≤ 4
  layersBound : layers ≤ 4

section Compiled
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The compiled GKR verifier: the ideal meaning of the exported validator with
the challenge function `challenge`, on the raw public statement, from the
initial transcript `initial`, read through the acceptance output the policy
selects. -/
def compiledVerifier {m : Type → Type} [Monad m] (challenge : History F G → m F)
    (inputs outputs add mul : List F) (layers selector width : Nat) (initial : History F G)
    (proof : Proof F G) : m (PIR.Outcome (Option Bool) × Proof F G) :=
  (fun result => (mapOutcome GkrProof.acceptance result.1, result.2)) <$>
    ideal GkrProof.context challenge (helperTable GkrProof.program F G) GkrProof.participant.returned
      GkrProof.participant.instructions
      (GkrProof.inputs inputs outputs add mul layers selector width ++ [.transcript initial]) proof

/-- For every challenge function, the compiled verifier on a well-formed
statement is the Fiat–Shamir transform of the plain GKR verifier. -/
theorem construction {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (inputs outputs add mul : List F) (layers selector width : Nat)
    (inputsTable outputsTable : Table F width) (addTables mulTables : Nat → Wiring F width)
    (wellFormed : WellFormed inputs outputs add mul layers selector width inputsTable outputsTable
      addTables mulTables)
    (handle : Nat) (initial : History F G) (proof : Proof F G) :
    compiledVerifier challenge inputs outputs add mul layers selector width initial proof =
      transform GkrProof.context challenge
        (GkrVerifier.verifier {} handle layers width outputsTable inputsTable addTables mulTables)
        initial proof := by
  rw [compiledVerifier, GkrProof.spec_transform challenge handle
    (GkrProof.inputs inputs outputs add mul layers selector width) rfl initial proof, GkrProof.context_eq,
    GkrProof.reading handle inputs outputs add mul layers selector width initial outputsTable inputsTable
      wellFormed.outputsDecoded wellFormed.inputsDecoded addTables mulTables wellFormed.addShape
      wellFormed.mulShape wellFormed.addBound wellFormed.mulBound wellFormed.addDecoded
      wellFormed.mulDecoded wellFormed.selectorBound wellFormed.widthBound wellFormed.layersBound]

end Compiled

section Security
variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Fiat–Shamir soundness of the compiled GKR proof Entry for a fixed
statement: against every prover with at most `queries` queries to one lazily
sampled random oracle on all typed histories (empty initial cache, shared with
the verifier's challenges), the compiled verifier accepts claimed outputs other
than the circuit's outputs on its inputs with probability at most
`(queries + width + layers (2 width + 1)) max 2 width / |F|`, for every
well-formed statement and initial transcript. -/
theorem soundness (inputs outputs add mul : List F) (layers selector width : Nat)
    (inputsTable outputsTable : Table F width) (addTables mulTables : Nat → Wiring F width)
    (wellFormed : WellFormed inputs outputs add mul layers selector width inputsTable outputsTable
      addTables mulTables)
    (wrong : outputsTable ≠ values addTables mulTables inputsTable layers 0)
    (initial : History F G) (prover : OracleComp (FieldOracle F G) (Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (prover >>= compiledVerifier historyQuery inputs outputs add mul layers selector width initial)).run' ∅}[
      Accepted (· = some true) result.1] ≤
      (queries + (width + layers * (2 * width + 1))) * GkrFiatShamir.error F width := by
  have same : (prover >>= compiledVerifier historyQuery inputs outputs add mul layers selector width initial) =
      FiatShamir.experiment GkrProof.context
        (GkrVerifier.verifier {} 0 layers width outputsTable inputsTable addTables mulTables) initial prover :=
    congrArg (prover >>= ·) (funext fun proof => construction historyQuery inputs outputs add mul layers
      selector width inputsTable outputsTable addTables mulTables wellFormed 0 initial proof)
  rw [same]
  exact GkrFiatShamir.soundness {} 0 layers width outputsTable inputsTable addTables mulTables
    GkrProof.context wrong initial prover queries proverBound

end Security

end ZkcSecurity.Examples.CompiledGkrFiatShamir
