module

public import ZkcArkLib.Examples.GkrFiatShamir
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import ZkcExamples.Construction.GkrProof
public import ZkcExamples.Structured.GkrSourceVerifier

@[expose] public section

/-! Fiat–Shamir soundness of the compiled GKR proof Entry.

The subject is the compiler's constructed validator for the GKR example's
`example::Proof` Entry (`ZkcExamples.Construction.GkrProofParticipant.participant`),
which the composed transcript-construction and participant projection check
accepts (`ZkcExamples.Construction.GkrProof.compiled`). Its meaning is actual checked Domain execution of the exported operations under the
Entry's checked occurrence context, with helper calls read by the original's
checked helpers, on the circuit's input values, the claimed outputs, the stacked
wiring tables, the number of layers, the number of selector coordinates and the
width, the initial transcript and the proof's messages. The verifier accepts
when the acceptance output the policy selects is true (`compiledVerifier`).

Three proved links compose:

* Vertical. Structural checks fix the admitted export. The separate
  all-reply Domain-to-source connection proves that, for every challenge
  function, its execution is the Fiat–Shamir transform of the admitted original
  GKR validator, read through its acceptance output
  (`GkrProof.compiled_transform`).
* Original. On a well-formed statement the original validator at the verifier
  is the plain GKR verifier
  (`ZkcExamples.Structured.GkrSourceVerifier.verifier_reads`): the generated
  normal form of the admitted root (`Generated.Presentations.Gkr.Root.verifier_participant`),
  its loops read as the folds of their callbacks' normal forms and its helper
  calls read with the admitted unit's helper laws.
* Horizontal. The plain verifier's transform has a charged certificate composed
  from one reduction per phase (`ZkcSecurity.Examples.GkrFiatShamir.certificate`).

A statement is well-formed (`WellFormed`) when the input values and claimed
outputs decode to tables of the width, every layer's block of the stacked add
and mul tables decodes to that layer's wiring, the stacked tables have
`2 ^ selector` blocks of `2 ^ (3 width)` values, every layer has a block, and the
width and the number of layers are within the Entry's maxima. `soundness`
bounds the probability that the compiled verifier accepts claimed outputs other
than the circuit's, for a fixed well-formed statement and initial transcript, in
a random oracle on all typed histories, by
`(Q + width + layers (2 width + 1)) max 2 width / |F|`; `soundness_charged`
bounds it against a weighted adversary budget, each oracle key charged its
challenge site's error. Acceptance here ignores unread proof messages; no
executable meaning of this Entry is covered.
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

/-- The compiled GKR verifier: actual checked Domain execution of the exported validator with
the challenge function `challenge`, on the raw public statement, from the
initial transcript `initial`, read through the acceptance output the policy
selects. -/
def compiledVerifier {m : Type → Type} [Monad m] (challenge : History F G → m F)
    (inputs outputs add mul : List F) (layers selector width : Nat) (initial : History F G)
    (proof : Proof F G) : m (PIR.Outcome (Option Bool) × Proof F G) :=
  GkrProof.compiledVerifier challenge inputs outputs add mul layers selector width initial proof

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
  rw [compiledVerifier, GkrProof.compiled_transform challenge inputs outputs add mul layers selector width handle
    initial proof]
  congr 1
  exact GkrSourceVerifier.verifier_reads handle inputs outputs add mul layers selector width outputsTable
    inputsTable wellFormed.outputsDecoded wellFormed.inputsDecoded addTables mulTables wellFormed.addShape
    wellFormed.mulShape wellFormed.addBound wellFormed.mulBound wellFormed.addDecoded wellFormed.mulDecoded
    wellFormed.selectorBound wellFormed.widthBound wellFormed.layersBound

end Compiled

section Security
variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Fiat–Shamir soundness of the compiled GKR proof Entry for a fixed
statement, against a weighted adversary budget: against every prover whose
queries to one lazily sampled random oracle on all typed histories (empty
initial cache, shared with the verifier's challenges) charge at most
`proverCost` on every path, each oracle key charged the error of its challenge
site in the Entry's occurrence context (`GkrFiatShamir.siteCharge`: `1 / |F|` at
the output point, `2 / |F|` at a layer Sumcheck round, `width / |F|` at the line
challenge), the compiled verifier accepts claimed outputs other than the
circuit's outputs on its inputs with probability at most
`proverCost + (width + layers (2 width + 1)) max 2 width / |F|`, for every
well-formed statement and initial transcript. -/
theorem soundness_charged (inputs outputs add mul : List F) (layers selector width : Nat)
    (inputsTable outputsTable : Table F width) (addTables mulTables : Nat → Wiring F width)
    (wellFormed : WellFormed inputs outputs add mul layers selector width inputsTable outputsTable
      addTables mulTables)
    (wrong : outputsTable ≠ values addTables mulTables inputsTable layers 0)
    (initial : History F G) (prover : OracleComp (FieldOracle F G) (Proof F G)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨Typed.keyCharge (GkrFiatShamir.siteCharge (G := G) {} GkrProof.context width)⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle
        (prover >>= compiledVerifier historyQuery inputs outputs add mul layers selector width initial)).run' ∅}[
      Accepted (· = some true) result.1] ≤
      proverCost + (width + layers * (2 * width + 1)) * GkrFiatShamir.error F width := by
  have same : (prover >>= compiledVerifier historyQuery inputs outputs add mul layers selector width initial) =
      FiatShamir.experiment GkrProof.context
        (GkrVerifier.verifier {} 0 layers width outputsTable inputsTable addTables mulTables) initial prover :=
    congrArg (prover >>= ·) (funext fun proof => construction historyQuery inputs outputs add mul layers
      selector width inputsTable outputsTable addTables mulTables wellFormed 0 initial proof)
  rw [same]
  exact GkrFiatShamir.soundness_charged {} 0 layers width outputsTable inputsTable addTables mulTables
    GkrProof.context wrong initial prover proverCost proverBound

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
