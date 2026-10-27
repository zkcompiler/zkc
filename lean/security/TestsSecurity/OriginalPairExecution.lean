module

public import ZkcExamples.Structured.OriginalArtifacts.SmallSumcheckProducerRoot
public import ZkcExamples.Structured.OriginalArtifacts.SmallSumcheckValidatorRoot
public import ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot
public import ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot

@[expose] public section

/-! Full pair regression instances use the shared transport theorem. Their types
are inferred from that theorem, avoiding a second spelling of its experiment. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.OriginalPairExecution
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcExamples.Structured.OriginalArtifacts
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

namespace Small

/-- Both actual participant certificates feed the existing pair experiment.
The producer's proof and complete oracle/service post-state feed validation;
a stopped producer skips validation. Shape and size are explicit admission
conditions for the original producer's table operations. -/
theorem execute_pair (raw : List F) (scalar : F) (count handle : Nat)
    (shape : PrimitiveLibrary.HasShape raw count 1) (bounded : raw.length < indexLimit)
    (producerHistory validatorHistory : Domain.History (uniformCarriers F G))
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m (uniformCarriers F G) S) (state : S)
    (services : Domain.LocalServices m (uniformCarriers F G) S) : type_of% (
  Original.executePair_eq (model := ringModel F G) (program := SmallSumcheck.program)
    (SmallSumcheckProducerRoot.producer raw count handle shape bounded producerHistory)
    (SmallSumcheckValidatorRoot.validator raw scalar count handle validatorHistory) oracle state services) :=
  Original.executePair_eq (model := ringModel F G) (program := SmallSumcheck.program)
    (SmallSumcheckProducerRoot.producer raw count handle shape bounded producerHistory)
    (SmallSumcheckValidatorRoot.validator raw scalar count handle validatorHistory) oracle state services

end Small

namespace Two

/-- The same pair transport composes the two source-selected library calls
on each side, retaining their separate full original ABI and shared history. -/
theorem execute_pair (leftRaw rightRaw : List F) (leftScalar rightScalar : F)
    (count handle : Nat)
    (leftShape : PrimitiveLibrary.HasShape leftRaw count 1) (leftBound : leftRaw.length < indexLimit)
    (rightShape : PrimitiveLibrary.HasShape rightRaw count 1) (rightBound : rightRaw.length < indexLimit)
    (producerHistory validatorHistory : Domain.History (uniformCarriers F G))
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m (uniformCarriers F G) S) (state : S)
    (services : Domain.LocalServices m (uniformCarriers F G) S) : type_of% (
  Original.executePair_eq (model := ringModel F G) (program := TwoSums.program)
    (TwoSumsProducerRoot.producer leftRaw rightRaw count handle leftShape leftBound rightShape rightBound producerHistory)
    (TwoSumsValidatorRoot.validator leftRaw rightRaw leftScalar rightScalar count handle validatorHistory) oracle state services) :=
  Original.executePair_eq (model := ringModel F G) (program := TwoSums.program)
    (TwoSumsProducerRoot.producer leftRaw rightRaw count handle leftShape leftBound rightShape rightBound producerHistory)
    (TwoSumsValidatorRoot.validator leftRaw rightRaw leftScalar rightScalar count handle validatorHistory) oracle state services

end Two

end TestsSecurity.OriginalPairExecution
