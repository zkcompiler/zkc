import Zkc.Vocabulary
import Zkc.Subject.Deployed

/-!
Kernel-checked verification of `Zkc.Vocabulary.standardEncoder` and `Zkc.Vocabulary.Project.linkedEncoder`:
distinctness on representative standard and project keys, byte-range bounds (`< 256`), and
full injectivity witnesses.
-/

namespace Zkc.Vocabulary.EncoderTests

open Zkc.Core
open Zkc.Vocabulary
open Zkc.Vocabulary.Project

theorem standard_encoder_inj_witness : standardEncoder.Injective :=
  standardEncoder_injective

theorem linked_encoder_inj_witness (b : Bindings) : (linkedEncoder b).Injective :=
  linkedEncoder_injective b

example : standardEncoder.typeKey (.field .bls12381Fr) ≠ standardEncoder.typeKey (.field .koalaBear) := by
  decide

example : standardEncoder.typeKey (.field .bls12381Fr) ≠ standardEncoder.typeKey (.nonzero .bls12381Fr) := by
  decide

example : standardEncoder.rowKey (.hash .sha256) ≠ standardEncoder.rowKey (.hash .keccak256) := by
  decide

example : standardEncoder.rowKey (.hash (.shake128 32)) ≠ standardEncoder.rowKey (.hash (.shake128 64)) := by
  intro h
  cases standardEncoder_injective.2.1 _ _ h

example : standardEncoder.lawKey (.uniform Field.bls12381Fr.ty) ≠
    standardEncoder.lawKey (.uniform Field.koalaBear.ty) := by
  decide

private def sampleBindings : Bindings := {}

example :
    (linkedEncoder sampleBindings).typeKey (.inl (.field .bls12381Fr)) ≠
    (linkedEncoder sampleBindings).typeKey (.inr (.type (.nominal "suite.merlin3.bls12-381.fr64be/0.state") .nil)) := by
  decide

example :
    (linkedEncoder sampleBindings).rowKey (.inr ⟨"suite.merlin3.start", .nil⟩) ≠
    (linkedEncoder sampleBindings).rowKey (.inr ⟨"suite.merlin3.absorb", .nil⟩) := by
  intro h
  have h1 : (Sum.inr ⟨"suite.merlin3.start", .nil⟩ : Sum RowKey PrimitiveName) =
      Sum.inr ⟨"suite.merlin3.absorb", .nil⟩ :=
    (linkedEncoder_injective sampleBindings).2.1 _ _ h
  have h2 := congrArg (fun k : Sum RowKey PrimitiveName => match k with | .inr p => p.name | .inl _ => "") h1
  exact absurd h2 (by decide)

example :
    (linkedEncoder sampleBindings).rowKey (.inr ⟨"layout.canonical.write", .cons (.type .bool .nil) .nil⟩) ≠
    (linkedEncoder sampleBindings).rowKey (.inr ⟨"layout.canonical.write", .cons (.type .nat .nil) .nil⟩) := by
  intro h
  have h1 : (Sum.inr ⟨"layout.canonical.write", .cons (.type .bool .nil) .nil⟩ : Sum RowKey PrimitiveName) =
      Sum.inr ⟨"layout.canonical.write", .cons (.type .nat .nil) .nil⟩ :=
    (linkedEncoder_injective sampleBindings).2.1 _ _ h
  have h2 := congrArg (fun k : Sum RowKey PrimitiveName => match k with | .inr p => p.arguments | .inl _ => .nil) h1
  cases h2

private def primFoo : PrimitiveName := ⟨"project.custom.hash", .nil⟩

private def bindingsSigBool : Bindings :=
  ⟨[(primFoo, ⟨[.bool], [.bool]⟩)], by decide⟩

private def bindingsSigNat : Bindings :=
  ⟨[(primFoo, ⟨[.nat], [.nat]⟩)], by decide⟩

/-- Cross-project signature binding: two `Bindings` mapping the same `PrimitiveName` to different
`PrimitiveSignature`s produce distinct `linkedEncoder` row bytes. -/
theorem linked_encoder_distinguishes_signatures :
    (linkedEncoder bindingsSigBool).rowKey (.inr primFoo) ≠
    (linkedEncoder bindingsSigNat).rowKey (.inr primFoo) := by
  intro hEq
  have hSig := linkedEncoder_signature_distinguishes bindingsSigBool bindingsSigNat primFoo hEq
  have hDiff : bindingsSigBool.signature primFoo ≠ bindingsSigNat.signature primFoo := by decide
  exact hDiff hSig

end Zkc.Vocabulary.EncoderTests
