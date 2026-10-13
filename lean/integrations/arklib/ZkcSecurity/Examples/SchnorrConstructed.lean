module

public import Zkc.Protocols.Schnorr.NativeConstruction
public import ZkcSecurity.Examples.SchnorrConstructedData
public import ZkcSecurity.Examples.SchnorrFiatShamir

@[expose] public section

/-! Security connection for one actual exported constructed Schnorr participant.
The canonical interpretation is explicit; the retained native descriptor is Merlin.
-/
namespace ZkcSecurity.Examples.SchnorrConstructed
open Zkc.Source Zkc.Protocols.Schnorr
open Zkc.Protocols.Schnorr.Construction
open ZkcSecurity.VCVio.Schnorr.FiatShamir
open ZkcExamples.NativePrograms

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def imported : Constructed.Imported SchnorrConstructedData.snapshot :=
  SchnorrConstructedData.imported

theorem source_identity : SchnorrConstructedData.snapshot.source =
    Variants.SchnorrHelpersData.snapshot.source := rfl

/-- Select public bindings from the retained actual source and candidate identities. -/
def publicBinding {Context G : Type} (context : Context) (base key : G) :
    Binding (Constructed.OccurrenceContext Context) G :=
  SchnorrConstructedData.binding context base key

variable {Context F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def actual : Construction.Verifier Context F G :=
  NativeConstruction.verifier imported rfl rfl

/-- This normalizes the actual admitted instruction sequence, retaining the full
returned transcript. No assumption identifies a lookalike verifier with this body. -/
theorem full_denotation (binding : Binding Context G) (proof : G × F) :
    imported.denote (NativeConstruction.meaning proof) (NativeConstruction.inputs binding) =
      .call (binding, proof.1) (fun (challenge : F) =>
        .done (.cons (decide (proof.2 • binding.base = proof.1 + challenge • binding.key))
          (.cons (⟨binding, some proof.1, some challenge, true, some proof.2⟩ :
            NativeConstruction.Transcript Context F G) .nil))) :=
  SchnorrConstructedData.full_denotation binding proof

/-- The result projection realizes the concrete construction of the imported
Helpers source. Its actual algebra and state operands were used above. -/
theorem realizes : Realizes (actual (Context := Context) (F := F) (G := G))
    (SchnorrVariants.verifier .helpers) 0 := by
  intro binding proof
  constructor
  change (imported.denote (NativeConstruction.meaning proof) (NativeConstruction.inputs binding)).bind
    (fun reply => .done (NativeConstruction.result reply)) = _
  rw [full_denotation, construct_eq (SchnorrVariants.contract .helpers)]
  rfl

variable [SampleableType F] [DecidableEq Context] [Fintype F] [Inhabited F]

/-- Actual exported participant, proved construction, source contract, named game. -/
theorem extraction (prover : Prover Context F G) (binding : Binding Context G) (budget : Nat)
    (queryBound : _root_.FiatShamir.nmaHashQueryBound (Binding Context G)
      (prover binding.key binding) budget) :
    let acc := acceptance actual prover binding
    acc * (acc / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← extractor prover binding budget}[witness • binding.base = binding.key] :=
  ZkcSecurity.VCVio.Schnorr.FiatShamir.extraction
    (SchnorrVariants.contract .helpers) realizes prover binding budget queryBound

/-- This consumer fixes source and constructed-candidate identity from the
retained export. The host still supplies the stated application and group inputs. -/
theorem source_bound_extraction (prover : Prover (Constructed.OccurrenceContext Context) F G)
    (context : Context)
    (base key : G) (budget : Nat)
    (queryBound : _root_.FiatShamir.nmaHashQueryBound
      (Binding (Constructed.OccurrenceContext Context) G)
      (prover key (publicBinding context base key)) budget) :
    let binding := publicBinding context base key
    let acc := acceptance actual prover binding
    acc * (acc / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← extractor prover binding budget}[witness • base = key] :=
  extraction prover (publicBinding context base key) budget queryBound

end ZkcSecurity.Examples.SchnorrConstructed
