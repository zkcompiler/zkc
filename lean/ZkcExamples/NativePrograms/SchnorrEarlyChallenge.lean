module

public import Aesop
public import Lean
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Ring
public import Zkc.Protocols.Schnorr.Common
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeView
public import ZkcTools.ProcessView

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
noncomputable section
namespace ZkcExamples.NativePrograms.SchnorrEarlyChallenge
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Schnorr.Common

abbrev program := ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeInputs.program
abbrev imported := ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeInputs.imported

def wiring : Wiring := ⟨0, "bls12-381.g1", "bls12-381.fr", "label_636f6d6d69746d656e74_0", "label_6368616c6c656e6765", "label_64656c6976657279_0", "label_726573706f6e7365_0"⟩
variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def inputs (base key : G) (service : Nat) : Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some base) (.cons (some key) (.cons none (.cons none (.cons (some service) (.nil)))))

/-- The derived scalar observation of the actual typed Structured participant. -/
def verifier (base key : G) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F G) (Option Bool) :=
  ((program.participant F G 1 (inputs (F := F) (G := G) base key service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

noncomputable def processView (base key : G) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F G) (Option Bool) :=
  process_view% ((ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeView.view (F := F) (G := G) (base) (key) (service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

theorem process_view_eq (base key : G) (service : Nat) :
    verifier (F := F) (G := G) base key service = processView (F := F) (G := G) base key service := by
  unfold verifier
  change ((program.participant F G 1
    (ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeView.inputs (F := F) (G := G) (base) (key) (service))).bind _).interpret _ = _
  rw [ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeView.source_equation]
  rfl

end ZkcExamples.NativePrograms.SchnorrEarlyChallenge
end
