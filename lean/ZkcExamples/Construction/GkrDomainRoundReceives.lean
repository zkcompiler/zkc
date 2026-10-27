module

public import ZkcExamples.Construction.GkrDomainRoundTail

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 400000
noncomputable section
namespace ZkcExamples.Construction.GkrDomainRoundReceives
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol GkrDomainRounds GkrDomainPhaseBinding GkrDomainRoundTail
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Metadata of this exact generated receive occurrence. -/
def leftTemplate0 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s57" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_6c656674" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s9" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0",             "label_726f756e64_0", "role00000000", "role00000001"] }

def leftOrigin0 (layerIndex index : Nat) : Origin :=
  Domain.atCoordinates (context.message (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "0") 0 1)
    [layerIndex, index]

theorem left_resolved0 (layerIndex index : Nat) :
    Domain.templateOrigin context leftTemplate0 [layerIndex, index] = some (leftOrigin0 layerIndex index) := by
  kernel_rfl

theorem left_projected0 (layerIndex index : Nat) :
    Origin.withoutCoordinates (leftOrigin0 layerIndex index) =
      context.message (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "0") 0 1 := by
  kernel_rfl

def leftReceive0 : Domain.View.Block (uniformCarriers F G) :=
  receiveBlock (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "0") 0 leftTemplate0
    54 53 40 50

/-- Metadata of this exact generated receive occurrence. -/
def leftTemplate1 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s57" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_6c656674" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s9" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1",             "label_726f756e64_1", "role00000000", "role00000001"] }

def leftOrigin1 (layerIndex index : Nat) : Origin :=
  Domain.atCoordinates (context.message (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "1") 0 1)
    [layerIndex, index]

theorem left_resolved1 (layerIndex index : Nat) :
    Domain.templateOrigin context leftTemplate1 [layerIndex, index] = some (leftOrigin1 layerIndex index) := by
  kernel_rfl

theorem left_projected1 (layerIndex index : Nat) :
    Origin.withoutCoordinates (leftOrigin1 layerIndex index) =
      context.message (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "1") 0 1 := by
  kernel_rfl

def leftReceive1 : Domain.View.Block (uniformCarriers F G) :=
  receiveBlock (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "1") 0 leftTemplate1
    59 58 40 50

/-- Metadata of this exact generated receive occurrence. -/
def leftTemplate2 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s57" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_6c656674" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s9" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2",             "label_726f756e64_2", "role00000000", "role00000001"] }

def leftOrigin2 (layerIndex index : Nat) : Origin :=
  Domain.atCoordinates (context.message (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "2") 0 1)
    [layerIndex, index]

theorem left_resolved2 (layerIndex index : Nat) :
    Domain.templateOrigin context leftTemplate2 [layerIndex, index] = some (leftOrigin2 layerIndex index) := by
  kernel_rfl

theorem left_projected2 (layerIndex index : Nat) :
    Origin.withoutCoordinates (leftOrigin2 layerIndex index) =
      context.message (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "2") 0 1 := by
  kernel_rfl

def leftReceive2 : Domain.View.Block (uniformCarriers F G) :=
  receiveBlock (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "2") 0 leftTemplate2
    64 63 40 50


def leftPrefix0 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep0 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep1 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep2 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep3 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep4 (ringModel F G) program context]

theorem left_prefix0_identity :
    sequenceBlocks (leftPrefix0 (F := F) (G := G)) = leftReceive0 := by
  kernel_rfl

def leftPrefix1 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep5 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep6 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep7 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep8 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep9 (ringModel F G) program context]

theorem left_prefix1_identity :
    sequenceBlocks (leftPrefix1 (F := F) (G := G)) = leftReceive1 := by
  kernel_rfl

def leftPrefix2 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep10 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep11 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep12 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep13 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep3BodyStep14 (ringModel F G) program context]

theorem left_prefix2_identity :
    sequenceBlocks (leftPrefix2 (F := F) (G := G)) = leftReceive2 := by
  kernel_rfl

/-- Partition the actual generated callback at the receive boundaries.
The existing handler removes checkpoints before these blocks compose. -/
theorem left_decomposition (env : Env (F := F) (G := G)) :
    (Generated.Constructed.GkrValidator.bodyStep37BodyStep3Body (ringModel F G) program context env).interpret operations =
      ((leftReceive0 env).interpret operations).bind fun first =>
      ((leftReceive1 first).interpret operations).bind fun second =>
      ((leftReceive2 second).interpret operations).bind fun third =>
      (leftTail third).interpret operations := by
  change (sequenceBlocks (leftPrefix0 ++ (leftPrefix1 ++ (leftPrefix2 ++ leftTailBlocks))) env).interpret operations = _
  simp only [sequenceBlocks_append, left_prefix0_identity, left_prefix1_identity,
    left_prefix2_identity, leftTail]

/-- Metadata of this exact generated receive occurrence. -/
def rightTemplate0 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s57" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_7269676874" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s9" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0",             "label_726f756e64_0", "role00000000", "role00000001"] }

def rightOrigin0 (layerIndex index : Nat) : Origin :=
  Domain.atCoordinates (context.message (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "0") 0 1)
    [layerIndex, index]

theorem right_resolved0 (layerIndex index : Nat) :
    Domain.templateOrigin context rightTemplate0 [layerIndex, index] = some (rightOrigin0 layerIndex index) := by
  kernel_rfl

theorem right_projected0 (layerIndex index : Nat) :
    Origin.withoutCoordinates (rightOrigin0 layerIndex index) =
      context.message (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "0") 0 1 := by
  kernel_rfl

def rightReceive0 : Domain.View.Block (uniformCarriers F G) :=
  receiveBlock (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "0") 0 rightTemplate0
    61 60 40 57

/-- Metadata of this exact generated receive occurrence. -/
def rightTemplate1 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s57" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_7269676874" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s9" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1",             "label_726f756e64_1", "role00000000", "role00000001"] }

def rightOrigin1 (layerIndex index : Nat) : Origin :=
  Domain.atCoordinates (context.message (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "1") 0 1)
    [layerIndex, index]

theorem right_resolved1 (layerIndex index : Nat) :
    Domain.templateOrigin context rightTemplate1 [layerIndex, index] = some (rightOrigin1 layerIndex index) := by
  kernel_rfl

theorem right_projected1 (layerIndex index : Nat) :
    Origin.withoutCoordinates (rightOrigin1 layerIndex index) =
      context.message (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "1") 0 1 := by
  kernel_rfl

def rightReceive1 : Domain.View.Block (uniformCarriers F G) :=
  receiveBlock (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "1") 0 rightTemplate1
    66 65 40 57

/-- Metadata of this exact generated receive occurrence. -/
def rightTemplate2 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s57" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_7269676874" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s9" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2",             "label_726f756e64_2", "role00000000", "role00000001"] }

def rightOrigin2 (layerIndex index : Nat) : Origin :=
  Domain.atCoordinates (context.message (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "2") 0 1)
    [layerIndex, index]

theorem right_resolved2 (layerIndex index : Nat) :
    Domain.templateOrigin context rightTemplate2 [layerIndex, index] = some (rightOrigin2 layerIndex index) := by
  kernel_rfl

theorem right_projected2 (layerIndex index : Nat) :
    Origin.withoutCoordinates (rightOrigin2 layerIndex index) =
      context.message (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "2") 0 1 := by
  kernel_rfl

def rightReceive2 : Domain.View.Block (uniformCarriers F G) :=
  receiveBlock (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "2") 0 rightTemplate2
    71 70 40 57


def rightPrefix0 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep0 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep1 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep2 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep3 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep4 (ringModel F G) program context]

theorem right_prefix0_identity :
    sequenceBlocks (rightPrefix0 (F := F) (G := G)) = rightReceive0 := by
  kernel_rfl

def rightPrefix1 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep5 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep6 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep7 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep8 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep9 (ringModel F G) program context]

theorem right_prefix1_identity :
    sequenceBlocks (rightPrefix1 (F := F) (G := G)) = rightReceive1 := by
  kernel_rfl

def rightPrefix2 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep10 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep11 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep12 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep13 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep37BodyStep6BodyStep14 (ringModel F G) program context]

theorem right_prefix2_identity :
    sequenceBlocks (rightPrefix2 (F := F) (G := G)) = rightReceive2 := by
  kernel_rfl

/-- Partition the actual generated callback at the receive boundaries.
The existing handler removes checkpoints before these blocks compose. -/
theorem right_decomposition (env : Env (F := F) (G := G)) :
    (Generated.Constructed.GkrValidator.bodyStep37BodyStep6Body (ringModel F G) program context env).interpret operations =
      ((rightReceive0 env).interpret operations).bind fun first =>
      ((rightReceive1 first).interpret operations).bind fun second =>
      ((rightReceive2 second).interpret operations).bind fun third =>
      (rightTail third).interpret operations := by
  change (sequenceBlocks (rightPrefix0 ++ (rightPrefix1 ++ (rightPrefix2 ++ rightTailBlocks))) env).interpret operations = _
  simp only [sequenceBlocks_append, right_prefix0_identity, right_prefix1_identity,
    right_prefix2_identity, rightTail]

end ZkcExamples.Construction.GkrDomainRoundReceives
