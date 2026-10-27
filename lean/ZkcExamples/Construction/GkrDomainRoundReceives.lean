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
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s23" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_6c656674" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s6" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0",             "label_726f756e64_0", "role00000000", "role00000001"] }

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
    21 20 12 17

/-- Metadata of this exact generated receive occurrence. -/
def leftTemplate1 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s23" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_6c656674" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s6" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1",             "label_726f756e64_1", "role00000000", "role00000001"] }

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
    26 25 12 17

/-- Metadata of this exact generated receive occurrence. -/
def leftTemplate2 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s23" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_6c656674" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s6" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2",             "label_726f756e64_2", "role00000000", "role00000001"] }

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
    31 30 12 17


def leftPrefix0 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep0 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep1 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep2 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep3 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep4 (ringModel F G) program context]

theorem left_prefix0_identity :
    sequenceBlocks (leftPrefix0 (F := F) (G := G)) = leftReceive0 := by
  kernel_rfl

def leftPrefix1 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep5 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep6 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep7 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep8 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep9 (ringModel F G) program context]

theorem left_prefix1_identity :
    sequenceBlocks (leftPrefix1 (F := F) (G := G)) = leftReceive1 := by
  kernel_rfl

def leftPrefix2 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep10 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep11 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep12 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep13 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep1BodyStep14 (ringModel F G) program context]

theorem left_prefix2_identity :
    sequenceBlocks (leftPrefix2 (F := F) (G := G)) = leftReceive2 := by
  kernel_rfl

/-- Partition the actual generated callback at the receive boundaries.
The existing handler removes checkpoints before these blocks compose. -/
theorem left_decomposition (env : Env (F := F) (G := G)) :
    (Generated.Constructed.GkrValidator.bodyStep3BodyStep1Body (ringModel F G) program context env).interpret operations =
      ((leftReceive0 env).interpret operations).bind fun first =>
      ((leftReceive1 first).interpret operations).bind fun second =>
      ((leftReceive2 second).interpret operations).bind fun third =>
      (leftTail third).interpret operations := by
  change (sequenceBlocks (leftPrefix0 ++ (leftPrefix1 ++ (leftPrefix2 ++ leftTailBlocks))) env).interpret operations = _
  simp only [sequenceBlocks_append, left_prefix0_identity, left_prefix1_identity,
    left_prefix2_identity, leftTail]

/-- Metadata of this exact generated receive occurrence. -/
def rightTemplate0 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s23" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_7269676874" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s6" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0",             "label_726f756e64_0", "role00000000", "role00000001"] }

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
    25 24 12 21

/-- Metadata of this exact generated receive occurrence. -/
def rightTemplate1 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s23" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_7269676874" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s6" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1",             "label_726f756e64_1", "role00000000", "role00000001"] }

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
    30 29 12 21

/-- Metadata of this exact generated receive occurrence. -/
def rightTemplate2 : Template :=
  { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",   steps := [{ kind := "repeat",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "s23" },             { kind := "apply",               protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2",               site := "label_7269676874" },             { kind := "repeat",               protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba",               site := "s6" }],   event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2",             "label_726f756e64_2", "role00000000", "role00000001"] }

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
    35 34 12 21


def rightPrefix0 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep0 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep1 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep2 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep3 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep4 (ringModel F G) program context]

theorem right_prefix0_identity :
    sequenceBlocks (rightPrefix0 (F := F) (G := G)) = rightReceive0 := by
  kernel_rfl

def rightPrefix1 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep5 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep6 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep7 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep8 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep9 (ringModel F G) program context]

theorem right_prefix1_identity :
    sequenceBlocks (rightPrefix1 (F := F) (G := G)) = rightReceive1 := by
  kernel_rfl

def rightPrefix2 : List (Domain.View.Block (uniformCarriers F G)) :=
  [Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep10 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep11 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep12 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep13 (ringModel F G) program context,
   Generated.Constructed.GkrValidator.bodyStep3BodyStep3BodyStep14 (ringModel F G) program context]

theorem right_prefix2_identity :
    sequenceBlocks (rightPrefix2 (F := F) (G := G)) = rightReceive2 := by
  kernel_rfl

/-- Partition the actual generated callback at the receive boundaries.
The existing handler removes checkpoints before these blocks compose. -/
theorem right_decomposition (env : Env (F := F) (G := G)) :
    (Generated.Constructed.GkrValidator.bodyStep3BodyStep3Body (ringModel F G) program context env).interpret operations =
      ((rightReceive0 env).interpret operations).bind fun first =>
      ((rightReceive1 first).interpret operations).bind fun second =>
      ((rightReceive2 second).interpret operations).bind fun third =>
      (rightTail third).interpret operations := by
  change (sequenceBlocks (rightPrefix0 ++ (rightPrefix1 ++ (rightPrefix2 ++ rightTailBlocks))) env).interpret operations = _
  simp only [sequenceBlocks_append, right_prefix0_identity, right_prefix1_identity,
    right_prefix2_identity, rightTail]

end ZkcExamples.Construction.GkrDomainRoundReceives
