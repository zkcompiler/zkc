module

public import ZkcExamples.Construction.GkrSourceProtocol
public import Zkc.Construction.Uniform.OccurrenceSourceProcess
public import Zkc.Construction.OccurrenceReindex
public meta import Zkc.Source.KernelRfl

@[expose] public section

/-! Source-owned delivery and occurrence routes for the current GKR entry.
Discovery proposes paths; the existing source resolver checks each path and
its exact dynamic repeat stack before any nominal oracle is called. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrSourceRouting
open Zkc.Source Zkc.Source.Structured Zkc.Construction

abbrev context := GkrSourceProtocol.context
abbrev snapshot := ZkcExamples.Structured.GkrSourceData.snapshot

def template0 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s37" }], event := ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f7574707574", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"] }

def template1 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s37" }], event := ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f75747075745f64656c6976657279_0", "label_6f75747075745f64656c6976657279_0", "role00000001", "role00000000"] }

def template2 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_6c656674" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"] }

def template3 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_6c656674" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"] }

def template4 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_6c656674" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"] }

def template5 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_6c656674" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"] }

def template6 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_6c656674" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"] }

def template7 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_7269676874" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"] }

def template8 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_7269676874" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"] }

def template9 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_7269676874" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"] }

def template10 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_7269676874" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"] }

def template11 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "apply", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "label_7269676874" }, { kind := "repeat", protocol := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", site := "s9" }], event := ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"] }

def template12 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }], event := ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f6e7374616e74_0", "label_6c696e655f636f6e7374616e74_0", "role00000000", "role00000001"] }

def template13 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }, { kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s91" }], event := ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f656666696369656e74_0", "label_6c696e655f636f656666696369656e74_0", "role00000000", "role00000001"] }

def template14 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }], event := ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"] }

def template15 : Template := { entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", steps := [{ kind := "repeat", protocol := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", site := "s57" }], event := ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f64656c6976657279_0", "label_6c696e655f64656c6976657279_0", "role00000001", "role00000000"] }

def templates : List Template := [template0, template1, template2, template3, template4, template5, template6, template7, template8, template9, template10, template11, template12, template13, template14, template15]


def deliveries : List Original.Delivery :=
  [⟨template0, template1⟩, ⟨template5, template6⟩,
   ⟨template10, template11⟩, ⟨template14, template15⟩]

def routing (handle : Nat) (mode : Domain.Mode := .validator) : Original.Routing where
  snapshot := snapshot
  context := context
  mode := mode
  selectedHandle := handle
  messages := templates
  draws := templates
  deliveries := deliveries


/-- The two applications have distinct complete source paths, including their
shared enclosing layer and their own inner round coordinate. -/
inductive Side where
  | left
  | right
  deriving DecidableEq

def roundContext : Side → ProtocolContext
  | .left => ZkcExamples.Structured.GkrVerifier.leftContext {}
  | .right => ZkcExamples.Structured.GkrVerifier.rightContext {}

def roundFrames (side : Side) (layer index : Nat) : Original.Frames :=
  [⟨"s57", layer⟩, ⟨qualifyProtocolSite (roundContext side).applicationPrefix "s9", index⟩]


end ZkcExamples.Construction.GkrSourceRouting
