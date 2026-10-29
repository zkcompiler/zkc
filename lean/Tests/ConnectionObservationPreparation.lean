import Tests.ConnectionSymbolicRepeat

/-! The compiler's post-action coordinate schedule at two nested symbolic
repeat indices. Both old fused schedules remain covered by the imported tests.
-/
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
noncomputable section
namespace Tests.ConnectionObservationPreparation
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate Tests.ConnectionSymbolicRepeat

def receivedInner (reversed : Bool := false) : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.receive "message" "message" "P" .index [.data .index]) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 11 (if reversed then 7 else 4) [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 12 (if reversed then 4 else 7) [.indices]) <|
  Domain.View.sequence (Domain.View.observe fsContext "suite" message 9 10 13 [.transcript "suite"]) Domain.View.empty

def receivedOuter (reversed : Bool := false) : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 4 [10,14] 1 [5,6] [.data .index, .transcript "suite"]
    (receivedInner reversed model)) Domain.View.empty

def receivedView (reversed : Bool := false) : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 3 [7,8] 0 [2,3] [.data .index, .transcript "suite"]
    (receivedOuter reversed model)) Domain.View.empty

def received : Certificate (routing fsContext) {} [] 1 2 nestedDefinition pattern
    [.data 4] (some 5) [] fsLayout (receivedView false) := by derive_connection_alignment

def sentInner (reversed : Bool := false) : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.send "message" "message" "V" 8 []) <|
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 10 (if reversed then 7 else 4) [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 11 (if reversed then 4 else 7) [.indices]) <|
  Domain.View.sequence (Domain.View.observe fsContext "suite" message 9 8 12 [.transcript "suite"]) Domain.View.empty

def sentOuter (reversed : Bool := false) : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 4 [8,13] 1 [5,6] [.data .index, .transcript "suite"]
    (sentInner reversed model)) Domain.View.empty

def sentView (reversed : Bool := false) : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 3 [7,8] 0 [2,3] [.data .index, .transcript "suite"]
    (sentOuter reversed model)) Domain.View.empty

def sent : Certificate (routing fsContext .producer) {} [] 0 2 nestedDefinition pattern
    [.data 4] (some 5) [] fsLayout (sentView false) := by derive_connection_alignment

example : True := by
  fail_if_success
    have : Certificate (routing fsContext) {} [] 1 2 nestedDefinition pattern
        [.data 4] (some 5) [] fsLayout (receivedView true) := by derive_connection_alignment
  trivial
example : True := by
  fail_if_success
    have : Certificate (routing fsContext .producer) {} [] 0 2 nestedDefinition pattern
        [.data 4] (some 5) [] fsLayout (sentView true) := by derive_connection_alignment
  trivial

/-- The same physical history selector is mandatory at the final frame. -/
example : True := by
  fail_if_success
    have : Certificate (routing fsContext) {} [] 1 2 nestedDefinition pattern
        [.data 4] (some 4) [] fsLayout (receivedView false) := by derive_connection_alignment
  trivial

end Tests.ConnectionObservationPreparation
