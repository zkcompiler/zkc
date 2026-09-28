import Zkc.Source.Mathematical.DataBounds
import Tests.MathematicalGraph
import Zkc.Source.Mathematical.ProtocolAdmission

set_option autoImplicit false
namespace Tests.MathematicalProtocol
open Zkc.Source Zkc.Source.Mathematical
open MathematicalGraph (Ty number publicPort privatePort)

inductive Service where
  | counter | other
  deriving DecidableEq, Repr

inductive Local where
  | shared | distinct
  deriving DecidableEq, Repr

abbrev vocabulary : Protocol.Vocabulary where
  toAlgebra := { MathematicalGraph.algebra with Wire := fun _ => Unit }
  Service := Service
  serviceArguments := fun _ => [number]
  serviceResult := fun _ => number
  Local := Local
  localCapabilities := fun _ => [.counter, .counter]
  localArguments := fun _ => [number]
  localResult := fun _ => number
  localDistinct | .shared => [] | .distinct => [(0, 1)]

abbrev cap (service : Service) (roles : List Nat) (root : Nat) :
    Protocol.Capability Nat Service := ⟨⟨service, roles⟩, root⟩

def capabilities : List (Protocol.Capability Nat Service) :=
  [cap .counter [0] 7, cap .counter [0] 7, cap .counter [0, 1] 8, cap .other [0] 9]

def signature : Protocol.Signature Nat vocabulary :=
  ⟨[0], [⟨.counter, [0]⟩], [privatePort], [privatePort]⟩

def admit (Γ results : List (Port Nat Ty)) (raw : Protocol.Raw Nat vocabulary) :=
  Protocol.decode [0, 1] capabilities [signature] Data.capacity
    MathematicalGraph.countValid 64 Γ results 0 raw

def sites (Γ results : List (Port Nat Ty)) (raw : Protocol.Raw Nat vocabulary) :
    Except Protocol.Error (List Nat) := return (← admit Γ results raw).program.sites

example : sites [privatePort] [privatePort] (.query 0 0 0 [0] (.ret [0])) = .ok [0] := rfl
example : sites [privatePort] [privatePort] (.query 0 1 0 [0] (.ret [0])) = .error .permission := rfl
example : sites [⟨[1], number⟩] [privatePort] (.query 0 0 0 [0] (.ret [0])) = .error .permission := rfl
example : sites [privatePort] [privatePort] (.query 1 0 0 [0] (.ret [0])) = .error .site := rfl
example : sites [privatePort] [privatePort] (.query 0 2 0 [0] (.ret [0])) = .error .owner := rfl

-- Ports zero and one name the same state component. Their distinct indices
-- cannot discharge a registered requirement for two distinct roots.
example : sites [privatePort] [privatePort]
    (.local 0 0 .distinct [0, 1] [0] (.ret [0])) = .error .alias := rfl
example : sites [privatePort] [privatePort]
    (.local 0 0 .distinct [0, 2] [0] (.ret [0])) = .ok [0] := rfl
example : sites [privatePort] [privatePort]
    (.local 0 0 .shared [0, 0] [0] (.ret [0])) = .ok [0] := rfl
example : sites [privatePort] [privatePort]
    (.local 0 0 .shared [0, 3] [0] (.ret [0])) = .error .service := rfl

example : sites [privatePort] [privatePort]
    (.invoke 0 0 [2] [0] (.ret [0])) = .ok [0] := rfl
example : sites [privatePort] [privatePort]
    (.invoke 0 1 [2] [0] (.ret [0])) = .error (.graph .scope) := rfl
example : sites [privatePort] [privatePort]
    (.invoke 0 0 [3] [0] (.ret [0])) = .error .service := rfl

-- Reversed sender/receiver order still gives the canonical role set. The old
-- binding remains private; only the newly created message binding is shared.
example : sites [⟨[1], number⟩] [publicPort]
    (.message 0 ⟨number, ()⟩ 1 0 0 (.ret [0])) = .ok [0] := rfl
example : sites [⟨[1], number⟩] [publicPort]
    (.message 0 ⟨number, ()⟩ 1 0 0 (.ret [1])) = .error .permission := rfl
example : sites [privatePort] [privatePort]
    (.message 0 ⟨number, ()⟩ 0 0 0 (.ret [0])) = .error .sender := rfl

def repeated (count : Nat) : Protocol.Raw Nat vocabulary :=
  .repeat 0 count [privatePort] [0] []
    (.query 1 0 0 [1] (.ret [0]))
    (.message 2 ⟨number, ()⟩ 0 1 0 (.ret [0]))

example : sites [privatePort] [publicPort] (repeated 0) = .ok [0, 1, 2] := rfl
example : sites [privatePort] [publicPort] (repeated 1000000000) = .ok [0, 1, 2] := rfl
example : sites [privatePort] [privatePort]
    (.repeat 0 0 [privatePort] [0] [] (.query 2 0 0 [1] (.ret [0])) (.ret [0])) = .error .site := rfl
example : sites [privatePort, privatePort] [privatePort]
    (.repeat 0 0 [privatePort] [0] [] (.query 1 0 0 [2] (.ret [0])) (.ret [0])) =
    .error (.graph .scope) := rfl

-- Repeat returns may cover declared ports; this differs from a pure fold's
-- exact availability invariant. Explicit capture two supplies the public value.
example : sites [privatePort, publicPort] [privatePort]
    (.repeat 0 2 [privatePort] [0] [1] (.ret [2]) (.ret [0])) = .ok [0] := rfl
example : sites [privatePort] [privatePort]
    (.repeat 0 0 [privatePort] [0] [] (.stop 1 0 .reject) (.ret [0])) = .ok [0, 1] := rfl
example : sites [] [] (.stop 0 2 .abort) = .error .owner := rfl

example : sites [publicPort, publicPort] [publicPort]
    (.pure [0, 1] (.operation .add [0, 1] (.outputs [0])) (.ret [0])) = .ok [] := rfl
example : sites [publicPort, privatePort] [publicPort]
    (.pure [0, 1] (.operation .add [0, 1] (.outputs [0])) (.ret [0])) = .error .permission := rfl

example {Γ results raw result} (accepted : admit Γ results raw = .ok result) :
    result.program.erase = raw :=
  Protocol.decode_erases (vocabulary := vocabulary) [0, 1] capabilities [signature]
    Data.capacity MathematicalGraph.countValid (fuel := 64) accepted

example {Γ results raw result} (_accepted : admit Γ results raw = .ok result) :
    result.program.sites = List.range' 0 result.program.sites.length := result.program.sites_dense

end Tests.MathematicalProtocol
