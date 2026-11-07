module

public import Zkc.Construction.Participant

@[expose] public section

/-! Ordered observations from the native proof descriptor. A message retains
its transmission codec. Index draws retain their exclusive bound. -/
namespace Zkc.Executable.Descriptor

inductive Observation where
  | message (payload codec : String)
  | draw
  | index (bound : Nat)
  deriving DecidableEq, Repr

structure Event where
  template : Construction.Template
  observation : Observation
  deriving DecidableEq, Repr

end Zkc.Executable.Descriptor
