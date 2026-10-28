import Tests.ConnectionSymbolicRepeat

/-! A role-private carried component stays in logical state but has no native
cell. The callback and certificate are independent of the runtime count. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionProjectedRepeat
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate

def spec : RepeatSpec := ⟨[.boolean,.boolean], [], [0,1], [[0],[1]], 2⟩
def callback : Region protocolDialect [.index,.boolean,.boolean] [.boolean,.boolean] :=
  .ret (.cons (.there .here) (.cons (.there (.there .here)) .nil))
def signature : ProtocolSignature :=
  ⟨"privateRepeat", ["P","V"], [.index,.boolean,.boolean], [.boolean,.boolean],
    [[0,1],[0],[1]], [[0],[1]]⟩
def body : Region protocolDialect signature.inputs signature.outputs :=
  .letOp (.mark "loop") .nil .nil <|
  .letOp (.repeat spec "loop") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    (.cons callback .nil) <|
  .ret (.cons .here (.cons (.there .here) .nil))
def source : CheckedProtocol := .ofBody signature body
def pattern : InputPattern signature.inputs := .cons .present (.cons .absent (.cons .present .nil))
def layout : Layout pattern.scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here)))]
def routing : Original.Routing := Tests.ConnectionSymbolicRepeat.routing
  Tests.ConnectionSymbolicRepeat.plainContext
def target (count : Nat := 0) (yielded : Nat := 3) : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.loop 2 [yielded] count [1] [.data .boolean] Domain.View.empty)
    Domain.View.empty

def accepted : Certificate routing {} [] 1 2 source pattern [.absent,.data 2] none [] layout (target 0 3) := by
  derive_connection_alignment

example : accepted.alignment.size = 3 := rfl

-- Returning a different cell, using a different count, or yielding the loop
-- index must fail even when some concrete run happens to make values equal.
example : True := by
  fail_if_success
    have : Certificate routing {} [] 1 2 source pattern [.absent,.data 1] none [] layout (target 0 3) := by
      derive_connection_alignment
  trivial
example : True := by
  fail_if_success
    have : Certificate routing {} [] 1 2 source pattern [.absent,.data 2] none [] layout (target 1 3) := by
      derive_connection_alignment
  trivial
example : True := by
  fail_if_success
    have : Certificate routing {} [] 1 2 source pattern [.absent,.data 2] none [] layout (target 0 2) := by
      derive_connection_alignment
  trivial
example : True := by
  fail_if_success
    have : Certificate routing {} [] 1 2 source pattern [.data 2,.data 2] none [] layout (target 0 3) := by
      derive_connection_alignment
  trivial

#print axioms accepted
#print axioms Original.Simulation.projectedFramedRepeat
end Tests.ConnectionProjectedRepeat
