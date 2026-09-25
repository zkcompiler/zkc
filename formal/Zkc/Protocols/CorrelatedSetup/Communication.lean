import Zkc.Protocols.CorrelatedSetup.Execution
import Zkc.Protocols.CorrelatedSetup.Source
import Zkc.Semantics.Boundary

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.CorrelatedSetup.Communication
open PIR Zkc.Probability.AdaptiveTape Zkc.Protocols.CorrelatedSetup.Service

variable {F : Type} [CommRing F] [DecidableEq F]

/-- The same Zkc.Source.Expressions-derived immutable coefficient cache is shared; draws and
    reply-dependent requests still occur at their original boundaries. -/
def cachedHandler (s : Setup F) (w : Witness F) (p : Triple F) (value : F × F) :
    Handler (Zkc.Protocols.CorrelatedSetup.Execution.sig F) (History F × List F) (Event F)
  | .stop, (h,tape) => ⟨.returned (),(⟨h.events ++ [.stopped],true⟩,tape),[.stopped]⟩
  | .request _, (h,[]) => ⟨.stopped .exhausted,(h,[]),[]⟩
  | .request req, (h,r :: rest) =>
      let reply := Zkc.Protocols.CorrelatedSetup.Execution.deliver req.cutAfterU
        (actualResponse s value req r) (tags s (publicationsOf w p)).2.2
      ⟨.returned reply,(Zkc.Protocols.CorrelatedSetup.Execution.receive h req reply,rest),[Zkc.Protocols.CorrelatedSetup.Execution.event req reply]⟩

omit [DecidableEq F] in
theorem cached_handler_exact (s : Setup F) (w : Witness F) (p : Triple F)
    (cache : CoefficientCache s w p) :
    cachedHandler s w p cache.value = Zkc.Protocols.CorrelatedSetup.Execution.handler s w p := by
  rw [cache.valid]
  rfl

omit [DecidableEq F] in
/-- Unlike the old History projection, this includes exhaustion, post-state,
    all previous emissions and arbitrary reply-adaptive client continuations. -/
theorem cached_execution_exact {A : Type} (s : Setup F) (w : Witness F) (p : Triple F)
    (cache : CoefficientCache s w p) (body : Proc (Zkc.Protocols.CorrelatedSetup.Execution.sig F) A)
    (state : History F × List F) :
    body.run (cachedHandler s w p cache.value) state =
      body.run (Zkc.Protocols.CorrelatedSetup.Execution.handler s w p) state := by
  rw [cached_handler_exact]

/-- Predeclared source edits: a new setup dependency, an additional permitted
    request, and changed partial delivery. No new optimizer is inferred. -/
inductive Edit where | baseline | capture | extraRequest | fullDelivery
  deriving DecidableEq, Repr

def code : Edit → Zkc.Protocols.CorrelatedSetup.Source.Program
  | .baseline => Zkc.Protocols.CorrelatedSetup.Source.adaptive
  | .capture => {Zkc.Protocols.CorrelatedSetup.Source.adaptive with challenge := .add (.add (.var 0) (.var 3)) (.var 5)}
  | .extraRequest => {Zkc.Protocols.CorrelatedSetup.Source.adaptive with
      stop := .ifz (.sub (.var 3) (.lit 3)) (.lit 0) (.lit 1)}
  | .fullDelivery => {Zkc.Protocols.CorrelatedSetup.Source.adaptive with cut := .lit 0}

theorem edits_checked (edit : Edit) : (code edit).Good := by
  cases edit <;> decide +kernel

def dependencies (c : Zkc.Protocols.CorrelatedSetup.Source.Program) : List Nat :=
  c.stop.deps ++ c.star.deps ++ c.challenge.deps ++ c.cut.deps

theorem capture_dependency_found :
    dependencies (code .baseline) = [3,4,0,3,4] ∧
    dependencies (code .capture) = [3,4,0,3,5,4] := ⟨rfl,rfl⟩

/-- Independently written direct-library controller for exactly the same edits.
    It has the same history, arithmetic, setup and cache capability. -/
def libraryController (edit : Edit) (s : Setup F) : Controller F := fun p h =>
  if (h.events.length : F) = (if edit = .extraRequest then 3 else 2) then none else
    some ⟨2 + Zkc.Protocols.CorrelatedSetup.Source.lastU h,
      p.1 + h.events.length + (if edit = .capture then s.delta else 0),
      if edit = .fullDelivery then false else decide (Zkc.Protocols.CorrelatedSetup.Source.lastU h ≠ 0)⟩

theorem controller_exact [Nontrivial F] (edit : Edit) (s : Setup F) (w : Witness F) :
    (code edit).denote s w = libraryController edit s := by
  funext p h
  cases edit <;>
    simp [code,Zkc.Protocols.CorrelatedSetup.Source.adaptive,Zkc.Protocols.CorrelatedSetup.Source.Program.denote,Zkc.Source.Expressions.Expr.eval,
      Zkc.Protocols.CorrelatedSetup.Source.inputs,libraryController,sub_eq_zero]

def generated (edit : Edit) (s : Setup F) (w : Witness F) (p : Triple F)
    (n : Nat) (history : History F) (tape : List F) :=
  (Zkc.Protocols.CorrelatedSetup.Execution.source ((code edit).denote s w) p n history).run
    (cachedHandler s w p (Zkc.Protocols.CorrelatedSetup.Source.sourceCache s w p).value) (history,tape)

def library (edit : Edit) (s : Setup F) (w : Witness F) (p : Triple F)
    (n : Nat) (history : History F) (tape : List F) :=
  (Zkc.Protocols.CorrelatedSetup.Execution.source (libraryController edit s) p n history).run
    (cachedHandler s w p (buildCache s w p).value) (history,tape)

/-- Equal complete executions, uniformly in public horizon and finite tape;
    no native timing or unique compiler capability follows from this equality. -/
theorem equally_capable [Nontrivial F] (edit : Edit) (s : Setup F) (w : Witness F) (p : Triple F)
    (n : Nat) (history : History F) (tape : List F) :
    generated edit s w p n history tape = library edit s w p n history tape := by
  unfold generated library
  rw [controller_exact,(Zkc.Protocols.CorrelatedSetup.Source.sourceCache s w p).valid]
  rfl


end Zkc.Protocols.CorrelatedSetup.Communication
