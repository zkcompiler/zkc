import Zkc.Compiler.Analysis.Observation
import Zkc.Compiler.Analysis.Sampling
import Zkc.Semantics.Locality

/-! Direct-channel locality for structural sampling analysis.

A sample node contains its ordinary argument expression, including a bounded
sampler's bound. Its provider reply is a separate boundary input. Fixing that
input says nothing about its distribution or its dependence on provider history.
Native extraction, provider conformance and exact absorption are separate checks.
-/

namespace Zkc.Compiler.Analysis.SamplingLocality

variable {Origin Value Operator : Type}

inductive Input (Origin : Type)
  | entry : Origin → Input Origin
  | receive : Origin → Input Origin
  | sample : Origin → Input Origin

inductive Expression (Origin Operator : Type)
  | input : Input Origin → Expression Origin Operator
  | apply : Operator → Expression Origin Operator → Expression Origin Operator →
      Expression Origin Operator
  | sample : Origin → Expression Origin Operator → Expression Origin Operator

def uses : Expression Origin Operator → Input Origin → Prop
  | .input source, key => key = source
  | .apply _ left right, key => uses left key ∨ uses right key
  | .sample event arguments, key => key = .sample event ∨ uses arguments key

def evaluate (operations : Operator → Value → Value → Value)
    (sampling : Origin → Value → Value → Value)
    (environment : Input Origin → Value) : Expression Origin Operator → Value
  | .input source => environment source
  | .apply op left right => operations op (evaluate operations sampling environment left)
      (evaluate operations sampling environment right)
  | .sample event arguments => sampling event (environment (.sample event))
      (evaluate operations sampling environment arguments)

theorem evaluate_agrees (operations : Operator → Value → Value → Value)
    (sampling : Origin → Value → Value → Value)
    (expression : Expression Origin Operator) (a b : Input Origin → Value)
    (same : ∀ source, uses expression source → a source = b source) :
    evaluate operations sampling a expression = evaluate operations sampling b expression := by
  induction expression with
  | input source => exact same source rfl
  | apply op left right ihLeft ihRight =>
      change operations op (evaluate operations sampling a left) (evaluate operations sampling a right) = _
      rw [ihLeft (fun source h => same source (Or.inl h)),
          ihRight (fun source h => same source (Or.inr h))]
      rfl
  | sample event arguments ih =>
      change sampling event (a (.sample event)) (evaluate operations sampling a arguments) = _
      rw [same (.sample event) (Or.inl rfl), ih (fun source h => same source (Or.inr h))]
      rfl

def localView (expression : Expression Origin Operator)
    (environment : Input Origin → Value) (source : {s // uses expression s}) : Value :=
  environment source.val

theorem evaluation_factors_through_view (operations : Operator → Value → Value → Value)
    (sampling : Origin → Value → Value → Value) (expression : Expression Origin Operator) :
    Zkc.Semantics.Locality.FiberConstant (localView expression)
      (fun environment => evaluate operations sampling environment expression) := by
  intro a b same
  apply evaluate_agrees operations sampling expression a b
  intro source present
  exact congrFun same ⟨source, present⟩

def NoDirectReception (expression : Expression Origin Operator) : Prop :=
  ∀ origin, ¬ uses expression (.receive origin)

/-- Direct support includes sampler arguments. Fixing provider replies cannot
hide a received bound. Successful sampling, independence and entropy are not
conclusions of this theorem. -/
theorem direct_channel (operations : Operator → Value → Value → Value)
    (sampling : Origin → Value → Value → Value)
    (expression : Expression Origin Operator) (a b : Input Origin → Value)
    (noReception : NoDirectReception expression)
    (entries : ∀ origin, a (.entry origin) = b (.entry origin))
    (samples : ∀ origin, a (.sample origin) = b (.sample origin)) :
    evaluate operations sampling a expression = evaluate operations sampling b expression := by
  apply evaluate_agrees operations sampling expression a b
  intro source present
  cases source with
  | entry origin => exact entries origin
  | sample origin => exact samples origin
  | receive origin => exact False.elim (noReception origin present)

/-- The expression extractor's direct-reception component uses the same
transfer functions as the separate sampling abstraction. Provider history is
outside this continuation expression; it is not erased by a security theorem. -/
def provenance : Expression Origin Operator → Sampling.Provenance Origin
  | .input (.entry _) => Sampling.empty
  | .input (.receive event) => Sampling.reception event
  | .input (.sample event) => Sampling.sample event Sampling.empty Sampling.empty
  | .apply _ left right => Sampling.join (provenance left) (provenance right)
  | .sample event arguments => Sampling.sample event Sampling.empty (provenance arguments)

theorem received_support (expression : Expression Origin Operator) (origin : Origin) :
    (provenance expression).received origin ↔ uses expression (.receive origin) := by
  induction expression with
  | input source =>
      cases source <;> simp [provenance, uses, Sampling.empty, Sampling.reception, Sampling.sample]
  | apply op left right ihLeft ihRight =>
      exact or_congr ihLeft ihRight
  | sample event arguments ih =>
      simpa [provenance, Sampling.sample, uses] using ih

def DirectChannelInvariant (operations : Operator → Value → Value → Value)
    (sampling : Origin → Value → Value → Value)
    (expression : Expression Origin Operator) : Prop :=
  ∀ a b, (∀ origin, a (.entry origin) = b (.entry origin)) →
    (∀ origin, a (.sample origin) = b (.sample origin)) →
    evaluate operations sampling a expression = evaluate operations sampling b expression

/-- A sound over-approximation of direct reception discharges locality. The
native analyzer still has to supply its own extraction/correspondence evidence. -/
theorem direct_support_summary (operations : Operator → Value → Value → Value)
    (sampling : Origin → Value → Value → Value) :
    SummarySound (DirectChannelInvariant (Origin := Origin) operations sampling)
      provenance (fun summary property => (∀ origin, ¬ summary.received origin) → property) := by
  intro expression absent a b entries samples
  apply direct_channel operations sampling expression a b _ entries samples
  intro origin used
  exact absent origin ((received_support expression origin).mpr used)

end Zkc.Compiler.Analysis.SamplingLocality
