module

public import ZkcSecurity.Source.PublicProperties
public import ZkcSecurity.Source.LoopContracts
public meta import ZkcSecurity.Tools.SourceProperties.Loops

@[expose] public section

/-! An unrelated indexed source loop receives arbitrary public indices, may
refuse, and retains both iteration observations. No and cost use separate
contracts; a mutation of the recursion continuation cannot reuse either one. -/
set_option autoImplicit false
namespace TestsSecurity.SourceLoopInstallation
open Zkc.Source Zkc.Source.Structured Zkc.Obligations Zkc.Transcript
open ZkcSecurity.Source ZkcSecurity.FiatShamir
variable {carriers : Carriers}
  (escape : EscapeJudgment (PublicProperties.Event carriers) PublicProperties.Raw)

def step (state : Nat) : PIR.Process (Occurrence.signature carriers) Nat :=
  if state = 0 then .halt .refused else
    .call (.action (.receive .index "amount" 0)) (fun amount => .done (state + amount))

def loop (site : String) : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state =>
    (Occurrence.iterations.within site index (step state)).bind (loop site (index + 1) count)

def step_no (floor state : Nat) (valid : floor ≤ state)
    (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface escape (fun _ next => floor ≤ next)
      history (step state) := by
  unfold step
  split
  · exact .halt .refused
  · apply Derivation.receive rfl
    intro raw amount decoded
    exact .done (by omega)

def no (floor index count state : Nat) (valid : floor ≤ state) (site : String)
    (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface escape (fun _ next => floor ≤ next)
      history (loop site index count state) := by
  install_source_loop_no using_invariant (fun _ (_index _remaining : Nat) next => floor ≤ next) using_rules
    [step_no escape]

theorem step_cost (state : Nat) (price : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price) (step state) history 0 := by
  unfold step
  split
  · trivial
  · intro raw amount decoded
    trivial

theorem cost (index count state : Nat) (site : String) (price : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (loop site index count state) history (count * 0) := by
  install_source_loop_cost per_iteration 0 using_rules [step_cost (carriers := carriers)]

def unframed : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state => (step state).bind (unframed (index + 1) count)

def step_history (minimum floor state : Nat)
    (history : List (PublicProperties.Event carriers))
    (valid : minimum ≤ history.length ∧ floor ≤ state) :
    Derivation PublicProperties.interface escape
      (fun reached next => minimum ≤ reached.length ∧ floor ≤ next) history (step state) := by
  unfold step
  split
  · exact .halt .refused
  · apply Derivation.receive rfl
    intro raw amount decoded
    refine .done ⟨?_, ?_⟩
    · simpa only [List.length_append, List.length_singleton] using
        (Nat.le_trans valid.1 (Nat.le_add_right _ 1))
    · omega

/-- The No invariant depends on the history actually reached after each
adversarial receive. It cannot be installed by a history-erasing frame rule. -/
def history (minimum floor index count state : Nat)
    (reached : List (PublicProperties.Event carriers))
    (valid : minimum ≤ reached.length ∧ floor ≤ state) :
    Derivation PublicProperties.interface escape
      (fun final next => minimum ≤ final.length ∧ floor ≤ next) reached
      (unframed index count state) := by
  install_source_loop_no using_invariant
    (fun final (_index _remaining : Nat) next => minimum ≤ final.length ∧ floor ≤ next) using_rules [step_history escape]

/-- A round-dependent mathematical assertion can name the actual loop
coordinate without encoding it into the protocol's returned state. -/
def indexedStep (_state index : Nat) : PIR.Process (Occurrence.signature carriers) Nat :=
  .done (index + 1)

def indexed : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state => (indexedStep state index).bind (indexed (index + 1) count)

def indexed_step (state index : Nat) (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface escape (fun _ next => next = index + 1)
      history (indexedStep state index) := .done rfl

def indexed_invariant (index count : Nat) (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface escape (fun _ next => next = index + count)
      history (indexed index count index) := by
  install_source_loop_no using_invariant (fun _ current (_remaining : Nat) next => next = current)
    using_rules [indexed_step escape]
  rfl

/-- The callback law is insufficient when the actual successor changes its
continuation. This process increments its index twice, which the counted loop
law must reject even though its immediate callback is unchanged. -/
def skipped (site : String) : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state =>
    (Occurrence.iterations.within site index (step state)).bind (skipped site (index + 2) count)

example (floor index count state : Nat) (valid : floor ≤ state) (site : String)
    (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface escape (fun _ next => floor ≤ next)
      history (skipped site index count state) := by
  fail_if_success
    install_source_loop_no using_invariant (fun _ (_index _remaining : Nat) next => floor ≤ next) using_rules [step_no escape]
  induction count generalizing index state history with
  | zero => exact .done valid
  | succ count ih =>
    rw [skipped]
    exact (OccurrenceProperties.within site index _ (step_no escape floor state valid) history).bind _
      (fun reached next holds => ih (index + 2) next holds reached)

/-- A different actual pair exchanges an arbitrary index and retains both
complete loop states. Matching iteration frames come from the checked bodies. -/
def pairedSend (state : Nat) : PIR.Process (Occurrence.signature carriers) Nat :=
  .call (.action (.send (ty := .index) "paired" 1 state)) (fun _ => .done (state + 1))

def pairedReceive (_state : Nat) : PIR.Process (Occurrence.signature carriers) Nat :=
  .call (.action (.receive .index "paired" 0)) (fun amount => .done (amount + 1))

def sendLoop (site : String) : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state =>
    (Occurrence.iterations.within site index (pairedSend state)).bind (sendLoop site (index + 1) count)

def receiveLoop (site : String) : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state =>
    (Occurrence.iterations.within site index (pairedReceive state)).bind (receiveLoop site (index + 1) count)

theorem paired_step (left right : Nat) :
    Pair ⟨0, 1, []⟩ (fun a b => a = b)
      (pairedSend (carriers := carriers) left) (pairedReceive right) :=
  .message .index "paired" 0 1 left rfl ⟨rfl, rfl⟩ (.done rfl)

theorem paired (index count state : Nat) (site : String) :
    Pair ⟨0, 1, []⟩ (fun a b => a = b)
      (sendLoop (carriers := carriers) site index count state)
      (receiveLoop site index count state) := by
  install_source_loop_pair using_invariant (fun _ _ (a b : Nat) => a = b)
    using_rules [paired_step (carriers := carriers)]

def skippedReceiveLoop (site : String) : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state =>
    (Occurrence.iterations.within site index (pairedReceive state)).bind
      (skippedReceiveLoop site (index + 2) count)

/-- A paired callback cannot authorize a changed continuation coordinate. -/
example (_index _count _state : Nat) (_site : String) : True := by
  fail_if_success
    have altered : Pair ⟨0, 1, []⟩ (fun a b => a = b)
        (sendLoop (carriers := carriers) _site _index _count _state)
        (skippedReceiveLoop _site _index _count _state) := by
      install_source_loop_pair using_invariant (fun _ _ (a b : Nat) => a = b)
        using_rules [paired_step (carriers := carriers)]
  trivial

/-- Inner counts depend on the actual outer coordinate. Both levels retain
source enter/leave observations and the complete reply-dependent state. -/
def nested (outer inner : String) : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state =>
    (Occurrence.iterations.within outer index (loop inner 0 index state)).bind
      (nested outer inner (index + 1) count)

def nested_no (floor index count state : Nat) (valid : floor ≤ state) (outer inner : String)
    (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface escape (fun _ next => floor ≤ next)
      history (nested outer inner index count state) := by
  install_source_loop_no using_invariant (fun _ (_index _remaining : Nat) next => floor ≤ next)
    using_rules [no escape]

theorem inner_cost (index count state : Nat) (site : String) (price : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (loop site index count state) history 0 := by
  simpa only [mul_zero] using cost index count state site price history

theorem nested_cost (index count state : Nat) (outer inner : String) (price : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (nested outer inner index count state) history (count * 0) := by
  install_source_loop_cost per_iteration 0 using_rules [inner_cost (carriers := carriers)]

/-- No selected callback law: installation leaves the precise typed seam,
which is proved here from the existing component law rather than assumed. -/
def open_no (floor index count state : Nat) (valid : floor ≤ state)
    (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface escape (fun _ next => floor ≤ next)
      history (unframed index count state) := by
  install_source_loop_no using_invariant (fun _ (_index _remaining : Nat) next => floor ≤ next) using_rules []
  exact step_no escape floor _ (by assumption) _

/-- A symbolic requested budget stays a separate inequality goal. -/
theorem open_cost (index count state : Nat) (site : String) (price budget : ENNReal)
    (sufficient : 0 ≤ budget) (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (loop site index count state) history budget := by
  install_source_loop_cost per_iteration 0 using_rules [step_cost (carriers := carriers)]
  simpa only [mul_zero] using sufficient

/-- A charged query tests a nonzero symbolic price. Every actual reply is
retained by the loop; cost has no honest or No premise. -/
def queryStep (state : Nat) : PIR.Process (Occurrence.signature carriers) Nat :=
  .call (.action (.query "draw" "field" (.cons 7 .nil))) (fun _ => .done (state + 1))

theorem query_cost (state : Nat) (price : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (queryStep state) history price := by
  exact ⟨0, by simp only [add_zero]; exact le_rfl, fun _ => trivial⟩

def queryLoop (site : String) : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state =>
    (Occurrence.iterations.within site index (queryStep state)).bind (queryLoop site (index + 1) count)

theorem charged_cost (index count state : Nat) (site : String) (price : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (queryLoop site index count state) history (count * price) := by
  install_source_loop_cost per_iteration price using_rules [query_cost (carriers := carriers)]

/-- An absent cost callback stays a typed goal even when the total inequality
is solved. It can then be discharged explicitly with the real query law. -/
theorem open_cost_callback (index count state : Nat) (site : String) (price : ENNReal)
    (history : List (PublicProperties.Event carriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (queryLoop site index count state) history (count * price) := by
  install_source_loop_cost per_iteration price using_rules []
  apply OccurrenceProperties.within_cost
  intro reached
  exact query_cost _ _ reached

/-- Missing paired mathematics is a normal goal, not a new local axiom. -/
theorem open_pair (index count state : Nat) (site : String) :
    Pair ⟨0, 1, []⟩ (fun a b => a = b)
      (sendLoop (carriers := carriers) site index count state)
      (receiveLoop site index count state) := by
  install_source_loop_pair using_invariant (fun _ _ (a b : Nat) => a = b) using_rules []
  apply Pair.within
  exact paired_step _ _

/-- A callback with a changed actual occurrence frame cannot close pairing. -/
example (_index _count _state : Nat) : True := by
  fail_if_success
    have _changed : Pair ⟨0, 1, []⟩ (fun a b => a = b)
        (sendLoop (carriers := carriers) "left-frame" _index _count _state)
        (receiveLoop "right-frame" _index _count _state) := by
      solve
      | install_source_loop_pair using_invariant (fun _ _ (a b : Nat) => a = b)
          using_rules [paired_step (carriers := carriers)]
  trivial

/-- The callback proposal refuses a dependence on the remaining counter;
its shared theorem promises only the checked index/state callback shape. -/
def remainingStep : Nat → Nat → Nat → PIR.Process (Occurrence.signature carriers) Nat
  | _, 0, state => .done state
  | index, count + 1, state =>
    (step (state + count)).bind (remainingStep (index + 1) count)

example (_index _count _state : Nat)
    (_history : List (PublicProperties.Event carriers)) : True := by
  fail_if_success
    have _changed : Derivation PublicProperties.interface escape (fun _ next => 0 ≤ next)
        _history (remainingStep _index _count _state) := by
      solve
      | install_source_loop_no using_invariant (fun _ (_index _remaining : Nat) next => 0 ≤ next)
          using_rules [step_no escape]
  trivial

#print axioms open_pair
#print axioms charged_cost
#print axioms open_cost_callback
#print axioms LoopContracts.counted_no
#print axioms LoopContracts.counted_pair
#print axioms LoopContracts.counted_cost

#print axioms nested_no
#print axioms nested_cost
#print axioms open_no
#print axioms open_cost

#print axioms paired

#print axioms no
#print axioms history
#print axioms cost
end TestsSecurity.SourceLoopInstallation
