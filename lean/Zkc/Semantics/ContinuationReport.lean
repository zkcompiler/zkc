import Zkc.Semantics.Continuation

set_option autoImplicit false

namespace PIR.Continuation

variable {I : Signature} {A B S E Key : Type}

/-- An internal execution account. A freely constructed record is not evidence
    of execution, an authenticated receipt, or a permitted public artifact. -/
structure Report (S E A B : Type) where
  verifier : Execution S E (Terminal A)
  arm : Option (Execution S E B)
  combined : Execution S E B

/-- Retain the actual verifier result separately from follow-on completion.
    This refines the account of `after`; it does not change its execution. -/
def runReport (p : Proc I (Terminal A)) (arm : A → Proc I B)
    (h : Handler I S E) (s : S) : Report S E A B :=
  let first := p.run h s
  match first.outcome with
  | .stopped why => ⟨first, none, ⟨.stopped why, first.state, first.events⟩⟩
  | .returned .rejected => ⟨first, none, ⟨.stopped .reject, first.state, first.events⟩⟩
  | .returned (.accepted a) =>
    let last := (arm a).run h first.state
    ⟨first, some last, ⟨last.outcome, last.state, first.events ++ last.events⟩⟩

theorem report_verifier (p : Proc I (Terminal A)) (arm : A → Proc I B)
    (h : Handler I S E) (s : S) :
    (runReport p arm h s).verifier = p.run h s := by
  cases result : (p.run h s).outcome with
  | stopped => simp [runReport, result]
  | returned value => cases value <;> simp [runReport, result]

theorem report_combined (p : Proc I (Terminal A)) (arm : A → Proc I B)
    (h : Handler I S E) (s : S) :
    (runReport p arm h s).combined = (after p arm).run h s := by
  cases result : (p.run h s).outcome with
  | stopped why => simp [runReport, result, stopped_no_arm p arm h s why result]
  | returned value =>
    cases value with
    | rejected => simp [runReport, result, rejected_no_arm p arm h s result]
    | accepted a => simp [runReport, result, accepted_retains_prefix p arm h s a result]

theorem report_accepted (p : Proc I (Terminal A)) (arm : A → Proc I B)
    (h : Handler I S E) (s : S) (a : A)
    (yes : (p.run h s).outcome = .returned (.accepted a)) :
    (runReport p arm h s).verifier.outcome = .returned (.accepted a) ∧
    (runReport p arm h s).arm = some ((arm a).run h (p.run h s).state) := by
  simp [runReport, yes]

/-- Consumption persists under an explicit frame on the authoritative ledger.
    This covers every arm outcome; arbitrary ledger-writing arms do not satisfy
    the premise. Issuance, key interpretation, and intermediate access control
    remain separate obligations. -/
theorem consumed_under_frame [DecidableEq Key] (key : Key) (a : A)
    (arm : A → Option (Key × A) → Execution (Option (Key × A)) Unit B)
    (frame : (arm a none).state = none) :
    ((take key (some (key, a))).follow arm).state = none := by
  simpa [take, Execution.follow] using frame

end PIR.Continuation
