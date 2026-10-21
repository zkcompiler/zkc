module

public import ZkcArkLib.Sumcheck.Multilinear.Protocol
public import ZkcSecurity.VCVio.Execution

@[expose] public section


namespace ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal

open OracleComp OracleSpec
open Zkc.Protocols.Sumcheck.Multilinear
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open Zkc.Polynomial.Multilinear
open _root_.Interaction.Oracle _root_.Sumcheck.Interaction
open ZkcSecurity.VCVio.Execution
open scoped ENNReal

variable {F S E K : Type}

/-- The service has a pre-draw stage and a post-draw stage. Delivery is separate.
    Each result may stop and retains its own state and observation prefix. -/
structure AfterPair (F S E K : Type) where
  beforeDraw : Phase S E Unit
  publicAbort : Phase S E Unit
  afterDraw : F → Phase S E Unit
  deliver : F → Phase S E K
  /-- Trusted append/loop admission, after delivery and before the next round. -/
  advance : F → Phase S E Unit := fun _ s => pure ⟨.returned (), s, []⟩

/-- The high computation is selected by the low computation. Its input state
    includes any acknowledgment/private state retained at the first receive. -/
abbrev High (F S E K : Type) := Phase S E (F × AfterPair F S E K)
abbrev Low (F S E K : Type) := Phase S E (F × High F S E K)

/-- Finite phase/strategy family, not a source AST. Continuations are actual
    computations selected by previous computations, not fixed transcripts. -/
def Strategy (F S E : Type) : Nat → Type
  | 0 => Phase S E Unit
  | n + 1 => Low F S E (Strategy F S E n)

def stopped {A : Type} (why : PIR.Stop) (r : PIR.Execution S E K) :
    PIR.Execution S E A := ⟨.stopped why, r.state, r.events⟩

/-- Exact stop preservation follows from the existing followM, with no exception
    layer that could discard an already returned observation prefix. -/
theorem stopped_follow (why : PIR.Stop) (s : S) (events : List E)
    (next : K → S → ProbComp (PIR.Execution S E F)) :
    (PIR.Execution.followM ⟨.stopped why, s, events⟩ next) =
      pure ⟨.stopped why, s, events⟩ := rfl

/-- Useful in an arbitrary probabilistic prefix: no-op abort is exactly a bare
    reject, including the accumulated state/events and already stopped paths. -/
theorem noOp_abort_is_bare {A : Type} (prior : ProbComp (PIR.Execution S E A)) :
    (do let p ← prior
        p.followM fun _ s => do
          let aborted ← noOp s
          pure (stopped (A := K) .reject aborted)) =
    (do let p ← prior
        p.followM fun _ s => pure ⟨.stopped .reject, s, []⟩) := by
  simp [noOp, result, stopped]

/-- Optional joint-runtime wrapper. It preserves the prefix before executing
    public abort; it is not part of the bare Participant guard semantics. -/
def abortAfter {A : Type} (prior : ProbComp (PIR.Execution S E A))
    (abort : Phase S E Unit) : ProbComp (PIR.Execution S E K) := do
  let p ← prior
  p.followM fun _ s => do
    let a ← abort s
    pure (stopped .reject a)

theorem abortAfter_returned {A : Type} (a : A) (s : S) (prior : List E)
    (abort : Phase S E Unit) :
    abortAfter (K := K) (pure ⟨.returned a, s, prior⟩) abort = (do
      let after ← abort s
      pure ⟨.stopped .reject, after.state, prior ++ after.events⟩) := by
  simp [abortAfter, PIR.Execution.followM, stopped]

variable [Field F] [DecidableEq F]

/-- Guard-success service preparation is put before the ordinary endpoint
    selection. For each fixed verifier-private claim the proof may hardcode it.
    No future coin is available to this construction.
    On guard failure it is not run; public abort belongs to the response. -/
def prepare (claim : F) (low : Low F S E K) (s : S) :
    ProbComp (PIR.Execution S E (Message F × AfterPair F S E K)) := do
  let first ← low s
  first.followM fun (lo, high) s => do
    let second ← high s
    second.followM fun (hi, tail) s => do
      if boundary (lo, hi) = claim then
        let ready ← tail.beforeDraw s
        ready.followM fun _ s => pure (result ((lo, hi), tail) s)
      else pure (result ((lo, hi), tail) s)

/-- Fixed causal completion, used only after an already stopped source branch. -/
def dummy : (n : Nat) → EndpointProver (F := F) unifSpec n
  | 0 => ()
  | n + 1 => pure ⟨(0, 0), fun
      | none => pure ()
      | some _ => pure (dummy n)⟩

def complete : (n : Nat) → F → Strategy F S E n → S →
    EndpointProver (F := F) unifSpec n
  | 0, _, _, _ => ()
  | n + 1, claim, low, s => do
      let ready ← prepare claim low s
      match ready.outcome with
      | .stopped _ => dummy (n + 1)
      | .returned (pair, tail) =>
          pure ⟨pair, fun
            | none => do
                let _ ← tail.publicAbort ready.state
                pure ()
            | some r => do
                let queried ← tail.afterDraw r ready.state
                match queried.outcome with
                | .stopped _ => pure (dummy n)
                | .returned _ => do
                    let sent ← tail.deliver r queried.state
                    match sent.outcome with
                    | .stopped _ => pure (dummy n)
                    | .returned next => do
                        let advanced ← tail.advance r sent.state
                        match advanced.outcome with
                        | .stopped _ => pure (dummy n)
                        | .returned _ => pure (complete n (evaluate pair r) next advanced.state)⟩

/-- A terminal predicate is parameterized by the accumulated chronological
    challenge list. The actual table predicate is supplied by the bridge. -/
def run [SampleableType F] : (n : Nat) → F → List F → Strategy F S E n → S →
    ProbComp (PIR.Execution S E (List F × F))
  | 0, claim, point, terminal, s => do
      let checked ← terminal s
      checked.followM fun _ s => pure (result (point, claim) s)
  | n + 1, claim, point, low, s => do
      let ready ← prepare claim low s
      ready.followM fun (pair, tail) s => do
        if boundary pair = claim then
          let r ← ($ᵗ F)
          let queried ← tail.afterDraw r s
          queried.followM fun _ s => do
            let sent ← tail.deliver r s
            sent.followM fun next s => do
              let advanced ← tail.advance r s
              advanced.followM fun _ s => run n (evaluate pair r) (point ++ [r]) next s
        else
          let aborted ← tail.publicAbort s
          pure (stopped .reject aborted)

def accepts (terminal : List F → F → Prop) (r : PIR.Execution S E (List F × F)) : Prop :=
  match r.outcome with
  | .stopped _ => False
  | .returned pc => terminal pc.1 pc.2

def phaseGame [SampleableType F] (n : Nat) (claim : F) (point : List F)
    (strategy : Strategy F S E n) (s : S) (terminal : List F → F → Prop) : ProbComp Prop := do
  let execution ← run n claim point strategy s
  return accepts terminal execution

/-- An observation of the pinned endpoint equations. Equality to the actual
    ArkLib execution is proved below, rather than assumed. -/
def endpointGame [SampleableType F] : (n : Nat) → F → List F →
    EndpointProver (F := F) unifSpec n → (List F → F → Prop) → ProbComp Prop
  | 0, claim, point, _, terminal => pure (terminal point claim)
  | n + 1, claim, point, prover, terminal => do
      let chosen ← prover
      if boundary chosen.1 = claim then
        let r ← ($ᵗ F)
        let next ← chosen.2 (some r)
        endpointGame n (evaluate chosen.1 r) (point ++ [r]) next terminal
      else
        let _ ← chosen.2 none
        pure False


end ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal
