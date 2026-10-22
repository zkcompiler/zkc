module

public import ZkcExamples.Structured.SchnorrHonestProver

@[expose] public section

/-! A proved cut of the admitted prover before its challenge receive. The
checkpoint retains the actual sent commitment and private nonce. It introduces
no scheduler, new source, or future-dependent representative challenge. -/
namespace ZkcExamples.Structured.SchnorrCheckpoints
open Zkc.Source Zkc.Source.Structured SchnorrInteractive

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def commitmentPrefix (base : G) (service : Nat) : PIR.Process (participantInterface F G) (G × F) :=
  .call (.query nonceSite scalarDomain (.cons service .nil)) fun (nonce : F) =>
  .call (.send (ty := .group groupDomain) wiring.commitmentSite 1 (nonce • base)) fun _ =>
  .done (nonce • base, nonce)

def resume (witness : F) (state : G × F) : PIR.Process (participantInterface F G) (Option Bool) :=
  .call (.receive (.field scalarDomain) wiring.deliverySite 1) fun (challenge : F) =>
  .call (.send (ty := .field scalarDomain) wiring.responseSite 1
    (state.2 + challenge * witness)) fun _ => .done none

/-- This equality follows from the admitted source process equation,
so the prefix cannot inspect the later challenge and its state supplies resume. -/
theorem prover_cut (base proverKey : G) (witness : F) (service : Nat) :
    proverProcess base proverKey witness service =
      (commitmentPrefix base service).bind (resume witness) := by
  rw [prover_equation]
  rfl

omit [DecidableEq F] [DecidableEq G] in
/-- No challenge reply is supplied to this prefix; attempting one would stop.
The output commitment is exactly the observed send and the nonce remains private. -/
theorem prefix_run (base : G) (nonce : F) (service : Nat) :
    (commitmentPrefix base service).run
      (SchnorrHonestProver.replyHandler service (.returned nonce) (.stopped .refused)) () =
      ⟨.returned (nonce • base, nonce), (),
        [.query nonceSite scalarDomain (.cons service .nil),
         .send (ty := .group groupDomain) wiring.commitmentSite 1 (nonce • base)]⟩ := by
  simp [commitmentPrefix, PIR.Process.run, PIR.Execution.follow, SchnorrHonestProver.replyHandler,
    services, Values.get]
  rfl

def returnedValue {A : Type} : PIR.Outcome A → Option A
  | .returned result => some result
  | .stopped _ => none

/-- Unwrap an actual successful prefix execution, without a default value. -/
def commitment (base : G) (nonce : F) (service : Nat) : G × F :=
  (returnedValue ((commitmentPrefix base service).run
    (SchnorrHonestProver.replyHandler service (.returned nonce) (.stopped .refused)) ()).outcome).get
      (by rw [prefix_run]; rfl)

omit [DecidableEq F] [DecidableEq G] in
theorem commitment_eq (base : G) (nonce : F) (service : Nat) :
    commitment base nonce service = (nonce • base, nonce) := by
  simp only [commitment, prefix_run, returnedValue, Option.get_some]

omit [DecidableEq F] [DecidableEq G] in
/-- Resume uses the private nonce returned by commit, and sends the response
at the source's actual response site. There is no second nonce query. -/
theorem resume_run (base : G) (witness nonce challenge : F) (service : Nat) :
    (resume witness (commitment base nonce service)).run
      (SchnorrHonestProver.replyHandler service (.stopped .refused) (.returned challenge)) () =
      ⟨.returned none, (),
        [.receive (.field scalarDomain) wiring.deliverySite 1,
         .send (ty := .field scalarDomain) wiring.responseSite 1
           (nonce + challenge * witness)]⟩ := by
  rw [commitment_eq]
  simp [resume, PIR.Process.run, PIR.Execution.follow, SchnorrHonestProver.replyHandler]

end ZkcExamples.Structured.SchnorrCheckpoints
