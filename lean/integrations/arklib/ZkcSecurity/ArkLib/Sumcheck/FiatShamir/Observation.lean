module

public import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Game

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

/-! Exact query/state observation scope of the two-round correspondence. -/

namespace ZkcSecurity.ArkLib.Sumcheck.FiatShamir

open Interaction.Oracle Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.AlgebraicRounds
open Zkc.Protocols.Sumcheck.Common

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
variable {Salt : Type} [DecidableEq Salt]

abbrev RestorationKey (F Salt : Type) [Field F] [DecidableEq F] [Fintype F]
    [SampleableType F] := Key (Statement F) Salt (rounds (F := F) 2)

def firstKey (z : Statement F) (message : Message F) (salt : Salt) : RestorationKey F Salt :=
  Key.here z message salt

/-- Prior challenges are deliberately absent; prior messages and salts remain. -/
def secondKey (z : Statement F) (firstMessage : Message F) (firstSalt : Salt)
    (secondMessage : Message F) (secondSalt : Salt) : RestorationKey F Salt :=
  Key.later firstMessage firstSalt (Key.here z secondMessage secondSalt)

def messages (firstMessage : Message F) (firstSalt : Salt)
    (secondMessage : Message F) (secondSalt : Salt) : Messages Salt (rounds (F := F) 2) :=
  ⟨firstMessage, firstSalt, secondMessage, secondSalt, PUnit.unit⟩

omit [DecidableEq Salt] in
/-- Logical-round grouping identifies the completed path, not just its truth value. -/
theorem completedPath_eq (z : Statement F) (firstMessage : Message F) (firstSalt : Salt)
    (secondMessage : Message F) (secondSalt : Salt)
    (table : Table (Statement F) Salt (rounds (F := F) 2)) :
    completedPath (rounds (F := F) 2) z (messages firstMessage firstSalt secondMessage secondSalt)
      table = path firstMessage (table (firstKey z firstMessage firstSalt))
        secondMessage (table (secondKey z firstMessage firstSalt secondMessage secondSalt)) := rfl

omit [DecidableEq Salt] in
/-- The completion log has both distinct round keys, even on an early-rejected proof. -/
theorem completion_log (z : Statement F) (firstMessage : Message F) (firstSalt : Salt)
    (secondMessage : Message F) (secondSalt : Salt)
    (table : Table (Statement F) Salt (rounds (F := F) 2)) :
    (tableQueryLog (complete (rounds (F := F) 2) z
      (messages firstMessage firstSalt secondMessage secondSalt)) table).map Sigma.fst =
      [firstKey z firstMessage firstSalt,
        secondKey z firstMessage firstSalt secondMessage secondSalt] := by
  rw [complete_log_keys]
  rfl

omit [DecidableEq Salt] in
theorem roundKeys_distinct (z : Statement F) (firstMessage : Message F) (firstSalt : Salt)
    (secondMessage : Message F) (secondSalt : Salt) :
    firstKey z firstMessage firstSalt ≠
      secondKey z firstMessage firstSalt secondMessage secondSalt := by
  intro impossible
  cases impossible

omit [DecidableEq Salt] in
/-- Even adversarially selected, inconsistent prefixes reconstruct their first
challenge from the first key in the same table. -/
theorem secondKey_extractor (z : Statement F) (firstMessage : Message F) (firstSalt : Salt)
    (secondMessage : Message F) (secondSalt : Salt)
    (table : Table (Statement F) Salt (rounds (F := F) 2)) :
    keyExtractor (statementExtractor z)
      (secondKey z firstMessage firstSalt secondMessage secondSalt) table =
      keyExtractor
        (extractor 1 (True ∧ firstMessage.boundary = z.claim)
          ((polynomial z.coefficients).restrict (table (firstKey z firstMessage firstSalt)))
          (firstMessage.evaluate (table (firstKey z firstMessage firstSalt))))
        (Key.here z secondMessage secondSalt)
        (fun key => table (Key.later firstMessage firstSalt key)) := rfl

/-- Resampling a later key does not change its pre-challenge knowledge state. -/
theorem secondKey_state_update (z : Statement F) (firstMessage : Message F) (firstSalt : Salt)
    (secondMessage : Message F) (secondSalt : Salt)
    (table : Table (Statement F) Salt (rounds (F := F) 2)) (value : F) :
    keyExtractor (statementExtractor z)
      (secondKey z firstMessage firstSalt secondMessage secondSalt)
      (Function.update table (secondKey z firstMessage firstSalt secondMessage secondSalt) value) =
    keyExtractor (statementExtractor z)
      (secondKey z firstMessage firstSalt secondMessage secondSalt) table :=
  keyExtractor_update _ _ _ _

/-- Project only challenge sites from the actual PIR event sequence. -/
def querySite : Action Nat Native.language services (ScalarValue F F) → Option String
  | .query site _ _ => some site
  | _ => none

omit [Fintype F] [SampleableType F] [DecidableEq Salt] in
/-- Exact early-stop observations. All six receives are grouped into two
quadratic messages before their respective challenge; the final state counts
reached effects, and only reached query sites appear in the log. -/
theorem reached_observations {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring program) (z : Statement F) (service : Nat)
    (prover : Strategy F) (first second : F) :
    let result := run program z.coefficients z.claim service prover first second
    (result.state, result.events.filterMap querySite) =
      if wireBoundary prover.first = z.claim then
        if wireBoundary (prover.second first) = wireEvaluate prover.first first then
          (10, [wiring.firstChallenge, wiring.secondChallenge])
        else (8, [wiring.firstChallenge])
      else (3, []) := by
  unfold run
  rw [(certificate.realizes z.coefficients z.claim service).process_eq]
  by_cases firstCheck : wireBoundary prover.first = z.claim
  all_goals by_cases secondCheck :
    wireBoundary (prover.second first) = wireEvaluate prover.first first
  all_goals simp [experiment, experimentWith, standardArithmetic, PIR.Proc.run,
    PIR.Execution.follow, handler_receive_field, handler_query, handler_send, received,
    querySite, firstCheck, secondCheck]

end ZkcSecurity.ArkLib.Sumcheck.FiatShamir
