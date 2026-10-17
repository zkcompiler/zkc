module

public import ZkcSecurity.FiatShamir.Decoding
public import ZkcSecurity.Examples.CausalSumcheck.SourceVerifier
public import ZkcSecurity.ArkLib.Sumcheck.Multilinear.Protocol
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness
public import Zkc.Source.Structured.CommonAdapter

@[expose] public section

/-! Fiat–Shamir soundness of the imported Sumcheck verifier.

The subject is the actual imported `example::Interactive` verifier
(`SumcheckSourceViews.imported.program`, role 1) projected to the common
participant actions (`importedValidator`). On every admitted count it is the
plain process `validator`: per round two received field messages, the boundary
check, one challenge, its delivery, and the interpolated claim; then the
public-table terminal check (`importedValidator_eq`).

Round-by-round soundness: a residual is doomed when its current claim is false
for the original table's multilinear extension summed over the remaining
Boolean coordinates. Received messages keep the claim; a failed boundary check
rejects; a passed check and a fresh challenge make the interpolated claim true
with probability at most `1 / |F|` (ArkLib's
`MultivariateRound.uniform_successor_soundness`, through the multilinear
message and table bridge); a doomed final claim fails the terminal check.
`ZkcSecurity.FiatShamir.soundness` then bounds the Fiat–Shamir transform.
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.SumcheckFiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Source.Common.Native
open ZkcExamples.Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.FiatShamir
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open _root_.Sumcheck.Interaction
open scoped ENNReal

variable {F G : Type}

section Process
variable [CommRing F] [DecidableEq F]

/-- After the challenge: deliver it, then interpolate the next claim. -/
def afterChallenge (ctx : ProtocolContext) (pc : List F × F) (low high challenge : F) :
    PIR.Proc (Actions F G) (List F × F) :=
  .call (.send (ty := .field "bls12-381.fr") (SumcheckVerifierLaws.deliverySite ctx)
    (ctx.roles 0) challenge) fun _ =>
    .done (pc.1 ++ [challenge], (1 - challenge) * low + challenge * high)

/-- After both halves: the boundary check, then the challenge. -/
def afterHigh (ctx : ProtocolContext) (handle : Nat) (pc : List F × F) (low high : F) :
    PIR.Proc (Actions F G) (List F × F) :=
  if pc.2 = low + high then
    .call (.query (SumcheckVerifierLaws.challengeSite ctx) "bls12-381.fr" (.cons handle .nil))
      fun challenge => afterChallenge ctx pc low high challenge
  else .halt .reject

/-- After the low half: receive the high half. -/
def afterLow (ctx : ProtocolContext) (handle : Nat) (pc : List F × F) (low : F) :
    PIR.Proc (Actions F G) (List F × F) :=
  .call (.receive (.field "bls12-381.fr") (SumcheckVerifierLaws.highSite ctx) (ctx.roles 0))
    fun high => afterHigh ctx handle pc low high

/-- One verifier round over the common participant actions. -/
def verifierRound (ctx : ProtocolContext) (handle : Nat) (pc : List F × F) :
    PIR.Proc (Actions F G) (List F × F) :=
  .call (.receive (.field "bls12-381.fr") (SumcheckVerifierLaws.lowSite ctx) (ctx.roles 0))
    fun low => afterLow ctx handle pc low

/-- The public-table terminal check on the final point and claim. -/
def terminal (count : Nat) (table : Table F count) (pc : List F × F) :
    PIR.Proc (Actions F G) (Option Bool) :=
  .done (some (decide (pc.1.length = count ∧
    extension count table (coordinates count pc.1) = pc.2)))

/-- The plain verifier: `count` rounds from the empty point and the claim, then
the terminal check. -/
def validator (ctx : ProtocolContext) (handle count : Nat) (table : Table F count) (claim : F) :
    PIR.Proc (Actions F G) (Option Bool) :=
  (PIR.repeatN count (verifierRound ctx handle) ([], claim)).bind (terminal count table)

end Process

section Import
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The actual imported verifier of `example::Interactive` at role 1, with its
present inputs, projected to the common participant actions. -/
def importedValidator (raw : List F) (claim : F) (count handle : Nat) :
    PIR.Proc (Actions F G) (Option Bool) :=
  ((SumcheckSourceViews.imported.program.participant F G 1
    (SumcheckSourceVerifier.sourceRootInputs (some raw) (some claim) (some count)
      (some handle))).bind fun outputs => .done (outputs.get .here)).interpret
    CommonAdapter.project

theorem repeatN_interpret {I J : PIR.Signature} {S : Type}
    (operations : PIR.OperationInterpretation I J) (step : S → PIR.Proc I S) :
    ∀ (count : Nat) (state : S), (PIR.repeatN count step state).interpret operations =
      PIR.repeatN count (fun next => (step next).interpret operations) state
  | 0, _ => rfl
  | count + 1, state => by
      simp only [PIR.repeatN, PIR.Proc.interpret_bind]
      congr 1
      funext next
      exact repeatN_interpret operations step count next

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem roundPresent_project (ctx : ProtocolContext) (handle : Nat) (pc : List F × F) :
    (SumcheckVerifierLaws.roundPresent (G := G) ctx handle pc).interpret CommonAdapter.project =
      verifierRound ctx handle pc := by
  unfold SumcheckVerifierLaws.roundPresent verifierRound afterLow afterHigh afterChallenge
  refine congrArg (PIR.Proc.call _) (funext fun low => ?_)
  refine congrArg (PIR.Proc.call _) (funext fun high => ?_)
  simp only [PIR.Proc.bind]
  by_cases checked : pc.2 = low + high <;> simp only [checked, ↓reduceIte] <;> rfl

/-- On every admitted count the imported verifier is the plain verifier, with
every interaction, stop and result. -/
theorem importedValidator_eq (count : Nat) (admitted : count ≤ 2) (raw : List F)
    (table : Table F count) (decoded : ofList? count raw = some table) (claim : F)
    (handle : Nat) :
    importedValidator (G := G) raw claim count handle =
      validator SumcheckSourceVerifier.childContext handle count table claim := by
  have collapse : ∀ process : PIR.Proc (participantInterface F G) (List F × F),
      (process.bind fun pc =>
          PIR.Proc.done (CausalSumcheck.SourceVerifier.checkedResult (G := G) count table pc)).bind
        (fun outputs : Values (Component (assignment F G)) [.boolean] =>
          PIR.Proc.done (outputs.get .here)) =
      process.bind fun pc => .done (some (decide (pc.1.length = count ∧
        extension count table (coordinates count pc.1) = pc.2))) := by
    intro process
    rw [PIR.Proc.bind_assoc]
    rfl
  rw [importedValidator, CausalSumcheck.SourceVerifier.source_present count admitted raw table
    decoded claim handle]
  refine (congrArg (PIR.Proc.interpret CommonAdapter.project) (collapse _)).trans ?_
  rw [PIR.Proc.interpret_bind, repeatN_interpret]
  simp only [roundPresent_project]
  rfl

/-- Above the exported maximum the imported verifier refuses before any action. -/
theorem importedValidator_excess (count : Nat) (large : 2 < count) (raw : List F) (claim : F)
    (handle : Nat) :
    importedValidator (G := G) raw claim count handle = .halt .refused := by
  rw [importedValidator]
  change ((SumcheckSourceViews.program.participant F G 1
    (SumcheckSourceVerifier.sourceRootInputs (some raw) (some claim) (some count)
      (some handle))).bind fun outputs => .done (outputs.get .here)).interpret
    CommonAdapter.project = _
  rw [SumcheckSourceVerifier.verifier_excess (some raw) (some claim) count (some handle) large]
  rfl

end Import

/-! ## Round-by-round soundness -/

/-- Where a verifier residual stands: before a round, after its low half, after
both halves, or after its challenge. `remaining` counts the later rounds. -/
inductive Phase (F : Type) where
  | round (remaining : Nat) (point : List F) (claim : F)
  | low (remaining : Nat) (point : List F) (claim low : F)
  | high (remaining : Nat) (point : List F) (claim low high : F)
  | challenged (remaining : Nat) (point : List F) (claim low high challenge : F)

section Certificate
variable [Field F] [DecidableEq F]

/-- The residual process at each phase, exactly as the verifier's continuations
produce it. -/
def residual (ctx : ProtocolContext) (handle count : Nat) (table : Table F count) :
    Phase F → PIR.Proc (Actions F G) (Option Bool)
  | .round remaining point claim =>
      (PIR.repeatN remaining (verifierRound ctx handle) (point, claim)).bind (terminal count table)
  | .low remaining point claim low =>
      ((afterLow ctx handle (point, claim) low).bind
        (PIR.repeatN remaining (verifierRound ctx handle))).bind (terminal count table)
  | .high remaining point claim low high =>
      ((afterHigh ctx handle (point, claim) low high).bind
        (PIR.repeatN remaining (verifierRound ctx handle))).bind (terminal count table)
  | .challenged remaining point claim low high challenge =>
      ((afterChallenge ctx (point, claim) low high challenge).bind
        (PIR.repeatN remaining (verifierRound ctx handle))).bind (terminal count table)

/-- ArkLib's realized polynomial oracle of the original table. -/
noncomputable abbrev behavior {count : Nat} (table : Table F count) :=
  (MultivariateRound.polynomialFamily F count 1).behaviorOfRealizations
    (fun _ => oracleStatement table)

/-- `claim` is false at `point`: ArkLib's closed round relation fails for the
table's multilinear extension summed over the remaining Boolean coordinates. -/
def FalseClaim {count : Nat} (table : Table F count) (point : List F) (claim : F) : Prop :=
  ∃ (i : Fin (count + 1)) (statement : _root_.Sumcheck.Spec.StatementRound F count i),
    point.length = i ∧ statement.target = claim ∧ statement.challenges = coordinates i point ∧
    ¬ MultivariateRound.closedRelation F count 1 (boolEmbedding F) i ⟨statement, behavior table⟩

/-- The doomed invariant: a false claim, with the point length matching the
rounds still to run. -/
def Holds (count : Nat) (table : Table F count) : Phase F → Prop
  | .round remaining point claim =>
      point.length + remaining = count ∧ FalseClaim table point claim
  | .low remaining point claim _ =>
      point.length + (remaining + 1) = count ∧ FalseClaim table point claim
  | .high remaining point claim _ _ =>
      point.length + (remaining + 1) = count ∧ FalseClaim table point claim
  | .challenged remaining point _ low high challenge =>
      point.length + (remaining + 1) = count ∧
        FalseClaim table (point ++ [challenge]) ((1 - challenge) * low + challenge * high)

/-- Doomed residuals: those of phases satisfying the invariant. -/
def Doomed (ctx : ProtocolContext) (handle count : Nat) (table : Table F count)
    (process : PIR.Proc (Actions F G) (Option Bool)) : Prop :=
  ∃ phase, Holds count table phase ∧ residual ctx handle count table phase = process

omit [DecidableEq F] in
theorem snoc_coordinates (point : List F) (challenge : F) {length : Nat}
    (sized : point.length = length) :
    Fin.snoc (α := fun _ => F) (coordinates length point) challenge =
      coordinates (length + 1) (point ++ [challenge]) := by
  funext index
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · simp [coordinates, sized]
  · have bound : earlier.val < point.length := sized ▸ earlier.isLt
    simp [coordinates, List.getElem?_append_left bound]

omit [DecidableEq F] in
/-- A claim different from the table sum is false at the empty point. -/
theorem falseClaim_initial {count : Nat} (table : Table F count) (claim : F)
    (different : claim ≠ booleanSum table) : FalseClaim table [] claim := by
  refine ⟨0, ⟨claim, Fin.elim0⟩, rfl, rfl, funext fun index => index.elim0, ?_⟩
  rw [closed_statement]
  exact fun same => different same.symm

omit [DecidableEq F] in
/-- A false claim at a complete point fails the terminal evaluation. -/
theorem falseClaim_terminal {count : Nat} (table : Table F count) (point : List F) (claim : F)
    (wrong : FalseClaim table point claim) (complete : point.length = count) :
    extension count table (coordinates count point) ≠ claim := by
  obtain ⟨index, statement, sized, target, challenges, notClosed⟩ := wrong
  have last : index = Fin.last count := Fin.ext (by simp [← sized, complete])
  subst last
  rw [MultivariateRound.closedRelation_last_iff] at notClosed
  intro evaluates
  apply notClosed
  change MvPolynomial.eval statement.challenges
    (ZkcSecurity.ArkLib.Sumcheck.Multilinear.statement table) = statement.target
  rw [statement_evaluate, challenges, target]
  exact evaluates

variable [Fintype F] [SampleableType F]

omit [DecidableEq F] in
/-- Per-round soundness, from ArkLib's single-round successor bound: after a
passed boundary check, a fresh uniform challenge makes a false claim true with
probability at most `1 / |F|`. -/
theorem falseClaim_successor {count : Nat} (table : Table F count) (point : List F)
    (claim low high : F) (wrong : FalseClaim table point claim) (open' : point.length < count)
    (checked : claim = low + high) :
    Pr{let challenge ← $ᵗ F}[
      ¬ FalseClaim table (point ++ [challenge]) ((1 - challenge) * low + challenge * high)] ≤
      1 / (Fintype.card F : ENNReal) := by
  obtain ⟨index, statement, sized, target, challenges, notClosed⟩ := wrong
  obtain ⟨position, rfl⟩ : ∃ position : Fin count, position.castSucc = index :=
    Fin.exists_castSucc_eq.mpr (fun last => by
      rw [last] at sized
      simp at sized
      omega)
  have passes : ((Finset.univ.map (boolEmbedding F)).toList.map
      (fun x => (message (low, high)).val.eval x)).sum = statement.target := by
    have evaluated : (fun x => (message (low, high)).val.eval x) =
        Zkc.Protocols.Sumcheck.Multilinear.evaluate (low, high) :=
      funext (message_evaluate (low, high))
    rw [evaluated, target, checked]
    exact domain_sum_message (low, high)
  have bound := MultivariateRound.uniform_successor_soundness count 1 F (boolEmbedding F) position
    statement (oracleStatement table) (message (low, high)) notClosed passes
  rw [Nat.cast_one] at bound
  refine (prEvent_mono _ _ _ (fun challenge escaped => ?_)).trans bound
  by_contra notClosed'
  apply escaped
  refine ⟨position.succ, ⟨(message (low, high)).val.eval challenge,
    Fin.snoc statement.challenges challenge⟩, ?_, ?_, ?_, notClosed'⟩
  · simp [sized]
  · rw [message_evaluate]
    rfl
  · change Fin.snoc (α := fun _ => F) statement.challenges challenge =
      coordinates (position.val + 1) (point ++ [challenge])
    rw [challenges]
    exact snoc_coordinates point challenge sized

omit [Fintype F] [SampleableType F] in
theorem residual_high_pass (ctx : ProtocolContext) (handle count : Nat) (table : Table F count)
    (remaining : Nat) (point : List F) (claim low high : F) (checked : claim = low + high) :
    residual (G := G) ctx handle count table (.high remaining point claim low high) =
      .call (.query (SumcheckVerifierLaws.challengeSite ctx) "bls12-381.fr" (.cons handle .nil))
        fun challenge => residual ctx handle count table
          (.challenged remaining point claim low high challenge) := by
  simp only [residual, afterHigh]
  rw [ite_eq_left_of_eq_true _ _ (eq_true checked)]
  rfl

omit [Fintype F] [SampleableType F] in
theorem residual_high_fail (ctx : ProtocolContext) (handle count : Nat) (table : Table F count)
    (remaining : Nat) (point : List F) (claim low high : F) (failed : ¬ claim = low + high) :
    residual (G := G) ctx handle count table (.high remaining point claim low high) =
      .halt .reject := by
  simp only [residual, afterHigh]
  rw [ite_eq_right_of_eq_false _ _ (eq_false failed)]
  rfl

/-- Every doomed residual meets its local obligation. -/
theorem doomed_step (ctx : ProtocolContext) (handle count : Nat) (table : Table F count) :
    ∀ process, Doomed (G := G) ctx handle count table process →
      Step (Doomed ctx handle count table) (· = some true) (1 / (Fintype.card F : ENNReal))
        process := by
  rintro _ ⟨phase, holds, rfl⟩
  cases phase with
  | round remaining point claim =>
      obtain ⟨sized, wrong⟩ := holds
      cases remaining with
      | zero =>
          show ¬ some (decide (point.length = count ∧
            extension count table (coordinates count point) = claim)) = some true
          intro accepted
          simp only [Option.some.injEq, decide_eq_true_eq] at accepted
          exact falseClaim_terminal table point claim wrong accepted.1 accepted.2
      | succ remaining =>
          intro low
          exact ⟨.low remaining point claim low, ⟨sized, wrong⟩, rfl⟩
  | low remaining point claim low =>
      intro high
      exact ⟨.high remaining point claim low high, holds, rfl⟩
  | high remaining point claim low high =>
      obtain ⟨sized, wrong⟩ := holds
      by_cases checked : claim = low + high
      · rw [residual_high_pass ctx handle count table remaining point claim low high checked]
        refine (prEvent_mono _ _ _ (fun challenge escaped => ?_)).trans
          (falseClaim_successor table point claim low high wrong (by omega) checked)
        exact fun stays => escaped ⟨.challenged remaining point claim low high challenge,
          ⟨sized, stays⟩, rfl⟩
      · rw [residual_high_fail ctx handle count table remaining point claim low high checked]
        trivial
  | challenged remaining point claim low high challenge =>
      obtain ⟨sized, wrong⟩ := holds
      exact ⟨.round remaining (point ++ [challenge]) ((1 - challenge) * low + challenge * high),
        ⟨by simp; omega, wrong⟩, rfl⟩

/-- Round-by-round soundness of the plain verifier, with error `1 / |F|` per
challenge. -/
noncomputable def certificate (ctx : ProtocolContext) (handle count : Nat)
    (table : Table F count) :
    RoundByRound (F := F) (G := G) (· = some true) (1 / (Fintype.card F : ENNReal)) :=
  RoundByRound.ofStep (Doomed ctx handle count table) (doomed_step ctx handle count table)

omit [Fintype F] [SampleableType F] in
/-- Each round makes exactly one challenge. -/
theorem residual_queryBound (ctx : ProtocolContext) (handle count : Nat) (table : Table F count) :
    ∀ (remaining : Nat) (point : List F) (claim : F),
      QueryBound (residual (G := G) ctx handle count table (.round remaining point claim))
        remaining := by
  intro remaining
  induction remaining with
  | zero => intro point claim; trivial
  | succ remaining ih =>
      intro point claim low high
      by_cases checked : claim = low + high
      · change QueryBound (residual ctx handle count table (.high remaining point claim low high))
          (remaining + 1)
        rw [residual_high_pass ctx handle count table remaining point claim low high checked]
        exact ⟨Nat.succ_pos remaining, fun challenge => ih _ _⟩
      · change QueryBound (residual ctx handle count table (.high remaining point claim low high))
          (remaining + 1)
        rw [residual_high_fail ctx handle count table remaining point claim low high checked]
        trivial

variable [DecidableEq G]

/-- Fiat–Shamir soundness of the plain Sumcheck verifier.

Adversary interface: the statement (`table`, `claim`, `count`) and the initial
transcript history are fixed before the experiment; the prover is an arbitrary
oracle computation on the transcript oracle over all typed histories, with at
most `queries` queries on every path, counting repeats and cache hits; the
oracle starts empty and is shared with the transform, whose `count` challenges
are also charged. No other oracle or private randomness is available inside
the computation. -/
theorem soundness (context : Context) (ctx : ProtocolContext) (handle count : Nat)
    (table : Table F count) (claim : F) (falseClaim : claim ≠ booleanSum table)
    (initial : History F G) (prover : OracleComp (Spec F G) (Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (FiatShamir.experiment context
        (validator ctx handle count table claim) initial prover)).run' ∅}[
      Accepted (· = some true) result.1] ≤
      (queries + count) * (1 / (Fintype.card F : ENNReal)) :=
  FiatShamir.soundness (certificate ctx handle count table) context _
    ⟨.round count [] claim, ⟨by simp, falseClaim_initial table claim falseClaim⟩, rfl⟩ count
    (residual_queryBound ctx handle count table count [] claim) initial prover queries proverBound

end Certificate

section Imported
variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A refused validator never accepts. -/
noncomputable def refusedCertificate (error : ENNReal) :
    RoundByRound (F := F) (G := G) (A := Option Bool) (· = some true) error :=
  RoundByRound.ofStep (fun process => process = .halt .refused) (by rintro _ rfl; trivial)

/-- Fiat–Shamir soundness of the actual imported `example::Interactive`
verifier, for every count: up to the exported maximum of two rounds it is the
plain verifier; above it the verifier refuses. Same adversary interface as
`soundness`; the false claim is stated on the raw public vector. -/
theorem imported_soundness (context : Context) (count : Nat) (raw : List F)
    (table : Table F count) (decoded : ofList? count raw = some table) (claim : F)
    (falseClaim : claim ≠ raw.sum) (handle : Nat) (initial : History F G)
    (prover : OracleComp (Spec F G) (Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (FiatShamir.experiment context
        (importedValidator raw claim count handle) initial prover)).run' ∅}[
      Accepted (· = some true) result.1] ≤
      (queries + count) * (1 / (Fintype.card F : ENNReal)) := by
  by_cases admitted : count ≤ 2
  · rw [importedValidator_eq count admitted raw table decoded claim handle]
    exact soundness context SumcheckSourceVerifier.childContext handle count table claim
      (by rwa [booleanSum_ofList? raw table decoded]) initial prover queries proverBound
  · rw [importedValidator_excess count (by omega) raw claim handle]
    refine (FiatShamir.soundness (refusedCertificate (1 / (Fintype.card F : ENNReal))) context _
      rfl 0 trivial initial prover queries proverBound).trans ?_
    exact mul_le_mul_left (add_le_add_right (by exact_mod_cast Nat.zero_le count) _) _

omit [AddCommGroup G] [Module F G] in
/-- Composition with the construction rule of the compiled Proof Entry. The
two premises are the vertical links the stage-correspondence rules supply: the
compiled verifier, with the transcript oracle as challenge function, is the
Fiat–Shamir transform of an original validator (`construction`), and that
validator is the plain Sumcheck verifier (`projection`). -/
theorem compiled_soundness (context : Context)
    (compiled : Proof F G → OracleComp (Spec F G) (PIR.Outcome (Option Bool) × Proof F G))
    (original : PIR.Proc (Actions F G) (Option Bool)) (initial : History F G)
    (construction : ∀ proof, compiled proof = transform context historyQuery original initial proof)
    (ctx : ProtocolContext) (handle count : Nat) (table : Table F count) (claim : F)
    (projection : original = validator ctx handle count table claim)
    (falseClaim : claim ≠ booleanSum table)
    (prover : OracleComp (Spec F G) (Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (prover >>= compiled)).run' ∅}[
      Accepted (· = some true) result.1] ≤
      (queries + count) * (1 / (Fintype.card F : ENNReal)) := by
  have same : (prover >>= compiled) = FiatShamir.experiment context original initial prover := by
    unfold FiatShamir.experiment
    congr 1
    funext proof
    exact construction proof
  rw [same, projection]
  exact soundness context ctx handle count table claim falseClaim initial prover queries
    proverBound

end Imported

/-! ## Adaptively chosen statements -/

/-- A well-formed public statement of the imported verifier: the raw public
vector, the claim and the round count, with the vector's table at that count.
The table is determined by the vector and the count. -/
structure PublicStatement (F : Type) where
  raw : List F
  claim : F
  count : Nat
  table : Table F count
  decoded : ofList? count raw = some table

section Adaptive
variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Doomed residuals of every table and claim, and the refused verifier. -/
def DoomedAny (ctx : ProtocolContext) (handle : Nat)
    (process : PIR.Proc (Actions F G) (Option Bool)) : Prop :=
  (∃ count table, Doomed ctx handle count table process) ∨ process = .halt .refused

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem doomedAny_step (ctx : ProtocolContext) (handle : Nat) :
    ∀ process : PIR.Proc (Actions F G) (Option Bool), DoomedAny ctx handle process →
      Step (DoomedAny ctx handle) (· = some true) (1 / (Fintype.card F : ENNReal))
        process := by
  rintro process (⟨count, table, member⟩ | refused)
  · exact Step.mono (fun _ inside => .inl ⟨count, table, inside⟩) process
      (doomed_step ctx handle count table process member)
  · subst refused
    trivial

/-- One certificate for the imported verifier at every statement. -/
noncomputable def anyCertificate (ctx : ProtocolContext) (handle : Nat) :
    RoundByRound (F := F) (G := G) (· = some true) (1 / (Fintype.card F : ENNReal)) :=
  RoundByRound.ofStep (DoomedAny ctx handle) (doomedAny_step ctx handle)

/-- The imported verifier at a statement, in plain form: the plain verifier on
admitted counts and a refusal above them. -/
def plainFamily (handle : Nat) (statement : PublicStatement F) :
    PIR.Proc (Actions F G) (Option Bool) :=
  if statement.count ≤ 2 then
    validator SumcheckSourceVerifier.childContext handle statement.count statement.table
      statement.claim
  else .halt .refused

omit [Fintype F] [SampleableType F] in
theorem importedValidator_family (handle : Nat) (statement : PublicStatement F) :
    importedValidator (G := G) statement.raw statement.claim statement.count handle =
      plainFamily handle statement := by
  unfold plainFamily
  by_cases admitted : statement.count ≤ 2
  · rw [ite_eq_left admitted, importedValidator_eq statement.count admitted statement.raw
      statement.table statement.decoded statement.claim handle]
  · rw [ite_eq_right admitted, importedValidator_excess statement.count (by omega) statement.raw
      statement.claim handle]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem plainFamily_doomed (handle : Nat) (statement : PublicStatement F)
    (falseClaim : statement.claim ≠ statement.raw.sum) :
    (anyCertificate (G := G) SumcheckSourceVerifier.childContext handle).doomed
      (plainFamily handle statement) := by
  show DoomedAny SumcheckSourceVerifier.childContext handle (plainFamily handle statement)
  unfold plainFamily
  by_cases admitted : statement.count ≤ 2
  · rw [ite_eq_left admitted]
    refine .inl ⟨statement.count, statement.table, .round statement.count [] statement.claim,
      ⟨by simp, falseClaim_initial statement.table statement.claim ?_⟩, rfl⟩
    rwa [booleanSum_ofList? statement.raw statement.table statement.decoded]
  · rw [ite_eq_right admitted]
    exact .inr rfl

omit [Fintype F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem plainFamily_queryBound (handle : Nat) (statement : PublicStatement F) :
    QueryBound (plainFamily (G := G) handle statement) 2 := by
  unfold plainFamily
  by_cases admitted : statement.count ≤ 2
  · rw [ite_eq_left admitted]
    exact QueryBound.mono _ (residual_queryBound SumcheckSourceVerifier.childContext handle
      statement.count statement.table statement.count [] statement.claim) admitted
  · rw [ite_eq_right admitted]
    trivial

/-- Adaptive Fiat–Shamir soundness of the imported Sumcheck verifier.

The prover chooses the well-formed public statement after its oracle queries;
the initial history must determine the statement (`Determined`), as a binding
of the public inputs does. Challenges are decoded oracle answers whose events
exceed the uniform field's by at most `loss`. A false claim on the chosen
vector is accepted with probability at most `(queries + 2) * (1 / |F| + loss)`,
where two is the exported maximum count; larger counts are refused. -/
theorem adaptive_imported_soundness {B : Type} [SampleableType B] (context : Context)
    (handle : Nat) (decode : B → F) (loss : ENNReal) (balanced : Balanced decode loss)
    (initial : PublicStatement F → History F G) (determined : Determined initial)
    (prover : OracleComp (Oracle F G B) (PublicStatement F × Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (adaptiveExperiment context decode
        (fun statement : PublicStatement F =>
          importedValidator statement.raw statement.claim statement.count handle)
        initial prover)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤
      (queries + 2) * (1 / (Fintype.card F : ENNReal) + loss) := by
  have family : (fun statement : PublicStatement F =>
      importedValidator (G := G) statement.raw statement.claim statement.count handle) =
        plainFamily handle := funext (importedValidator_family handle)
  rw [family]
  exact FiatShamir.adaptive_soundness (anyCertificate SumcheckSourceVerifier.childContext handle)
    context decode balanced (plainFamily handle) initial determined
    (fun statement => statement.claim ≠ statement.raw.sum) (plainFamily_doomed handle) 2
    (plainFamily_queryBound handle) prover queries proverBound

/-- The adaptive bound with the suite's challenge derivation modelled as reduction
modulo the field size of a uniform sample below `N`, read through a numbering of
the field (for a 64-byte squeeze, `N = 2 ^ 512`). The decoding costs `|F| / N`
per challenge. -/
theorem reduced_imported_soundness (context : Context) (handle : Nat)
    (numbering : F ≃ Fin (Fintype.card F)) (N : Nat) [NeZero N] [SampleableType (Fin N)]
    (initial : PublicStatement F → History F G) (determined : Determined initial)
    (prover : OracleComp (Oracle F G (Fin N)) (PublicStatement F × Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (adaptiveExperiment context (reduce numbering N)
        (fun statement : PublicStatement F =>
          importedValidator statement.raw statement.claim statement.count handle)
        initial prover)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤
      (queries + 2) * (1 / (Fintype.card F : ENNReal) + (Fintype.card F : ENNReal) / N) :=
  adaptive_imported_soundness context handle (reduce numbering N) _ (balanced_reduce numbering N)
    initial determined prover queries proverBound

end Adaptive

end ZkcSecurity.Examples.SumcheckFiatShamir
