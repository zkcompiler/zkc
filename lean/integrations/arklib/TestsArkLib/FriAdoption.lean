import ZkcArkLib.Fri.Johnson
import ZkcArkLib.Fri.SourceCalculations
import ZkcArkLibExamples.Fri.VerifierCheck
import ZkcArkLibExamples.Fri.CommitChallenge
import ZkcArkLibExamples.Fri.CommitReadback
import ZkcArkLibExamples.Fri.VerifierInitialRead
import ZkcArkLibExamples.Fri.VirtualStore
import ZkcArkLibExamples.Fri.HolderPadding
import ZkcExamples.Structured.FriBindingExecution
import ZkcExamples.Structured.FriLowDegreeCall
import ZkcExamples.Structured.FriQueryCall
import ZkcArkLibExamples.Fri.PublishedSampling
import ZkcArkLibExamples.Fri.ClearCertificate
import ZkcTools.DeclarationAudit

/-! Focused controls for the mathematical FRI adapters. The two-round example is a mathematical
client with terminal dimension two, not a parameter change to an installed source application.
It reuses the last two certificates from the feasibility study and the existing soundness API.
-/

namespace TestsArkLib.FriAdoption

open ZkcSecurity.ArkLib.Fri
open Zkc.Source.Structured
open Domain OracleComp ReedSolomon.HiddenDerivative

section
open Zkc.Source ZkcExamples.Structured.FriScalarLoop

-- Source labels may change. Draw and delivery still have to occur in order,
-- and empty or repeated marks remain observations of the original process.
example : (DrawSites.fromBody (.letOp (.mark "") [] [] .nil
    (.letOp (.mark "") [] [] .nil (.letOp (.query 1 (.sampleIndex contract) "fresh") [] [] .nil
    (.letOp (.exchange .index 1 0 "forwarded") [] [] .nil (.ret [])))))).map
    (fun sites ↦ (sites.beforeDraw, sites.draw, sites.delivery)) = some (["", ""], "fresh", "forwarded") := rfl

example : DrawSites.fromBody (.letOp (.exchange .index 1 0 "forwarded") [] [] .nil
    (.letOp (.query 1 (.sampleIndex contract) "fresh") [] [] .nil (.ret []))) = none := rfl

example : DrawSites.fromBody (.bind [] (.stop .reject) (.ret [])) = none := rfl

private def selectsMark : ProtocolOp → Bool
  | .mark _ => true
  | _ => false

-- A mark inside a nested body is not a mark on the caller's continuation.
example : (Region.cutFirst selectsMark (d := protocolDialect) (Γ := []) (out := [])
    (.bind (.letOp (.mark "inner") .nil .nil (.ret (.nil : Operands [] []))) (.ret .nil))).isNone := rfl

-- The following mark is structurally present, but the stopping prefix keeps
-- it unreachable under every interpretation.
private def stoppedCaller : Region protocolDialect [] [] :=
  .bind (.stop (out := []) .reject) (.letOp (.mark "later") .nil .nil (.ret .nil))

example {I : PIR.Signature} (meaning : RegionMeaning protocolDialect I) (env : Environment meaning.Value []) :
    ((Region.cutFirst selectsMark stoppedCaller).get (by kernel_rfl)).reached meaning env = .halt .reject := rfl
end

-- A wrong source cursor cannot register a virtual view, even when the
-- captured word, challenge and geometry have the required types.
section
open Zkc.Source ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
variable {Aux E : Type} {M : Type → Type} [Monad M] [LawfulMonad M]

example (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
    (choose : PublishedWords.Chooser M model Aux E) (context : ProtocolContext) (n : Nat)
    (source : OracleAnchor) (beta shift : Octic) (before : VerifierPath.State Aux)
    (wrong : CommitVirtual.constructionSite.definition ≠ before.frame.definition) :
    PublishedWords.actionM FriSource.checkedUnit.oracles network choose (CommitVirtual.request context n source beta shift) before =
      pure ⟨.stopped .refused, before, []⟩ := by
  unfold PublishedWords.actionM
  rw [OraclePublication.actionM_local _ _ _ _ _ _ rfl]
  have different : (CommitVirtual.constructionSite.definition != before.frame.definition) = true :=
    bne_iff_ne.mpr wrong
  simp only [CommitVirtual.request, OracleProtocol.handler, different, Bool.true_or, ↓reduceIte]
end

-- Both random services run against the same published-word table in the
-- installed Commit caller. A different service handle fails at that site.
section
open Zkc.Source ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBearModel (model)
variable {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment} {Aux E : Type}
  [SampleableType (model.Field FriSource.extension)]
  (oracles : List (CheckedOracle snapshot domains math)) (ordinary : PublishedSampling.Network model Aux E)
  (fieldAudit : PublishedWords.Table model → model.Field FriSource.extension → List E)
  (indexAudit : PublishedWords.Table model → Fin 32 → List E)
  (choose : PublishedWords.Chooser ProbComp model Aux E)

private abbrev enteredCommit := FriSourceCalls.commitment.childContext FriSource.lowDegreeContext
private noncomputable abbrev servicesAt (service : Nat) :=
  CommitChallenge.handler oracles ordinary enteredCommit service fieldAudit indexAudit choose

noncomputable example (service : Nat) :
    RetainedSampling.Fresh (servicesAt oracles ordinary fieldAudit indexAudit choose service) service :=
  CommitChallenge.freshPositions oracles ordinary enteredCommit service fieldAudit indexAudit choose

example (state : CommitPublication.State model snapshot domains math Aux) :
    servicesAt oracles ordinary fieldAudit indexAudit choose 0 (FriCommitRound.drawRequest enteredCommit 1) state =
      pure ⟨.stopped .refused, state, []⟩ :=
  CommitChallenge.wrongService oracles ordinary enteredCommit 0 fieldAudit indexAudit choose 1 (by decide) state
end

-- On the same reached loop state, changing the sole coefficient from zero
-- to one flips the verifier's actual terminal guard. Even if its cursor
-- stops, no execution of the second suffix can return the remembered vector.
section
open Zkc.Source ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open FriCheckRound (coefficientsPort rememberedPort)
open VerifierTerminalGuard
example (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (env : Environment (FriBinding.Value model) Γ) (c : Octic)
    (selected : env coefficientsPort = OracleProtocol.concrete model (.vector FriSource.extension) [c]) :
    FriCheckRound.roundSite.next.denote (terminalMeaning context) (env.prepend (finalValues 0 0 4 1)) =
      OracleProtocol.withMarks (FriCheckRound.roundSite.continuationMarks context)
        (if c = 0 then .done (.cons (env rememberedPort) .nil) else .halt .reject) := by
  simpa [terminal, evaluate] using
    (VerifierTerminalGuard.installed context receiver env [c] selected 1 one_ne_zero (k := 2) (by decide)
      ⟨0, by decide⟩ (show 1 < indexLimit by decide) 0)

example : coefficientsPort.index ≠ rememberedPort.index := by decide +kernel

-- Cutting through the outer callback as though its nested body executed
-- exactly once would erase the trip count and change early-stop behavior.
example : FriCheckRound.roundOccurrence.onSpine = false := by kernel_rfl
end

-- On an invalid mathematical path the actual loop can reject or encounter a
-- cursor refusal. A returned vector, even the expected vector, is excluded.
section
open Zkc.Source ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBearModel (model)
example {Aux : Type} (before after : VerifierPath.Store Aux)
    (vector : Values (FriBinding.Value model) FriCheckRound.roundSite.outputs) :
    ¬ VerifierPath.outcome false vector before (.returned vector) after := by
  simp [VerifierPath.outcome]

-- A matching path cannot return with one read missing from the ledger.
example {Aux : Type} (before : VerifierPath.Store Aux)
    (vector : Values (FriBinding.Value model) FriCheckRound.roundSite.outputs) :
    ¬ VerifierPath.outcome true vector (VerifierPath.charged before 8) (.returned vector)
      (VerifierPath.charged before 7) := by
  rintro (⟨_, wrong⟩ | stopped)
  swap
  · cases stopped
  have count := congrArg (fun s : VerifierPath.Store Aux ↦ s.queries) wrong
  simp only [VerifierPath.charged] at count
  omega

-- In the three-fold, eight-sample instance, coalescing one repeated
-- position would perform only seven complete paths. The actual outer
-- loop's successful return rules out that read count even for equal cells.
example {Aux : Type} (store : VerifierPath.Store Aux) (returned : Values (FriBinding.Value model) FriCheckPositions.querySite.outputs) :
    ¬ VerifierPath.outcome true returned (VerifierPath.charged store (4 * 3 * 8))
      (.returned returned) (VerifierPath.charged store (4 * 3 * 7)) := by
  rintro (⟨_, kept⟩ | refused)
  · have count := congrArg (fun s : VerifierPath.Store Aux ↦ s.queries) kept
    simp only [VerifierPath.charged] at count
    omega
  · cases refused
end

-- A scalar or Boolean terminal payload does not encode a coefficient vector,
-- even at the expected terminal origin.
example (sites : ObservedLayers.Sites) : ObservedLayers.decode sites 2 0 3
    [.message sites.terminal (.boolean true)] = none := by
  simp [ObservedLayers.decode, Zkc.Construction.Domain.Payload.value]

-- The entry root remembers the exact earlier word and challenge values in order.
example (sites : ObservedLayers.Sites) (prior : ObservedFold.History)
    (layers : Layers ZkcSecurity.Domains.KoalaBear.Octic 5 3) :
    ObservedLayers.atRoot sites 5 3 (prior ++ ObservedLayers.observations sites 0 layers) =
      some layers := ObservedLayers.atRoot_observations sites prior layers

-- The actual word expression chooses an antipodal pair, not the original row.
example : bitAnd 31 (wrappingSubtract (logicalShiftRight 32 1) 1) = 15 := by decide
example : wrappingAdd 15 16 = 31 := by decide
example : bitAnd 31 (wrappingSubtract 32 1) ≠ 15 := by decide

-- Dropping the source's representable row-size premise is unsound at log size 64.
example : bitAnd (2 ^ 64 - 1)
    (wrappingSubtract (logicalShiftRight (2 ^ 64) 1) 1) ≠ (2 ^ 64 - 1) % 2 ^ 63 := by decide

-- Exact current padding rejects the overlength mathematical case.
example : ¬ (([1, 2, 3] : List ℚ) ++ List.replicate (2 - 3) 0).length = 2 := by decide
example : bounded 1 ([1] : List ℚ) = true ∧ ([1] : List ℚ).length ≠ 2 ^ 1 := by decide

section
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.FriSourceBodies
open ZkcSecurity.Domains.KoalaBear (Octic)

-- The installed helper rejects the two-cell input at width one; truncation
-- would turn this mutation into an apparently valid terminal message.
example {I : PIR.Signature} (a b : Octic) :
    invoke (RetainedFold.helpers (I := I)).closed helper21Helper (.cons [a, b] (.cons 1 .nil)) =
      .halt .reject := by
  refine (HolderPadding.installed [a, b] 1 (show 2 < indexLimit by decide) (by decide)).trans ?_
  rfl

-- Even the canonical empty list from interpolating zero produces one sent zero.
example {I : PIR.Signature} :
    invoke (RetainedFold.helpers (I := I)).closed helper21Helper (.cons [] (.cons 1 .nil)) =
      .done (.cons [(0 : Octic)] .nil) := by
  refine (HolderPadding.installed (I := I) [] 1 (by decide) (by decide)).trans ?_
  rfl
end

-- Sampled equality does not identify unsampled positions.
example : ∃ initial : Fin 2 → ℕ, initial 0 = 0 ∧ initial ≠ (fun _ ↦ 0) := by
  refine ⟨Fin.val, rfl, ?_⟩
  intro equality
  have atOne := congrFun equality 1
  norm_num at atOne

-- Duplicate positions still have distinct query ordinals: both checks must hold.
example : ¬ ∃ initial : Fin 2 → ℕ, ∀ query : Fin 2, initial 0 = query.val := by
  rintro ⟨initial, checks⟩
  have zero := checks 0
  have one := checks 1
  norm_num at zero one
  omega

-- The last head of the unchanged dimension-one demo cannot meet the new Johnson premise.
example : ¬ 2 ≤ degreeBound 0 (2 ^ 0) := by decide

private theorem certificate_sixteen : IsJohnsonWeightedCertificate 16 3 9 1 2 6 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight, johnsonWeightedHeightInt,
    johnsonWeightedMoment, johnsonWeightedSlope, johnsonWeightedN, johnsonWeightedW,
    johnsonWeightedR, johnsonWeightedT, johnsonWeightedU, Finset.sum_range_succ]

private theorem certificate_eight : IsJohnsonWeightedCertificate 8 1 5 1 1 4 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight, johnsonWeightedHeightInt,
    johnsonWeightedMoment, johnsonWeightedSlope, johnsonWeightedN, johnsonWeightedW,
    johnsonWeightedR, johnsonWeightedT, johnsonWeightedU, Finset.sum_range_succ]

private theorem threshold_sixteen : 9 ≤ ⌈(16 : ℝ) * (1 - 12 / 25)⌉₊ := by
  have exact : ⌈(16 : ℝ) * (1 - 12 / 25)⌉₊ = 9 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [exact]

private theorem threshold_eight : 5 ≤ ⌈(8 : ℝ) * (1 - 12 / 25)⌉₊ := by
  have exact : ⌈(8 : ℝ) * (1 - 12 / 25)⌉₊ = 5 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [exact]

-- A wrong integer threshold cannot be substituted even when the certificate is valid.
example : ¬ 10 ≤ ⌈(16 : ℝ) * (1 - 12 / 25)⌉₊ := by
  have exact : ⌈(16 : ℝ) * (1 - 12 / 25)⌉₊ = 9 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [exact]
  decide

variable {F : Type} [Field F] [Fintype F] [SampleableType F]

/-- Two different nontrivial head budgets, in the order consumed by `FoldingProximity`. -/
noncomputable def twoRoundError (F : Type) [Fintype F] (round : ℕ) : ENNReal :=
  if round = 0 then min 1 (ENNReal.ofReal ((763 : ℝ) / 3 / Fintype.card F))
  else min 1 (ENNReal.ofReal ((103 : ℝ) / 4 / Fintype.card F))

/-- Assembly checks the degree shift, subdomain and error shift at both rounds. -/
theorem weighted_two_round_proximity (domain : SmoothCosetFftDomain 5 F) :
    FoldingProximity 1 (12 / 25) domain 2 (twoRoundError F) := by
  apply foldingProximity_cons_weightedJohnson (R := 1) (t := 1) (radius := 12 / 25)
      (error := twoRoundError F) (A := 9) (multiplicity := 1) (B := 2) (H := 6)
      domain (by decide) certificate_sixteen (by decide) (by decide) (by decide)
      threshold_sixteen
  · norm_num [twoRoundError, degreeBound, johnsonWeightedRefinedExceptionCount]
  · apply foldingProximity_cons_weightedJohnson (R := 0) (t := 1) (radius := 12 / 25)
        (error := fun round ↦ twoRoundError F (round + 1))
        (A := 5) (multiplicity := 1) (B := 1) (H := 4)
        (domain.subdomain 1) (by decide) certificate_eight (by decide) (by decide) (by decide)
        threshold_eight
    · norm_num [twoRoundError, degreeBound, johnsonWeightedRefinedExceptionCount]
    · trivial

/-- The ordinary Johnson constructor also supplies a nonempty proximity chain. -/
theorem johnson_one_round_proximity (domain : SmoothCosetFftDomain 5 F) :
    FoldingProximity 2 (1 - johnsonAgreement 16 3 (1 / 4)) domain 1
      (fun _ ↦ min 1 (ENNReal.ofReal
        (johnsonExceptionCount 16 3 ⌈johnsonAgreement 16 3 (1 / 4) * 16⌉₊ (1 / 4) /
          (Fintype.card F : ℝ)))) := by
  apply foldingProximity_cons_johnson (R := 0) (t := 2) (eta := 1 / 4)
    domain (by decide) (by decide) (by norm_num)
  · have root : Real.sqrt ((3 : ℝ) / 16) ≤ 3 / 4 := Real.sqrt_le_iff.mpr (by norm_num)
    norm_num [degreeBound, johnsonAgreement, johnsonRhoMinus] at *
    linarith
  · rfl
  · exact le_rfl
  · trivial

variable [DecidableEq F]

/-- The assembled chain supplies the existing all-words escape API without a new engine. -/
theorem weighted_two_round_escapes (domain : SmoothCosetFftDomain 5 F) :
    FoldingEscapes 1 (12 / 25) domain 2 (twoRoundError F) :=
  foldingEscapes_of_proximity 1 (12 / 25) domain 2 _ (weighted_two_round_proximity domain)

/-- A client of the existing ideal soundness theorem, still conditional on geometry and roots. -/
theorem weighted_two_round_soundness (roots : ℕ → F) (shift : F) (queries : ℕ)
    (domain : SmoothCosetFftDomain 5 F)
    (geometry : ∀ i : Fin (2 ^ 5), domain i = point roots shift 5 i)
    (compatible : Compatible roots 5 2) (distance : ℝ)
    (prover : ProbComp ((Fin (2 ^ 5) → F) × Strategy F 5 2)) :
    Pr{let result ← experiment roots 1 shift queries prover}[
      result.2 = true ∧ Far domain (degreeBound 2 (2 ^ 1)) distance
        (toTrace 1 domain result.1).initial] ≤
      (∑ round ∈ Finset.range 2, twoRoundError F round) +
        ENNReal.ofReal (1 - min (12 / 25) distance) ^ queries :=
  soundness roots 1 queries domain shift geometry compatible (12 / 25) distance _
    (weighted_two_round_proximity domain) prover

end TestsArkLib.FriAdoption

-- Audit every declaration in the three new production modules, not just selected roots.
run_cmd (ZkcTools.DeclarationAudit.check
  [`ZkcArkLib.Fri.JohnsonBounds, `ZkcArkLib.Fri.Johnson, `ZkcArkLib.Fri.SourceCalculations]
  "FRI-MATHEMATICAL-ADAPTERS-PASS" (exactModules := true))

run_cmd (ZkcTools.DeclarationAudit.checkBoundary
  [`ZkcArkLib.Fri.JohnsonBounds, `ZkcArkLib.Fri.Johnson, `ZkcArkLib.Fri.SourceCalculations]
  [`ArkLib] [] "FRI-JOHNSON-UPSTREAM-BOUNDARY-PASS")

run_cmd ZkcTools.DeclarationAudit.checkCurrent "FRI-ADOPTION-CONTROLS-PASS"

run_cmd (ZkcTools.DeclarationAudit.check
  [`Zkc.Source.Structured.Bindings.MarkedSpine, `Zkc.Source.Structured.OracleQueryDerivation,
   `ZkcExamples.Structured.FriIndexCollections,
   `ZkcExamples.Structured.FriScalarLoop, `ZkcExamples.Structured.FriBoundedPositions,
   `ZkcExamples.Structured.FriBinding, `ZkcExamples.Structured.FriApplications,
   `ZkcArkLibExamples.Fri.RetainedQueries, `ZkcArkLibExamples.Fri.RetainedSampling,
   `ZkcArkLibExamples.Fri.PublishedSampling] "FRI-INSTALLED-SCALAR-SAMPLING-PASS" (exactModules := true))

run_cmd (ZkcTools.DeclarationAudit.check
  [`Zkc.Semantics.HandlerReturn, `Zkc.Source.Structured.OracleForwarding,
   `Zkc.Source.Structured.OracleLocalAction, `Zkc.Source.Structured.ReceiverForwarding,
   `ZkcExamples.Structured.FriBindingExecution] "FRI-RECEIVER-FORWARDING-PASS" (exactModules := true))

run_cmd (ZkcTools.DeclarationAudit.check
  [`ZkcArkLibExamples.Fri.RetainedDomain,
   `ZkcArkLibExamples.Fri.RetainedFold,
   `ZkcArkLibExamples.Fri.HolderFold,
   `ZkcArkLibExamples.Fri.HolderInterpolation,
   `ZkcArkLibExamples.Fri.HolderPadding,
   `ZkcArkLibExamples.Fri.ObservedFold,
   `ZkcArkLibExamples.Fri.ObservedLayers,
   `ZkcArkLibExamples.Fri.ObservedQueries,
   `ZkcArkLibExamples.Fri.TranscriptCharge,
   `ZkcArkLibExamples.Fri.TranscriptTrace,
   `ZkcArkLibExamples.Fri.ClearSites,
   `ZkcArkLibExamples.Fri.ClearCertificate] "FRI-RETAINED-CERTIFICATE-BOUNDARIES-PASS" (exactModules := true))


run_cmd (ZkcTools.DeclarationAudit.check
  [`Zkc.Semantics.CallRestriction, `Zkc.Source.Structured.OracleReadEffects,
   `Zkc.Source.Structured.OracleReadback, `ZkcExamples.Structured.FriPower,
   `ZkcExamples.Structured.FriVirtualBody, `ZkcArkLibExamples.Fri.VirtualReads,
   `ZkcArkLibExamples.Fri.VirtualWord, `Zkc.Source.Structured.RegisteredWord,
   `ZkcArkLibExamples.Fri.VirtualStore, `ZkcArkLibExamples.Fri.VerifierTerminal,
   `Zkc.Source.Structured.Bindings.Continuation, `Zkc.Source.Structured.Bindings.RepeatPrefix,
   `ZkcArkLibExamples.Fri.VerifierTerminalGuard, `ZkcArkLibExamples.Fri.VerifierPath,
   `Zkc.Source.Structured.MarkedReturn, `ZkcExamples.Structured.FriPeeledQuery, `ZkcArkLibExamples.Fri.VerifierQuery,
   `ZkcArkLibExamples.Fri.VerifierQueries, `Zkc.Source.RegionReturnProjection, `Zkc.Source.Structured.ReceiverMetadata,
   `ZkcExamples.Structured.FriCheckAdmission, `ZkcArkLibExamples.Fri.VerifierCheck,
   `Zkc.Source.Structured.OracleVirtualInstallation, `ZkcArkLibExamples.Fri.CommitVirtual]
  "FRI-VERIFIER-READS-AND-TERMINAL-PASS" (exactModules := true))

run_cmd (ZkcTools.DeclarationAudit.check
  [`Zkc.Source.Structured.OracleMetadata, `Zkc.Source.Structured.MarkedPrefix, `Zkc.Source.Structured.MarkedPublication,
   `ZkcExamples.Structured.FriValueAssociation, `ZkcExamples.Structured.FriCheckPositions,
   `Zkc.Source.Structured.ProtocolEmbeddingCheck, `ZkcExamples.Structured.FriPairIndex,
   `ZkcExamples.Structured.FriCheckRound, `ZkcArkLibExamples.Fri.VerifierInitialRead, `ZkcArkLibExamples.Fri.VerifierRound]
  "FRI-VERIFIER-CELLS-AND-ROUNDS-PASS" (exactModules := true))

run_cmd (ZkcTools.DeclarationAudit.check
  [`Zkc.Source.RegionSelection, `ZkcExamples.Structured.FriCommitRound, `ZkcArkLibExamples.Fri.CommitGeometry,
   `ZkcArkLibExamples.Fri.BinaryDomain, `ZkcArkLibExamples.Fri.CommitCaptures, `ZkcArkLibExamples.Fri.CommitDelivery,
   `Zkc.Source.Structured.RegisteredLifetime, `ZkcArkLibExamples.Fri.CommitIteration,
   `ZkcArkLibExamples.Fri.CommitLoop, `ZkcArkLibExamples.Fri.CommitReadback,
   `ZkcArkLibExamples.Fri.CommitPublication,
   `ZkcArkLibExamples.Fri.CommitChallenge]
  "FRI-PUBLICATION-BEFORE-CHALLENGE-PASS" (exactModules := true))

run_cmd (ZkcTools.DeclarationAudit.check
  [`ZkcExamples.Structured.FriSourceCalls, `ZkcExamples.Structured.FriPhaseCalls,
   `ZkcExamples.Structured.FriLowDegreeCall, `ZkcExamples.Structured.FriQueryCall]
  "FRI-SOURCE-DERIVED-PHASE-CALLS-PASS" (exactModules := true))
