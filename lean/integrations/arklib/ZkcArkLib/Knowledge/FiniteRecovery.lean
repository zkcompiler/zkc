module

public import ZkcSecurity.Commitment.FiniteRecovery
public import ArkLib.Interaction.Oracle.Security.KnowledgeComposition

@[expose] public section

/-! Finite oracle-recovery consumer of pinned ArkLib Knowledge. The request
fixes the sum relation, two-cell read access and straight-line algorithm.
The native extractor is checked against that algorithm, including its exact
received message. No KZG knowledge or general efficient-extractor claim follows.
Upstream: ArkLib 1e0241333c18d8b22cb68f9522da5f9fb88f9a06. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcArkLib.Knowledge.FiniteRecovery
open OracleComp OracleSpec Interaction.Oracle Interaction.Oracle.Security
open ZkcSecurity.Commitment.FiniteRecovery

variable {F : Type} [Add F] [DecidableEq F]

/-- Both cells are readable, after and only after this oracle-send node. -/
@[instance_reducible] def cellInterface : OracleInterface (F × F) where
  Query := Fin 2
  toOC.spec := Access F
  toOC.impl index cells := answers cells index

@[implicit_reducible] def protocol (F : Type) : Protocol :=
  Protocol.oracleWith (F × F) cellInterface Protocol.done

abbrev initial := emptySpec.toPFunctor

def inputImpl : QueryImpl (ofPFunctor initial) Id := fun query => nomatch query

def inputState (request : Request F) : KnowledgeState := ⟨F × F, request.Holds⟩

/-- The concrete message supplies the backward map; the terminal witness is
unit. This is not an existentially chosen witness-search function. -/
def extractor (request : Request F) : RoundExtractor (protocol F).tree (inputState request) :=
  fun cells => ⟨⟨Unit, fun _ => request.Holds cells⟩, (fun _ => cells), PUnit.unit⟩

def certificate (request : Request F) :
    KnowledgeCertificate (protocol F).tree (protocol F).roles (inputState request) where
  extractor := extractor request
  challenges := fun _ => PUnit.unit
  prover_preserving := ⟨fun _ _ holds => holds, fun _ => trivial⟩
  local_bound := fun _ => trivial

omit [DecidableEq F] in
/-- The operational two-query algorithm agrees with the pinned same-path
backward map on every received oracle payload, including invalid witnesses. -/
theorem extract_eq_native (request : Request F) (cells : F × F) :
    evalWithAnswerFn (answers cells) request.extract =
      (extractor request).extractWitness ⟨cells, PUnit.unit⟩ () := by
  rw [extract_eq]
  rfl

/-- Genuine use of upstream deterministic extraction: failure on an accepting
path would require a verifier challenge, and this selected tree has none. -/
theorem native_extraction (request : Request F) (cells : F × F)
    (accepted : ((extractor request).terminalState ⟨cells, PUnit.unit⟩).holds ()) :
    request.Holds (evalWithAnswerFn (answers cells) request.extract) := by
  rw [extract_eq_native]
  by_contra bad
  have impossible := RoundExtractor.extraction_failure_implies_bad_challenge
    (extractor request) (protocol F).roles (certificate request).prover_preserving
    ⟨cells, PUnit.unit⟩ () accepted bad
  exact impossible

omit [Add F] [DecidableEq F] in
/-- The actual handler added by the native oracle receive exposes exactly
these two cells. An earlier resource with the same signature is not selected. -/
theorem latest_access (cells : F × F) (index : Fin 2) :
    Access.extendImpl initial cellInterface inputImpl cells (.inr index) = answers cells index := rfl

/-- Route the fixed request algorithm through the latest received resource. -/
def latestRoute : QueryImpl (Access F)
    (OracleComp (unifSpec + ofPFunctor (Access.extend initial (cellInterface (F := F))))) :=
  fun index => liftM ((ofPFunctor (Access.extend initial (cellInterface (F := F)))).query (.inr index))

/-- One restricted native verifier. Its code has no access to the oracle
payload; the runtime closes its reads with the actual received resource. -/
def verifier (request : Request F) : Verifier.Strategy unifSpec
    (protocol F).tree (protocol F).roles (protocol F).oracles initial (fun _ => Bool) :=
  pure (simulateQ latestRoute request.verifier)

/-- The exact terminal action under the canonical native handler equals the
selected verifier. This binding is also used for honest acceptance below. -/
theorem closed_verifier (request : Request F) (cells : F × F) :
    simulateQ (Verifier.liftAccessImpl unifSpec (Access.extend initial (cellInterface (F := F)))
      (Access.extendImpl initial cellInterface inputImpl cells))
      (simulateQ latestRoute request.verifier) =
        (pure (decide (request.Holds cells)) : ProbComp Bool) := by
  simp only [Request.verifier, Request.extract, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, latestRoute, Verifier.liftAccessImpl,
    Access.extendImpl, cellInterface, answers]
  rfl

/-- The same verifier binding supplies acceptance for a related honest table. -/
theorem honest_accepts (request : Request F) (cells : F × F) (related : request.Holds cells) :
    simulateQ (Verifier.liftAccessImpl unifSpec (Access.extend initial (cellInterface (F := F)))
      (Access.extendImpl initial cellInterface inputImpl cells))
      (simulateQ latestRoute request.verifier) = (pure true : ProbComp Bool) := by
  rw [closed_verifier]
  exact congrArg pure (decide_eq_true related)

/-- The sender chooses one immutable oracle; its randomness precedes recovery. -/
def sender (adversary : ProbComp (F × F)) : Prover.Strategy unifSpec
    (protocol F).tree (protocol F).roles (fun _ => Unit) := do
  let cells ← adversary
  pure ⟨cells, ()⟩

def nativeRun (request : Request F) (adversary : ProbComp (F × F)) :=
  executeStrategies unifSpec (protocol F).tree (protocol F).roles (protocol F).oracles
    initial inputImpl (sender adversary) (verifier request)

/-- Exact native game, including its actual path and private sender output. -/
theorem nativeRun_eq (request : Request F) (adversary : ProbComp (F × F)) :
    nativeRun request adversary = (do
      let cells ← adversary
      pure ⟨⟨cells, PUnit.unit⟩, (), decide (request.Holds cells)⟩) := by
  unfold nativeRun
  change executeStrategies unifSpec (TypeTree.oracle (F × F) (fun _ => TypeTree.done))
    ⟨PUnit.unit, fun _ => PUnit.unit⟩ ⟨cellInterface, fun _ => PUnit.unit⟩ initial inputImpl
    (sender adversary) (verifier request) = _
  rw [executeStrategies_oracle]
  simp only [sender, verifier, bind_assoc, pure_bind, simulateQ_pure, executeStrategies_done]
  dsimp only [protocol, Protocol.done, Protocol.oracleWith, TypeTree.ExecutionPath,
    TypeTree.oracle, TypeTree.done, TypeTree.runtimeLens, PFunctor.FreeM.PathAlong,
    PFunctor.FreeM.Displayed, PFunctor.FreeM.PathAlong.algebra]
  apply bind_congr
  intro cells
  rw [closed_verifier]
  simp only [pure_bind]

/-- Average acceptance equals success of this request's straight-line recovery
on the same sent oracle. There is one run and no witness-search oracle. -/
theorem acceptance_eq_recovery (request : Request F) (adversary : ProbComp (F × F)) :
    Pr{let observed ← (nativeRun request adversary)}[observed.2.2 = true] =
      Pr{let cells ← adversary}[request.Holds (evalWithAnswerFn (answers cells) request.extract)] := by
  rw [nativeRun_eq]
  simp only [← map_eq_pure_bind, prEvent_map, decide_eq_true_eq, extract_eq]

end ZkcArkLib.Knowledge.FiniteRecovery
