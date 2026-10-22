module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import ZkcSecurity.Endpoint.Knowledge

@[expose] public section

/-! Operational replay extraction independent of Sigma evidence. Structural
response layouts fix componentwise recovery, witness coordinates and sampling. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
namespace ZkcSecurity.Endpoint.Extraction
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- Scalar leaves or products, with explicit private-input coordinates. -/
inductive Layout where
  | scalar (input : Nat)
  | pair (left right : Layout)
  deriving DecidableEq, Repr

abbrev Layout.Carrier (F : Type) : Layout → Type
  | .scalar _ => F
  | .pair left right => left.Carrier F × right.Carrier F

instance Layout.sampleable (F : Type) [SampleableType F] : (layout : Layout) →
    SampleableType (layout.Carrier F)
  | .scalar _ => inferInstanceAs (SampleableType F)
  | .pair left right =>
    letI := left.sampleable F
    letI := right.sampleable F
    inferInstanceAs (SampleableType (left.Carrier F × right.Carrier F))

/-- Response difference, applied to every scalar component. -/
def Layout.recover {F : Type} [Field F] (layout : Layout) :
    F → layout.Carrier F → F → layout.Carrier F → layout.Carrier F :=
  match layout with
  | .scalar _ => fun first response₁ second response₂ => (response₁ - response₂) / (first - second)
  | .pair a b => fun first response₁ second response₂ =>
      (a.recover first response₁.1 second response₂.1, b.recover first response₁.2 second response₂.2)
termination_by structural layout

@[simp] theorem Layout.recover_scalar {F : Type} [Field F] (input : Nat) (c₁ z₁ c₂ z₂ : F) :
    (Layout.scalar input).recover c₁ z₁ c₂ z₂ = (z₁ - z₂) / (c₁ - c₂) := rfl

@[simp] theorem Layout.recover_pair {F : Type} [Field F] (a b : Layout) (c₁ c₂ : F)
    (z₁ z₂ : (a.pair b).Carrier F) :
    (a.pair b).recover c₁ z₁ c₂ z₂ = (a.recover c₁ z₁.1 c₂ z₂.1, b.recover c₁ z₁.2 c₂ z₂.2) := rfl

/-- Every independent response has one private-input coordinate. -/
def Layout.coordinates : Layout → List Nat
  | .scalar input => [input]
  | .pair left right => left.coordinates ++ right.coordinates

/-- Repeated uses of a coordinate share its assigned value. Admission rules
out assigning two independent response components to the same coordinate. -/
def Layout.read {F : Type} (layout : Layout) : layout.Carrier F → Nat → Option F :=
  match layout with
  | .scalar coordinate => fun witness input => if input = coordinate then some witness else none
  | .pair a b => fun witness input => a.read witness.1 input <|> b.read witness.2 input
termination_by structural layout

@[simp] theorem Layout.read_scalar {F : Type} (coordinate : Nat) (witness : F) (input : Nat) :
    (Layout.scalar coordinate).read witness input = (if input = coordinate then some witness else none) := rfl

@[simp] theorem Layout.read_pair {F : Type} (a b : Layout) (witness : (a.pair b).Carrier F) (input : Nat) :
    (a.pair b).read witness input = (a.read witness.1 input <|> b.read witness.2 input) := rfl

/-- Collect the retained relation's actual scalar witness inputs. Its support
proof separately enforces private producer roles and excludes output ports. -/
def witnessCoordinates {signature : ProtocolSignature} (domain : String) :
    List String → {types : List Ty} → Values (BoundarySelector signature) types → Option (List Nat)
  | [], _, .nil => some []
  | purpose :: purposes, _, .cons (ty := type) selector rest => do
      let tail ← witnessCoordinates domain purposes rest
      if purpose = "witness" then
        if type = .field domain then return selector.port.index :: tail else none
      else return tail
  | _, _, _ => none

def Layout.admitted {snapshot : Structured.Snapshot} {imported : Structured.Imported snapshot}
    {policy : Policy} {publics : List Ty} (layout : Layout)
    (target : RetainedTarget imported policy publics) (domain : String) : Bool :=
  match witnessCoordinates domain target.application.relation.declaration.purposes target.application.selectors with
  | none => false
  | some coordinates => decide layout.coordinates.Nodup &&
      coordinates.all layout.coordinates.contains && layout.coordinates.all coordinates.contains

def Layout.embed {F G : Type} {snapshot : Structured.Snapshot}
    {imported : Structured.Imported snapshot} {policy : Policy} {publics : List Ty}
    (layout : Layout) (target : RetainedTarget imported policy publics)
    (witness : layout.Carrier F) : target.Witness F G :=
  fun type selector => match type with
    | .field _ => layout.read witness selector.port.index
    | _ => none

-- Materialize these shared unfolding equations in their owning module. Lazy
-- client-local generation would give the same public equation distinct stored
-- proof providers, which the declaration-closure audit correctly rejects.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Layout.embed

section Replay
variable {F Commit Resp Wit M : Type} [DecidableEq M] [DecidableEq Commit]
  [DecidableEq F] [SampleableType F] [SampleableType Wit]

/-- Ordinary prover trace with its final verification query. -/
def runTrace (verify : (M × Commit →ₒ F).QueryCache → Commit → Resp → Bool)
    (prover : M → OracleComp (unifSpec + (M × Commit →ₒ F)) (Commit × Resp))
    (message : M) : OracleComp (_root_.FiatShamir.Fork.wrappedSpec F)
      (_root_.FiatShamir.Fork.Trace Commit F Resp M) := do
  let ((forgery, cache), state) ← StateT.run (simulateQ
    (_root_.FiatShamir.Fork.unifForward M Commit F + _root_.FiatShamir.Fork.roImpl M Commit F) (do
      let proof ← prover message
      let _ ← HasQuery.query (spec := M × Commit →ₒ F) (message, proof.1)
      return ((message, proof), ∅))) (∅, [])
  let verified := verify state.1 forgery.2.1 forgery.2.2
  return ⟨forgery, cache, state.1, state.2, verified⟩

/-- Failed forks use the fixed carrier sampler. Successful forks use exactly
`recover`; the claims layer fixes it to response difference. -/
def recoverFork (recover : F → Resp → F → Resp → ProbComp Wit) :
    Option (_root_.FiatShamir.Fork.Trace Commit F Resp M ×
      _root_.FiatShamir.Fork.Trace Commit F Resp M) →
      OracleComp (_root_.FiatShamir.Fork.wrappedSpec F) Wit
  | none => liftComp ($ᵗ Wit) (_root_.FiatShamir.Fork.wrappedSpec F)
  | some (first, second) =>
      if first.forgery.2.1 = second.forgery.2.1 then
        match first.roCache first.target, second.roCache second.target with
        | some left, some right =>
            if left ≠ right then
              liftComp (recover left first.forgery.2.2 right second.forgery.2.2)
                (_root_.FiatShamir.Fork.wrappedSpec F)
            else liftComp ($ᵗ Wit) (_root_.FiatShamir.Fork.wrappedSpec F)
        | _, _ => liftComp ($ᵗ Wit) (_root_.FiatShamir.Fork.wrappedSpec F)
      else liftComp ($ᵗ Wit) (_root_.FiatShamir.Fork.wrappedSpec F)

def replay (verify : (M × Commit →ₒ F).QueryCache → Commit → Resp → Bool)
    (recover : F → Resp → F → Resp → ProbComp Wit)
    (prover : M → OracleComp (unifSpec + (M × Commit →ₒ F)) (Commit × Resp))
    (message : M) (queries : Nat) : ProbComp Wit :=
  simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := Unit →ₒ F))
    (contextFork (runTrace verify prover message) (_root_.FiatShamir.nmaForkBudget queries)
      (Sum.inr ()) (_root_.FiatShamir.Fork.forkPoint Commit F Resp M queries) >>=
        recoverFork recover)

/-- Operational compatibility requires no special-soundness assumption. -/
theorem replay_eq {Stmt PrvState : Type} {relation : Stmt → Wit → Bool}
    (sigma : SigmaProtocol Stmt Wit Commit PrvState F Resp relation)
    (generable : GenerableRelation Stmt Wit relation)
    (prover : _root_.FiatShamir.KnowledgeProver Stmt Commit F Resp M)
    (statement : Stmt) (message : M) (queries : Nat) :
    replay (fun cache commitment response => match cache (message, commitment) with
      | some challenge => sigma.verify statement commitment challenge response
      | none => false) sigma.extract (prover statement) message queries =
      _root_.FiatShamir.knowledgeExtractor sigma generable M prover message queries statement := by
  have trace : runTrace (fun cache commitment response => match cache (message, commitment) with
      | some challenge => sigma.verify statement commitment challenge response
      | none => false) (prover statement) message =
      _root_.FiatShamir.Fork.runTrace sigma generable M
        (_root_.FiatShamir.proverWithFinalQuery sigma generable M prover message) statement := by
    simp only [runTrace, _root_.FiatShamir.Fork.runTrace, _root_.FiatShamir.proverWithFinalQuery,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, monad_norm]
    apply bind_congr
    intro first
    apply bind_congr
    intro second
    cases second.2.1 (message, first.1.1) <;> rfl
  have branch : recoverFork (M := M) sigma.extract =
      _root_.FiatShamir.nmaForkExtractBranch (M := M) sigma := by
    funext pair
    cases pair with
    | none => rfl
    | some pair =>
      rcases pair with ⟨⟨⟨m₁, c₁, s₁⟩, a₁, r₁, l₁, v₁⟩, ⟨⟨m₂, c₂, s₂⟩, a₂, r₂, l₂, v₂⟩⟩
      simp only [recoverFork, _root_.FiatShamir.nmaForkExtractBranch, _root_.FiatShamir.Fork.Trace.target, dite_eq_ite]
      by_cases same : c₁ = c₂
      · simp only [same, ite_true]
        cases r₁ (m₁, c₁) <;> cases r₂ (m₂, c₂) <;> rfl
      · simp only [same, ite_false]
  unfold replay _root_.FiatShamir.knowledgeExtractor _root_.FiatShamir.nmaReduction
    _root_.FiatShamir.nmaForkExtract
  rw [trace, branch]

end Replay
end ZkcSecurity.Endpoint.Extraction
