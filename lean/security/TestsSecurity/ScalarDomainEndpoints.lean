module

public import ZkcExamples.Construction.SchnorrProof
public import ZkcExamples.Construction.SchnorrAndProof
public import ZkcExamples.Construction.ChaumPedersenProof
public import ZkcExamples.Construction.OkamotoProof
public import ZkcExamples.Construction.GuessProof
public import ZkcExamples.Construction.SumcheckProof
public import ZkcSecurity.Claims.StageLinks

@[expose] public section

/-! Operational boundary controls for the scalar endpoint model transition.
These controls quantify over raw typed proofs and opaque initial histories;
no honest-input or relation premise restricts the checked source transport. -/
set_option autoImplicit false
namespace TestsSecurity.ScalarDomainEndpoints
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Embedding and exact unread projection preserve every typed payload. -/
example (proof : Proof F G) :
    ScalarVerifier.proof (Uniform.DomainAdapter.embedProof proof) = some proof :=
  ScalarVerifier.proof_embed proof

/-- Oversize vectors and round counts are included in the operational theorem. -/
example (challenge : History F G → m F) (values : List F) (claim : F) (rounds handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    SumcheckProof.compiledVerifier challenge values claim rounds initial proof =
      transform SumcheckProof.context challenge (SumcheckProof.verifier values claim rounds handle)
        initial proof :=
  SumcheckProof.compiled_transform challenge values claim rounds handle initial proof

/-- The scalar legacy map is fixed by the actual repeated artifact. -/
example (origin : Origin) : ScalarVerifier.origin SumcheckProof.participant origin =
    Origin.withoutCoordinates origin := rfl

/-- Finite artifacts use literal origins, independent of security evidence. -/
example (origin : Origin) : ScalarVerifier.origin SchnorrProof.participant origin = origin := rfl

/-- Opaque initial history is not decoded as a nominal history suffix. -/
example (initial : History F G) :
    Uniform.DomainAdapter.readbackValue SumcheckProof.context.suite
      (ScalarVerifier.origin SumcheckProof.participant) initial
      (.transcript SumcheckProof.context.suite []) = some (.transcript initial) := by
  simp [Uniform.DomainAdapter.readbackValue, Uniform.DomainAdapter.readbackHistory]

/-- The generic evidence exposes only the equation for its fixed artifact. -/
example {art : ZkcSecurity.Endpoint.Artifacts} (compiled : ZkcSecurity.Endpoint.Compiled art)
    (connection : compiled.SourceConnection (F := F) (G := G))
    (challenge : History F G → m F) (statement : art.Statement F G) (handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    compiled.verifier challenge statement initial proof =
      transform compiled.context challenge (compiled.original statement handle) initial proof :=
  connection.equation challenge statement handle initial proof

/-- Static admission cannot manufacture a source connection by reflexivity. -/
example {art : ZkcSecurity.Endpoint.Artifacts} (_compiled : ZkcSecurity.Endpoint.Compiled art) : True := by
  fail_if_success
    have forged : _compiled.SourceConnection (F := F) (G := G) := ⟨by intros; rfl⟩
  trivial

end TestsSecurity.ScalarDomainEndpoints
