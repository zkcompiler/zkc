module

public import Zkc.Claims.Registry
public import ZkcSecurity.Endpoint.Extraction

@[expose] public section

/-! Request-owned extraction interfaces. These are registered semantic inputs,
not evidence. Version zero fixes structural response-difference recovery. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open OracleComp OracleSpec
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint

def responseDifference : Identifier := ⟨"extractors.response_difference", 0⟩

/-- The author library fixes the transcript interpretation before selecting a
proof method. Recovery and witness embedding are derived from `layout`, never
supplied as functions by the evidence. The site is an actual construction draw. -/
structure ExtractionProfile {art : Artifacts} (compiled : Compiled art) (F G : Type) where
  target : RetainedTarget compiled.imported art.participant.policy art.publics
  layout : Extraction.Layout
  domain : String
  coordinates : layout.admitted target domain = true
  Commit : Type
  decidableCommit : DecidableEq Commit
  shape : Sigma.Shape F G Commit (layout.Carrier F)
  native : String
  delivery : String
  selected : (native, delivery) ∈ compiled.context.draws
  request : Zkc.Construction.Request
  requestSelected : compiled.context.request = some request
  scalarChallenge : request = .draw domain
  challenge : shape.challenge = .challenge (compiled.context.query native request)

attribute [instance] ExtractionProfile.decidableCommit

namespace ExtractionProfile
variable {F G : Type} {art : Artifacts} {compiled : Compiled art}
  (profile : ExtractionProfile compiled F G)

abbrev Witness := profile.layout.Carrier F

instance sampleable [SampleableType F] : SampleableType profile.Witness := profile.layout.sampleable F

def embed (witness : profile.Witness) : profile.target.Witness F G :=
  profile.layout.embed profile.target witness

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def registry (target : SoundnessTarget compiled F G) (selected : target = .retained profile.target) :
    Registry { other : ExtractionProfile compiled F G // target = .retained other.target } :=
  ⟨[⟨responseDifference, "zkc.extractor.response-difference/0", some ⟨profile, selected⟩⟩]⟩

/-- Run the actual verifier against the replay's recorded oracle. Every history
uses its own routed cache entry; an unrecorded query fails rather than receiving
the selected challenge by fiat. This is conservative for general verifiers. -/
def verify (statement : art.Statement F G) (initial : History F G)
    (cache : (Sigma.Key F G profile.Commit →ₒ F).QueryCache)
    (commitment : profile.Commit) (response : profile.Witness) : Bool :=
  ((compiled.verifier (m := Option) (fun history => cache (profile.shape.route history))
    statement initial (profile.shape.proof commitment response)).map verdict).getD false

variable [SampleableType F]

/-- The adversary receives exactly the subject's publications and history.
Its typed output is read through the registered profile, never an evidence key. -/
def extract (statement : art.Statement F G) (initial : History F G)
    (prover : TypedProver F G (art.Statement F G)) (queries : Nat) : ProbComp profile.Witness :=
  Extraction.replay (profile.verify statement initial)
    (fun first left second right => pure (profile.layout.recover first left second right))
    (profile.shape.reduce (fun (_ : Unit) history => profile.shape.read <$> prover statement history) ())
    (.inl initial) queries

end ExtractionProfile
end ZkcSecurity.Claims
