module

public import Zkc.Protocols.Schnorr.NativeConstruction
public import ZkcSecurity.Examples.SchnorrFiatShamir

@[expose] public section

/-! Refusal controls for each state/signature boundary in the native ideal interpretation. -/
namespace ZkcSecurity.Examples.SchnorrConstructionControls
open Zkc.Source Zkc.Protocols.Schnorr
open SchnorrFiatShamir

def transcript : NativeConstruction.Transcript String Scalar Scalar := { binding := binding }
def proof : Scalar × Scalar := (3, 3)

def groupObserve : Constructed.Primitive :=
  ⟨"crypto.exec.indexed_transcript_observe_data", "", "", "",
    ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">",
     "!algebra.group<\"bls12-381.g1\">", "!algebra.indices"],
    ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]⟩
def fieldObserve : Constructed.Primitive :=
  { groupObserve with arguments :=
    ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">",
     "!algebra.field<\"bls12-381.fr\">", "!algebra.indices"] }
def sample : Constructed.Primitive :=
  ⟨"crypto.exec.indexed_transcript_challenge", "", "", "",
    ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">", "!algebra.indices"],
    ["!algebra.field<\"bls12-381.fr\">",
     "!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]⟩

abbrev interpret := NativeConstruction.primitive (Context := String) proof

theorem unsupported_primitive_refused :
    interpret ⟨"unsupported", "", "", "", [], []⟩ .nil = .halt .refused := rfl

theorem wrong_type_signature_refused :
    interpret { sample with arguments := [] } .nil = .halt .refused := rfl

theorem commitment_required :
    interpret sample (.cons transcript (.cons [] .nil)) = .halt .refused := rfl

theorem commitment_observed_once :
    interpret groupObserve (.cons { transcript with commitment := some 3 }
      (.cons (3 : Scalar) (.cons [] .nil))) = .halt .refused := rfl

theorem group_coordinates_refused :
    interpret groupObserve (.cons transcript (.cons (3 : Scalar) (.cons [0] .nil))) = .halt .refused := rfl

theorem sample_coordinates_refused :
    interpret sample (.cons { transcript with commitment := some 3 }
      (.cons [0] .nil)) = .halt .refused := rfl

theorem challenge_sampled_once :
    interpret sample (.cons { transcript with commitment := some 3, challenge := some 1 }
      (.cons [] .nil)) = .halt .refused := rfl

theorem challenge_required_for_delivery :
    interpret fieldObserve (.cons transcript (.cons (1 : Scalar) (.cons [] .nil))) = .halt .refused := rfl

theorem wrong_challenge_delivery_refused :
    interpret fieldObserve (.cons { transcript with commitment := some 3, challenge := some 1 }
      (.cons (2 : Scalar) (.cons [] .nil))) = .halt .refused := rfl

theorem field_coordinates_refused :
    interpret fieldObserve (.cons { transcript with commitment := some 3, challenge := some 1 }
      (.cons (1 : Scalar) (.cons [0] .nil))) = .halt .refused := rfl

theorem response_observed_once :
    interpret fieldObserve (.cons { transcript with commitment := some 3, challenge := some 1, delivered := true, response := some 0 } (.cons (1 : Scalar) (.cons [] .nil))) = .halt .refused := rfl

end ZkcSecurity.Examples.SchnorrConstructionControls
