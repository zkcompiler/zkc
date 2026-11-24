module

public import Zkc.Vocabulary.Standard
public import Zkc.Frontend.Semantics.Vocabulary

@[expose] public section

/-!
# Standard names in source

Source interfaces expose mathematical members such as field order and extension degree.
The corresponding type of the standard vocabulary supplies those values. Sealed source
types and the member names of modules are used during signature instantiation.
-/

namespace Zkc.Frontend
namespace StandardNames
open Zkc.Vocabulary (Field CurveGroup)

def fieldName : Field → String
  | .koalaBear => "koala-bear"
  | .koalaBear4 => "koala-bear.ext4"
  | .bls12381Fr => "bls12-381.fr"

def groupName : CurveGroup → String
  | .g1 => "bls12-381.g1"
  | .g2 => "bls12-381.g2"
  | .gt => "bls12-381.gt"

def fields : List Field := [.koalaBear, .koalaBear4, .bls12381Fr]
def groups : List CurveGroup := [.g1, .g2, .gt]

def fieldType (f : Field) : ClosedType := .nominal (fieldName f) #[]
def groupType (g : CurveGroup) : ClosedType := .nominal (groupName g) #[]

def fieldEntry (f : Field) : VocabularyType := Id.run do
  let baseSorts := #["Group", "Ring", "Field"]
  let members := #[("Scalar", fieldType f), ("Prime", fieldType f.prime)]
  let numbers := #[("Order", f.order), ("Characteristic", f.characteristic), ("Dimension", f.dimension),
    ("TwoAdicity", f.twoAdicity)]
  match f.over with
  | none => return ⟨fieldName f, baseSorts ++ #["PrimeField", "TwoAdicField"], members,
      numbers.push ("Bytes", (f.characteristic.log2 + 8) / 8)⟩
  | some (base, degree) => return ⟨fieldName f, baseSorts ++ #["ExtensionField", "TwoAdicField"],
      members.push ("Base", fieldType base), numbers.push ("Degree", degree)⟩

def groupEntry (g : CurveGroup) : VocabularyType :=
  ⟨groupName g, if g = .gt then #["Group"] else #["Group", "PrimeOrderGroup"],
    #[("Scalar", fieldType .bls12381Fr)], #[("Order", Field.bls12381Fr.order)]⟩

/-- Sealed types are available for source typing. Their runtime representations belong to
the extension that provides their operations. -/
def sealedTypes : Array VocabularyType :=
  #["oracle.handle", "oracle.claim", "suite.merlin3.bls12-381.fr64be/0.state",
    "suite.merlin3.bls12-381.fr64be/0.label"].map fun name => ⟨name, #[], #[], #[]⟩

def named (row : String) : ClosedType := .nominal row #[]

def sourceVocabulary : Vocabulary where
  types := (fields.map fieldEntry ++ groups.map groupEntry).toArray ++ sealedTypes
  modules := #[
    { row := "bls12-381", implements := some "zkc::algebra::Pairing"
      typeMembers := #[("Scalar", named "bls12-381.fr"), ("G1", named "bls12-381.g1"),
        ("G2", named "bls12-381.g2"), ("Target", named "bls12-381.gt")]
      naturalMembers := #[], standardFunctions := [("pair", "pairing.pair")] },
    { row := "hash.sha256", implements := some "zkc::hash::Hash", typeMembers := #[]
      naturalMembers := #[("Size", 32)], standardFunctions := [("hash", "hash.sha256")] },
    { row := "hash.keccak256", implements := some "zkc::hash::Hash", typeMembers := #[]
      naturalMembers := #[("Size", 32)], standardFunctions := [("hash", "hash.keccak256")] },
    { row := "hash.shake128", implements := some "zkc::hash::ExtendableOutput"
      typeMembers := #[], naturalMembers := #[], standardFunctions := [("output", "hash.shake128")] },
    { row := "hash.shake256", implements := some "zkc::hash::ExtendableOutput"
      typeMembers := #[], naturalMembers := #[], standardFunctions := [("output", "hash.shake256")] },
    { row := "suite.merlin3.bls12-381.fr64be/0", implements := some "zkc::construction::Suite"
      typeMembers := #[("Challenge", named "bls12-381.fr"),
        ("State", named "suite.merlin3.bls12-381.fr64be/0.state")]
      naturalMembers := #[("ChallengeUnits", 64), ("PositionUnits", 16)] },
    { row := "suite.poseidon2-duplex.koala-bear/0", implements := some "zkc::construction::Suite"
      typeMembers := #[("Challenge", named "koala-bear.ext4")]
      naturalMembers := #[("ChallengeUnits", 4), ("PositionUnits", 1)] },
    { row := "suite.schnorr-signature", implements := none
      typeMembers := #[("Challenge", named "bls12-381.fr")]
      naturalMembers := #[("ChallengeUnits", 64), ("PositionUnits", 16)] },
    { row := "suite.ml-dsa", implements := none, typeMembers := #[]
      naturalMembers := #[("ChallengeUnits", 32), ("PositionUnits", 8)] }]
  representatives := #[("Group", "bls12-381.gt"), ("PrimeOrderGroup", "bls12-381.g1"),
    ("Ring", "koala-bear"), ("Field", "koala-bear"), ("PrimeField", "koala-bear"),
    ("TwoAdicField", "koala-bear"), ("ExtensionField", "koala-bear.ext4")]

end StandardNames

def vocabulary : Vocabulary := StandardNames.sourceVocabulary

end Zkc.Frontend
