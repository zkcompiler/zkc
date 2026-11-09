module

public import Zkc.IR.Source.Structured.Catalogue

@[expose] public section

/-! Installed catalogue rows, generated from `common/catalog/declarations.json`.
Regenerate with support/installed_catalogue.py --write;
checks/check_installed_catalogue.py refuses a module that differs from a fresh
rendering.

Every installed domain row and random service, in declaration order, in the
encoding of exported rows. Which rows the Lean readers admit is decided in
`CatalogueEnvironment`, not here. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Installed

def Domains.«merlin3.koala-bear.ext8-binomial3.rejection31le/0» : Nominal where
  identity := "merlin3.koala-bear.ext8-binomial3.rejection31le/0"
  sort := .transcript
  members := [("ChallengeField", "koala-bear.ext8-binomial3")]
  capabilities := ["FieldTranscript", "IndexTranscript", "Transcript"]
  modulus := none

def Domains.«hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0» : Nominal where
  identity := "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0"
  sort := .transcript
  members := [("ChallengeField", "koala-bear.ext8-binomial3")]
  capabilities := ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"]
  modulus := none

def Domains.«hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0» : Nominal where
  identity := "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"
  sort := .transcript
  members := [("ChallengeField", "koala-bear.ext4-binomial3")]
  capabilities := ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"]
  modulus := none

def Domains.«hash-chain.keccak256.bls12-381.fr64be/0» : Nominal where
  identity := "hash-chain.keccak256.bls12-381.fr64be/0"
  sort := .transcript
  members := [("ChallengeField", "bls12-381.fr")]
  capabilities := ["FieldTranscript", "Transcript"]
  modulus := none

def Domains.«rows.merkle-keccak256.koala-bear/0» : Nominal where
  identity := "rows.merkle-keccak256.koala-bear/0"
  sort := .commitment
  members := [("ValueField", "koala-bear")]
  capabilities := ["VectorCommitment", "MultiOpening"]
  modulus := none

def Domains.«rows.merkle-keccak256.koala-bear.ext8-binomial3/0» : Nominal where
  identity := "rows.merkle-keccak256.koala-bear.ext8-binomial3/0"
  sort := .commitment
  members := [("ValueField", "koala-bear.ext8-binomial3")]
  capabilities := ["VectorCommitment", "MultiOpening"]
  modulus := none

def Domains.«rows.merkle-keccak256.koala-bear.ext4-binomial3/0» : Nominal where
  identity := "rows.merkle-keccak256.koala-bear.ext4-binomial3/0"
  sort := .commitment
  members := [("ValueField", "koala-bear.ext4-binomial3")]
  capabilities := ["VectorCommitment", "MultiOpening"]
  modulus := none

def Domains.«rows.merkle-poseidon2-16.koala-bear/0» : Nominal where
  identity := "rows.merkle-poseidon2-16.koala-bear/0"
  sort := .commitment
  members := [("ValueField", "koala-bear")]
  capabilities := ["VectorCommitment", "MultiOpening"]
  modulus := none

def Domains.«rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0» : Nominal where
  identity := "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0"
  sort := .commitment
  members := [("ValueField", "koala-bear.ext4-binomial3")]
  capabilities := ["VectorCommitment", "MultiOpening"]
  modulus := none

def Characteristics.«gf2-64.pentanomial-4-3-1» : Nat := 2
def Domains.«gf2-64.pentanomial-4-3-1» : Nominal where
  identity := "gf2-64.pentanomial-4-3-1"
  sort := .field
  members := []
  capabilities := ["Field", "CommRing"]
  modulus := some Characteristics.«gf2-64.pentanomial-4-3-1»

def Characteristics.«gf2-64.pentanomial-4-3-1.ext3-trinomial1» : Nat := 2
def Domains.«gf2-64.pentanomial-4-3-1.ext3-trinomial1» : Nominal where
  identity := "gf2-64.pentanomial-4-3-1.ext3-trinomial1"
  sort := .field
  members := [("BaseField", "gf2-64.pentanomial-4-3-1")]
  capabilities := ["ExtensionField", "Field", "CommRing"]
  modulus := some Characteristics.«gf2-64.pentanomial-4-3-1.ext3-trinomial1»

def Characteristics.«bn254.fr» : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617
def Domains.«bn254.fr» : Nominal where
  identity := "bn254.fr"
  sort := .field
  members := [("PairingG1", "bn254.g1"), ("PairingG2", "bn254.g2"), ("PairingGT", "bn254.gt")]
  capabilities := ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "TwoAdicField", "PairingField"]
  modulus := some Characteristics.«bn254.fr»

def Domains.«bn254.g1» : Nominal where
  identity := "bn254.g1"
  sort := .group
  members := [("Scalar", "bn254.fr")]
  capabilities := ["Group", "ScalarAction"]
  modulus := none

def Domains.«bn254.g2» : Nominal where
  identity := "bn254.g2"
  sort := .group
  members := [("Scalar", "bn254.fr")]
  capabilities := ["Group", "ScalarAction"]
  modulus := none

def Domains.«bn254.gt» : Nominal where
  identity := "bn254.gt"
  sort := .group
  members := [("Scalar", "bn254.fr")]
  capabilities := ["Group", "ScalarAction"]
  modulus := none

def Characteristics.«bls12-381.fr» : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513
def Domains.«bls12-381.fr» : Nominal where
  identity := "bls12-381.fr"
  sort := .field
  members := [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")]
  capabilities := ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"]
  modulus := some Characteristics.«bls12-381.fr»

def Domains.«bls12-381.g2» : Nominal where
  identity := "bls12-381.g2"
  sort := .group
  members := [("Scalar", "bls12-381.fr")]
  capabilities := ["Group", "ScalarAction"]
  modulus := none

def Domains.«bls12-381.gt» : Nominal where
  identity := "bls12-381.gt"
  sort := .group
  members := [("Scalar", "bls12-381.fr")]
  capabilities := ["Group", "ScalarAction"]
  modulus := none

def Characteristics.«ristretto255.scalar» : Nat := 7237005577332262213973186563042994240857116359379907606001950938285454250989
def Domains.«ristretto255.scalar» : Nominal where
  identity := "ristretto255.scalar"
  sort := .field
  members := []
  capabilities := ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo"]
  modulus := some Characteristics.«ristretto255.scalar»

def Domains.«ristretto255.group» : Nominal where
  identity := "ristretto255.group"
  sort := .group
  members := [("Scalar", "ristretto255.scalar")]
  capabilities := ["Group", "ScalarAction"]
  modulus := none

def Domains.«edwards25519.prime» : Nominal where
  identity := "edwards25519.prime"
  sort := .group
  members := [("Scalar", "ristretto255.scalar")]
  capabilities := ["Group", "ScalarAction"]
  modulus := none

def Domains.«merlin3.ristretto255.scalar64le/0» : Nominal where
  identity := "merlin3.ristretto255.scalar64le/0"
  sort := .transcript
  members := [("ChallengeField", "ristretto255.scalar")]
  capabilities := ["FieldTranscript", "Transcript"]
  modulus := none

def Domains.«bls12-381.g1» : Nominal where
  identity := "bls12-381.g1"
  sort := .group
  members := [("Scalar", "bls12-381.fr")]
  capabilities := ["Group", "ScalarAction"]
  modulus := none

def Domains.«multilinear.kzg.bls12-381/0» : Nominal where
  identity := "multilinear.kzg.bls12-381/0"
  sort := .commitment
  members := [("ValueField", "bls12-381.fr"), ("PointField", "bls12-381.fr"), ("EvaluationField", "bls12-381.fr")]
  capabilities := ["MultilinearOpening"]
  modulus := none

def Domains.«spongefish0.8.0.keccak.bls12-381.fr64be/0» : Nominal where
  identity := "spongefish0.8.0.keccak.bls12-381.fr64be/0"
  sort := .transcript
  members := [("ChallengeField", "bls12-381.fr")]
  capabilities := ["FieldTranscript", "Transcript"]
  modulus := none

def Domains.«merlin3.bls12-381.fr64be/0» : Nominal where
  identity := "merlin3.bls12-381.fr64be/0"
  sort := .transcript
  members := [("ChallengeField", "bls12-381.fr")]
  capabilities := ["FieldTranscript", "Transcript"]
  modulus := none

def Characteristics.«koala-bear» : Nat := 2130706433
def Domains.«koala-bear» : Nominal where
  identity := "koala-bear"
  sort := .field
  members := []
  capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"]
  modulus := some Characteristics.«koala-bear»

def Characteristics.«koala-bear.ext8-binomial3» : Nat := 2130706433
def Domains.«koala-bear.ext8-binomial3» : Nominal where
  identity := "koala-bear.ext8-binomial3"
  sort := .field
  members := [("BaseField", "koala-bear")]
  capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"]
  modulus := some Characteristics.«koala-bear.ext8-binomial3»

def Characteristics.«koala-bear.ext4-binomial3» : Nat := 2130706433
def Domains.«koala-bear.ext4-binomial3» : Nominal where
  identity := "koala-bear.ext4-binomial3"
  sort := .field
  members := [("BaseField", "koala-bear")]
  capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"]
  modulus := some Characteristics.«koala-bear.ext4-binomial3»

def Characteristics.«baby-bear» : Nat := 2013265921
def Domains.«baby-bear» : Nominal where
  identity := "baby-bear"
  sort := .field
  members := []
  capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"]
  modulus := some Characteristics.«baby-bear»

def Characteristics.«baby-bear.ext4-binomial11» : Nat := 2013265921
def Domains.«baby-bear.ext4-binomial11» : Nominal where
  identity := "baby-bear.ext4-binomial11"
  sort := .field
  members := [("BaseField", "baby-bear")]
  capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"]
  modulus := some Characteristics.«baby-bear.ext4-binomial11»

def Characteristics.«goldilocks» : Nat := 18446744069414584321
def Domains.«goldilocks» : Nominal where
  identity := "goldilocks"
  sort := .field
  members := []
  capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"]
  modulus := some Characteristics.«goldilocks»

def Characteristics.«goldilocks.ext2-binomial7» : Nat := 18446744069414584321
def Domains.«goldilocks.ext2-binomial7» : Nominal where
  identity := "goldilocks.ext2-binomial7"
  sort := .field
  members := [("BaseField", "goldilocks")]
  capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"]
  modulus := some Characteristics.«goldilocks.ext2-binomial7»

def Domains.«merlin3.baby-bear.ext4-binomial11.rejection31le/0» : Nominal where
  identity := "merlin3.baby-bear.ext4-binomial11.rejection31le/0"
  sort := .transcript
  members := [("ChallengeField", "baby-bear.ext4-binomial11")]
  capabilities := ["FieldTranscript", "IndexTranscript", "Transcript"]
  modulus := none

def Domains.«merlin3.goldilocks.ext2-binomial7.rejection64le/0» : Nominal where
  identity := "merlin3.goldilocks.ext2-binomial7.rejection64le/0"
  sort := .transcript
  members := [("ChallengeField", "goldilocks.ext2-binomial7")]
  capabilities := ["FieldTranscript", "IndexTranscript", "Transcript"]
  modulus := none

def Domains.«rows.merkle-poseidon2-16.baby-bear/0» : Nominal where
  identity := "rows.merkle-poseidon2-16.baby-bear/0"
  sort := .commitment
  members := [("ValueField", "baby-bear")]
  capabilities := ["VectorCommitment", "MultiOpening"]
  modulus := none

def Domains.«rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0» : Nominal where
  identity := "rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0"
  sort := .commitment
  members := [("ValueField", "baby-bear.ext4-binomial11")]
  capabilities := ["VectorCommitment", "MultiOpening"]
  modulus := none

def Domains.«rows.merkle-poseidon2-8.goldilocks/0» : Nominal where
  identity := "rows.merkle-poseidon2-8.goldilocks/0"
  sort := .commitment
  members := [("ValueField", "goldilocks")]
  capabilities := ["VectorCommitment", "MultiOpening"]
  modulus := none

def Domains.«rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0» : Nominal where
  identity := "rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0"
  sort := .commitment
  members := [("ValueField", "goldilocks.ext2-binomial7")]
  capabilities := ["VectorCommitment", "MultiOpening"]
  modulus := none

def Services.«random.bls12-381.fr/0» : Service where
  contract := "random.bls12-381.fr/0"
  sampled := "bls12-381.fr"
  methods := ["draw"]

def Services.«random.bn254.fr/0» : Service where
  contract := "random.bn254.fr/0"
  sampled := "bn254.fr"
  methods := ["draw"]

def Services.«random.ristretto255.scalar/0» : Service where
  contract := "random.ristretto255.scalar/0"
  sampled := "ristretto255.scalar"
  methods := ["draw"]

def Services.«random.koala-bear.ext8-binomial3/0» : Service where
  contract := "random.koala-bear.ext8-binomial3/0"
  sampled := "koala-bear.ext8-binomial3"
  methods := ["draw", "index", "indices"]

def Services.«random.koala-bear.ext4-binomial3/0» : Service where
  contract := "random.koala-bear.ext4-binomial3/0"
  sampled := "koala-bear.ext4-binomial3"
  methods := ["draw", "index", "indices"]

def Services.«random.baby-bear.ext4-binomial11/0» : Service where
  contract := "random.baby-bear.ext4-binomial11/0"
  sampled := "baby-bear.ext4-binomial11"
  methods := ["draw", "index", "indices"]

def Services.«random.goldilocks.ext2-binomial7/0» : Service where
  contract := "random.goldilocks.ext2-binomial7/0"
  sampled := "goldilocks.ext2-binomial7"
  methods := ["draw", "index", "indices"]

/-- Every installed domain row and random service. -/
def catalogue : Catalogue where
  nominals := [
    Domains.«merlin3.koala-bear.ext8-binomial3.rejection31le/0»,
    Domains.«hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0»,
    Domains.«hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0»,
    Domains.«hash-chain.keccak256.bls12-381.fr64be/0»,
    Domains.«rows.merkle-keccak256.koala-bear/0»,
    Domains.«rows.merkle-keccak256.koala-bear.ext8-binomial3/0»,
    Domains.«rows.merkle-keccak256.koala-bear.ext4-binomial3/0»,
    Domains.«rows.merkle-poseidon2-16.koala-bear/0»,
    Domains.«rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0»,
    Domains.«gf2-64.pentanomial-4-3-1»,
    Domains.«gf2-64.pentanomial-4-3-1.ext3-trinomial1»,
    Domains.«bn254.fr»,
    Domains.«bn254.g1»,
    Domains.«bn254.g2»,
    Domains.«bn254.gt»,
    Domains.«bls12-381.fr»,
    Domains.«bls12-381.g2»,
    Domains.«bls12-381.gt»,
    Domains.«ristretto255.scalar»,
    Domains.«ristretto255.group»,
    Domains.«edwards25519.prime»,
    Domains.«merlin3.ristretto255.scalar64le/0»,
    Domains.«bls12-381.g1»,
    Domains.«multilinear.kzg.bls12-381/0»,
    Domains.«spongefish0.8.0.keccak.bls12-381.fr64be/0»,
    Domains.«merlin3.bls12-381.fr64be/0»,
    Domains.«koala-bear»,
    Domains.«koala-bear.ext8-binomial3»,
    Domains.«koala-bear.ext4-binomial3»,
    Domains.«baby-bear»,
    Domains.«baby-bear.ext4-binomial11»,
    Domains.«goldilocks»,
    Domains.«goldilocks.ext2-binomial7»,
    Domains.«merlin3.baby-bear.ext4-binomial11.rejection31le/0»,
    Domains.«merlin3.goldilocks.ext2-binomial7.rejection64le/0»,
    Domains.«rows.merkle-poseidon2-16.baby-bear/0»,
    Domains.«rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0»,
    Domains.«rows.merkle-poseidon2-8.goldilocks/0»,
    Domains.«rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0»]
  services := [
    Services.«random.bls12-381.fr/0»,
    Services.«random.bn254.fr/0»,
    Services.«random.ristretto255.scalar/0»,
    Services.«random.koala-bear.ext8-binomial3/0»,
    Services.«random.koala-bear.ext4-binomial3/0»,
    Services.«random.baby-bear.ext4-binomial11/0»,
    Services.«random.goldilocks.ext2-binomial7/0»]

end Zkc.Source.Structured.Installed
