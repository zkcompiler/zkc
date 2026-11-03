//! The frame tags the native codec writes and reads, each read at build time
//! from the catalog's codec or aggregate-frame row. A tag whose row is removed
//! or loses its frame fails the build.
use zkc_runtime::catalog::{aggregate_frame_tag, codec_tag};

pub(crate) const BLS_FIELD: u8 = codec_tag("zkcv.field.bls12-381.fr/0");
pub(crate) const BLS_TABLE: u8 = codec_tag("zkcv.table.bls12-381.fr/0");
pub(crate) const BLS_VECTOR: u8 = codec_tag("zkcv.vector.bls12-381.fr/0");
pub(crate) const BLS_MATRIX: u8 = codec_tag("zkcv.matrix.bls12-381.fr/0");
pub(crate) const BLS_G1: u8 = codec_tag("zkcv.group.bls12-381.g1/0");
pub(crate) const BLS_G1_VECTOR: u8 = codec_tag("zkcv.groups.bls12-381.g1/0");
pub(crate) const BLS_G2: u8 = codec_tag("zkcv.group.bls12-381.g2/0");
pub(crate) const BLS_G2_VECTOR: u8 = codec_tag("zkcv.groups.bls12-381.g2/0");
pub(crate) const BLS_GT: u8 = codec_tag("zkcv.group.bls12-381.gt/0");
pub(crate) const KZG_COMMITMENT: u8 = codec_tag("zkcv.commitment.multilinear-kzg.bls12-381/0");
pub(crate) const KZG_PROOF: u8 = codec_tag("zkcv.proof.multilinear-kzg.bls12-381/0");
pub(crate) const BN254_FIELD: u8 = codec_tag("zkcv.field.bn254.fr/0");
pub(crate) const BN254_VECTOR: u8 = codec_tag("zkcv.vector.bn254.fr/0");
pub(crate) const BN254_MATRIX: u8 = codec_tag("zkcv.matrix.bn254.fr/0");
pub(crate) const BN254_G1: u8 = codec_tag("zkcv.group.bn254.g1/0");
pub(crate) const BN254_G1_VECTOR: u8 = codec_tag("zkcv.groups.bn254.g1/0");
pub(crate) const BN254_G2: u8 = codec_tag("zkcv.group.bn254.g2/0");
pub(crate) const BN254_G2_VECTOR: u8 = codec_tag("zkcv.groups.bn254.g2/0");
pub(crate) const BN254_GT: u8 = codec_tag("zkcv.group.bn254.gt/0");
pub(crate) const RISTRETTO_FIELD: u8 = codec_tag("zkcv.field.ristretto255.scalar/0");
pub(crate) const RISTRETTO_VECTOR: u8 = codec_tag("zkcv.vector.ristretto255.scalar/0");
pub(crate) const RISTRETTO_MATRIX: u8 = codec_tag("zkcv.matrix.ristretto255.scalar/0");
pub(crate) const RISTRETTO_GROUP: u8 = codec_tag("zkcv.group.ristretto255.group/0");
pub(crate) const RISTRETTO_GROUPS: u8 = codec_tag("zkcv.groups.ristretto255.group/0");
pub(crate) const EDWARDS_GROUP: u8 = codec_tag("zkcv.group.edwards25519.prime/0");
pub(crate) const EDWARDS_GROUPS: u8 = codec_tag("zkcv.groups.edwards25519.prime/0");
pub(crate) const BINARY_FIELD: u8 = codec_tag("zkcv.field.gf2-64.pentanomial-4-3-1/0");
pub(crate) const BINARY_VECTOR: u8 = codec_tag("zkcv.vector.gf2-64.pentanomial-4-3-1/0");
pub(crate) const BINARY_MATRIX: u8 = codec_tag("zkcv.matrix.gf2-64.pentanomial-4-3-1/0");
pub(crate) const BINARY_EXT3_FIELD: u8 =
    codec_tag("zkcv.field.gf2-64.pentanomial-4-3-1.ext3-trinomial1/0");
pub(crate) const BINARY_EXT3_VECTOR: u8 =
    codec_tag("zkcv.vector.gf2-64.pentanomial-4-3-1.ext3-trinomial1/0");
pub(crate) const BINARY_EXT3_MATRIX: u8 =
    codec_tag("zkcv.matrix.gf2-64.pentanomial-4-3-1.ext3-trinomial1/0");
pub(crate) const BOOL: u8 = codec_tag("zkcv.bool/0");
pub(crate) const INDEX: u8 = codec_tag("zkcv.index/0");
pub(crate) const INDICES: u8 = codec_tag("zkcv.indices/0");
pub(crate) const BYTES: u8 = codec_tag("zkcv.bytes/0");
/// Digest-generic Merkle frames, shared by every scheme of the layout.
pub(crate) const DIGEST_ROOT: u8 =
    codec_tag("zkcv.commitment.rows-merkle-poseidon2-16.koala-bear/0");
pub(crate) const DIGEST_PROOF: u8 = codec_tag("zkcv.proof.rows-merkle-poseidon2-16.koala-bear/0");
pub(crate) const MERKLE_ROOT: u8 = codec_tag("zkcv.commitment.rows-merkle-keccak256.koala-bear/0");
pub(crate) const MERKLE_PATH: u8 = codec_tag("zkcv.proof.rows-merkle-keccak256.koala-bear/0");
pub(crate) const MERKLE_EXT8_ROOT: u8 =
    codec_tag("zkcv.commitment.rows-merkle-keccak256.koala-bear.ext8-binomial3/0");
pub(crate) const MERKLE_EXT8_PATH: u8 =
    codec_tag("zkcv.proof.rows-merkle-keccak256.koala-bear.ext8-binomial3/0");
pub(crate) const MERKLE_EXT4_ROOT: u8 =
    codec_tag("zkcv.commitment.rows-merkle-keccak256.koala-bear.ext4-binomial3/0");
pub(crate) const MERKLE_EXT4_PATH: u8 =
    codec_tag("zkcv.proof.rows-merkle-keccak256.koala-bear.ext4-binomial3/0");
pub(crate) const FIELD_ARRAY: u8 = aggregate_frame_tag("field_array", "bls12-381.fr");
pub(crate) const VARIANT: u8 = aggregate_frame_tag("variant", "");
pub(crate) const SEQUENCE: u8 = aggregate_frame_tag("sequence", "");
