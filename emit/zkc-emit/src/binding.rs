//! The supplier binding: the explicit, emit-time answer to "which
//! concrete implementation realizes each codec class, the sponge, and
//! the algebra" — the profile discipline of `docs/spec/endpoints.md` §4
//! moved from run time to emit time. Every gap is an emitter refusal
//! naming the missing supplier; the emitted crate has no
//! supplier-missing path at all.

use crate::json::{self, Json};

/// The emitter's implementation vocabulary. The binding file selects by
/// name; an unknown name is a refusal, never a fallback.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImplKind {
    /// u64, eight big-endian bytes, toy squeeze derivation.
    ToyBe8,
    /// u32, one canonical BabyBear word, low-bits squeeze derivation.
    P3Word,
    /// [u32; 4], four canonical words least-significant-first, tuple
    /// bijection squeeze.
    P3Ext4,
    /// [u32; 8], eight canonical words; nothing squeezes a digest.
    P3Digest8,
    /// A BLS12-381 scalar: 32 big-endian bytes, canonical-or-reject.
    BlsFrBe32,
    /// A BLS12-381 G1 point: 48 bytes, standard compressed form,
    /// on-curve and in-subgroup or reject.
    BlsG1Be48,
}

impl ImplKind {
    pub fn from_name(name: &str) -> Option<ImplKind> {
        match name {
            "toy_be8" => Some(ImplKind::ToyBe8),
            "p3_word" => Some(ImplKind::P3Word),
            "p3_ext4" => Some(ImplKind::P3Ext4),
            "p3_digest8" => Some(ImplKind::P3Digest8),
            "bls_fr_be32" => Some(ImplKind::BlsFrBe32),
            "bls_g1_be48" => Some(ImplKind::BlsG1Be48),
            _ => None,
        }
    }

    pub fn rust_type(self) -> &'static str {
        match self {
            ImplKind::ToyBe8 => "u64",
            ImplKind::P3Word => "u32",
            ImplKind::P3Ext4 => "[u32; 4]",
            ImplKind::P3Digest8 => "[u32; 8]",
            ImplKind::BlsFrBe32 => "zkc_rt::kzg::Fr",
            ImplKind::BlsG1Be48 => "zkc_rt::kzg::G1",
        }
    }

    pub fn wire_width(self) -> usize {
        match self {
            ImplKind::ToyBe8 => 8,
            ImplKind::P3Word => 4,
            ImplKind::P3Ext4 => 16,
            ImplKind::P3Digest8 => 32,
            ImplKind::BlsFrBe32 => 32,
            ImplKind::BlsG1Be48 => 48,
        }
    }

    /// The zkc-rt cargo feature this implementation lives behind.
    pub fn feature(self) -> &'static str {
        match self {
            ImplKind::ToyBe8 => "toy",
            ImplKind::BlsFrBe32 | ImplKind::BlsG1Be48 => "kzg",
            _ => "plonky3",
        }
    }

    /// How many 32-bit limbs the type carries (for statement literals).
    pub fn limbs(self) -> usize {
        match self {
            ImplKind::ToyBe8 => 2,
            ImplKind::P3Word => 1,
            ImplKind::P3Ext4 => 4,
            ImplKind::P3Digest8 => 8,
            ImplKind::BlsFrBe32 => 8,
            ImplKind::BlsG1Be48 => 12,
        }
    }
}

/// The executable adapters for opaque check contracts, selected by the
/// contract's content digest — the same dispatch authority the
/// reference executor names when it refuses (zkc-E403).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckImpl {
    /// `zkc.check.kzg-opening`: e(C - y*g1, g2) == e(W, tau_g2 - z*g2).
    KzgOpening,
    /// `zkc.check.kzg-batch-opening`: the gamma-folded same-point form.
    KzgBatchOpening,
}

impl CheckImpl {
    pub fn from_name(name: &str) -> Option<CheckImpl> {
        match name {
            "kzg_bls12_381_opening" => Some(CheckImpl::KzgOpening),
            "kzg_bls12_381_batch_opening" => Some(CheckImpl::KzgBatchOpening),
            _ => None,
        }
    }
}

/// One bound check adapter. `tau_g2` is setup material — the pinned SRS
/// point the suite resolves — supplied by the binding, never by the
/// artifact; a test binding pins a known-tau point and says so.
#[derive(Debug, Clone)]
pub struct CheckBinding {
    pub implementation: CheckImpl,
    pub suite: String,
    pub tau_g2_hex: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpongeImpl {
    ToyDuplex,
    P3LenpadDuplex,
}

impl SpongeImpl {
    pub fn from_name(name: &str) -> Option<SpongeImpl> {
        match name {
            "toy_duplex" => Some(SpongeImpl::ToyDuplex),
            "p3_lenpad_duplex" => Some(SpongeImpl::P3LenpadDuplex),
            _ => None,
        }
    }

    pub fn feature(self) -> &'static str {
        match self {
            SpongeImpl::ToyDuplex => "toy",
            SpongeImpl::P3LenpadDuplex => "plonky3",
        }
    }
}

#[derive(Debug, Clone)]
pub struct ClassBinding {
    /// The codec name this implementation claims to realize; it must
    /// equal the document's baked route for the class.
    pub codec: String,
    pub implementation: ImplKind,
    /// The canonical modulus gate for decoded wire values and statement
    /// binding, when the class declares one (decimal).
    pub modulus: Option<u64>,
}

#[derive(Debug, Clone)]
pub struct AlgebraBinding {
    pub group: u64,
    pub field: u64,
}

#[derive(Debug, Clone)]
pub struct Binding {
    pub name: String,
    pub sponge_construction: String,
    pub sponge_iv: String,
    pub sponge_impl: SpongeImpl,
    pub algebra: Option<AlgebraBinding>,
    pub classes: Vec<(String, ClassBinding)>,
    /// Contract digest → executable adapter for opaque checks.
    pub checks: Vec<(String, CheckBinding)>,
    /// `tagged-name → sha256:<hex>`: the construction digests these
    /// suppliers claim to realize, compared against the artifact's pins.
    pub digests: Vec<(String, String)>,
    /// SHA-256 of the binding file bytes, lowercase hex (provenance).
    pub digest_of_file: String,
}

fn string_field(object: &Json, key: &str, context: &str) -> Result<String, String> {
    object
        .get(key)
        .and_then(Json::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("binding: {context} has no string field '{key}'"))
}

fn decimal_u64(text: &str, context: &str) -> Result<u64, String> {
    text.parse::<u64>()
        .map_err(|_| format!("binding: {context} '{text}' is not a decimal u64"))
}

impl Binding {
    pub fn parse(bytes: &[u8]) -> Result<Binding, String> {
        use sha2::{Digest, Sha256};
        let digest_of_file = Sha256::digest(bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();

        let root = json::parse(bytes)?;
        let name = string_field(&root, "name", "binding")?;

        let sponge = root.get("sponge").ok_or("binding has no sponge object")?;
        let sponge_construction = string_field(sponge, "construction", "sponge")?;
        let sponge_iv = string_field(sponge, "iv", "sponge")?;
        let sponge_impl_name = string_field(sponge, "impl", "sponge")?;
        let sponge_impl = SpongeImpl::from_name(&sponge_impl_name).ok_or_else(|| {
            format!("binding: unknown sponge implementation '{sponge_impl_name}'")
        })?;

        let algebra = match root.get("algebra") {
            None => None,
            Some(value) => {
                let group =
                    decimal_u64(&string_field(value, "group", "algebra")?, "algebra group")?;
                let field =
                    decimal_u64(&string_field(value, "field", "algebra")?, "algebra field")?;
                Some(AlgebraBinding { group, field })
            }
        };

        let mut classes = Vec::new();
        for (class, entry) in root
            .get("classes")
            .and_then(Json::as_object)
            .ok_or("binding has no classes object")?
        {
            let codec = string_field(entry, "codec", class)?;
            let impl_name = string_field(entry, "impl", class)?;
            let implementation = ImplKind::from_name(&impl_name).ok_or_else(|| {
                format!("binding: class '{class}' names unknown implementation '{impl_name}'")
            })?;
            let modulus = match entry.get("modulus") {
                None => None,
                Some(value) => Some(decimal_u64(
                    value.as_str().ok_or_else(|| {
                        format!("binding: class '{class}' modulus is not a string")
                    })?,
                    &format!("class '{class}' modulus"),
                )?),
            };
            if modulus.is_some() && implementation != ImplKind::ToyBe8 {
                return Err(format!(
                    "binding: class '{class}' declares a machine-level modulus, but only the \
                     toy implementation gates decoded values that way; the BabyBear codecs \
                     check canonicality per word"
                ));
            }
            classes.push((
                class.clone(),
                ClassBinding {
                    codec,
                    implementation,
                    modulus,
                },
            ));
        }

        let mut checks = Vec::new();
        if let Some(table) = root.get("checks") {
            for (digest, entry) in table
                .as_object()
                .ok_or("binding: checks is not an object")?
            {
                let impl_name = string_field(entry, "impl", digest)?;
                let implementation = CheckImpl::from_name(&impl_name).ok_or_else(|| {
                    format!("binding: check '{digest}' names unknown adapter '{impl_name}'")
                })?;
                let suite = string_field(entry, "suite", digest)?;
                let tau_g2_hex = string_field(entry, "tau_g2", digest)?;
                if tau_g2_hex.len() != 192
                    || !tau_g2_hex
                        .bytes()
                        .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
                {
                    return Err(format!(
                        "binding: check '{digest}' tau_g2 is not 96 compressed bytes as \
                         lowercase hex"
                    ));
                }
                checks.push((
                    digest.clone(),
                    CheckBinding {
                        implementation,
                        suite,
                        tau_g2_hex,
                    },
                ));
            }
        }

        let mut digests = Vec::new();
        for (tagged, digest) in root
            .get("digests")
            .and_then(Json::as_object)
            .ok_or("binding has no digests object")?
        {
            digests.push((
                tagged.clone(),
                digest
                    .as_str()
                    .map(str::to_owned)
                    .ok_or_else(|| format!("binding: digest for '{tagged}' is not a string"))?,
            ));
        }

        Ok(Binding {
            name,
            sponge_construction,
            sponge_iv,
            sponge_impl,
            algebra,
            classes,
            checks,
            digests,
            digest_of_file,
        })
    }

    pub fn class(&self, class: &str) -> Option<&ClassBinding> {
        self.classes
            .iter()
            .find(|(name, _)| name == class)
            .map(|(_, binding)| binding)
    }

    pub fn check(&self, digest: &str) -> Option<&CheckBinding> {
        self.checks
            .iter()
            .find(|(name, _)| name == digest)
            .map(|(_, check)| check)
    }

    pub fn digest_for(&self, tagged: &str) -> Option<&str> {
        self.digests
            .iter()
            .find(|(name, _)| name == tagged)
            .map(|(_, digest)| digest.as_str())
    }
}
