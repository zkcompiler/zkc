//! Exact invocation-binding serialization of caller-supplied immutable fields.
//! The caller owns source authentication, value import and context authorization.
use crate::logical;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

/// Fields selected and checked by the enclosing deployment consumer. The complete
/// construction descriptor is retained, including all programmable associations.
pub struct Invocation<'a> {
    pub descriptor: &'a Value,
    pub source: &'a str,
    pub entry: &'a str,
    pub producer: &'a str,
    pub validator: &'a str,
    pub context: &'a [u8],
}

impl Invocation<'_> {
    /// Build the ten-slot root before public values are available. Consumers
    /// replace slot 8 with canonical rows after their original import checks.
    pub fn root(&self) -> Value {
        const DIGITS: &[u8] = b"0123456789abcdef";
        let mut context = vec![0; self.context.len() * 2];
        for (pair, &byte) in context.as_chunks_mut::<2>().0.iter_mut().zip(self.context) {
            *pair = [DIGITS[(byte >> 4) as usize], DIGITS[(byte & 15) as usize]];
        }
        let context = String::from_utf8(context).expect("hex digits are ASCII");
        json!([
            "zkc.native-proof-binding/0",
            "sha256",
            self.descriptor[2],
            self.source,
            self.entry,
            self.producer,
            self.validator,
            self.descriptor,
            [],
            context
        ])
    }
}

/// Canonical public bytes are supplied by the consumer's selected value codec.
/// Index and type spellings have already been checked by that consumer.
pub fn public_row<'a>(
    role: &'a str,
    original: &'a str,
    logical_type: &'a str,
    wire: &'a [u8],
) -> [logical::Tree<'a>; 4] {
    [
        logical::Tree::Text(role),
        logical::Tree::Text(original),
        logical::Tree::Text(logical_type),
        logical::Tree::Hex(wire),
    ]
}

/// A digest and optional transcript buffer consume one canonical stream. The
/// buffer is reserved before writing and is unpublished until encoding finishes.
pub fn encode_binding(
    encoding: &logical::Encoding<'_>,
    retain: bool,
) -> Result<(Vec<u8>, [u8; 32]), logical::CodecError> {
    struct Sink {
        bytes: Vec<u8>,
        hash: Sha256,
        retain: bool,
    }
    impl std::io::Write for Sink {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.hash.update(bytes);
            if self.retain {
                self.bytes.extend_from_slice(bytes);
            }
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut sink = Sink {
        bytes: Vec::new(),
        hash: Sha256::new(),
        retain,
    };
    if retain {
        sink.bytes
            .try_reserve_exact(encoding.size())
            .map_err(|_| logical::CodecError("tree-allocation"))?;
    }
    encoding.write(&mut sink).expect("reserved binding sink");
    Ok((sink.bytes, sink.hash.finalize().into()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value as Json, json};
    use zkc_test_support::{hex, unhex};

    #[test]
    fn root_fields_match_the_vector_and_keep_the_complete_descriptor() {
        let vector: Json = serde_json::from_str(include_str!(
            "../../zkc-test-support/fixtures/native-proof-binding.json"
        ))
        .unwrap();
        let expected = &vector["tree"];
        let invocation = Invocation {
            descriptor: &expected[7],
            source: expected[3].as_str().unwrap(),
            entry: "main",
            producer: "P",
            validator: "V",
            context: &[],
        };
        assert_eq!(invocation.root(), *expected);

        let descriptor = json!([
            "zkc.native-proof-descriptor/0",
            "programmable",
            "zkc.native-origin/0",
            [
                "initializer",
                "adapter",
                "record-codec",
                ["complete", "association"]
            ]
        ]);
        let root = Invocation {
            descriptor: &descriptor,
            context: &[0, 0x0f, 0x80, 0xff],
            ..invocation
        }
        .root();
        assert_eq!(root.as_array().unwrap().len(), 10);
        assert_eq!(root[2], descriptor[2]);
        assert_eq!(root[7], descriptor);
        assert_eq!(root[8], json!([]));
        assert_eq!(root[9], "000f80ff");
    }

    #[test]
    fn retained_and_hash_only_bindings_match_the_independent_vector() {
        let vector: Json = serde_json::from_str(include_str!(
            "../../zkc-test-support/fixtures/native-proof-binding.json"
        ))
        .unwrap();
        let expected = unhex(vector["encoded_hex"].as_str().unwrap());
        let encoding = logical::Tree::Json(&vector["tree"]).prepare().unwrap();
        for retain in [true, false] {
            let (bytes, digest) = encode_binding(&encoding, retain).unwrap();
            assert_eq!(hex(&digest), vector["sha256"]);
            assert_eq!(bytes, if retain { expected.as_slice() } else { &[] });
        }
        // Exercise the mixed public-row composition too. The JSON spelling
        // takes the Text path; the borrowed row must expand Hex identically.
        for n in [0, 1, 511, 512, 513, 1024] {
            let wire: Vec<_> = (0..n).map(|i| i as u8).collect();
            let mut tree = vector["tree"].clone();
            tree[8] = json!([["V", "0", "bytes", hex(&wire)]]);
            let expected = logical::encode_tree(&tree).unwrap();
            let row = public_row("V", "0", "bytes", &wire);
            let rows = [logical::Tree::Array(&row)];
            let mut fields: Vec<_> = tree
                .as_array()
                .unwrap()
                .iter()
                .map(logical::Tree::Json)
                .collect();
            fields[8] = logical::Tree::Array(&rows);
            let encoding = logical::Tree::Array(&fields).prepare().unwrap();
            assert_eq!(encoding.size(), expected.len());
            for retain in [true, false] {
                let (bytes, digest) = encode_binding(&encoding, retain).unwrap();
                assert_eq!(digest, <[u8; 32]>::from(Sha256::digest(&expected)));
                assert_eq!(bytes, if retain { expected.as_slice() } else { &[] });
            }
        }
    }
}
