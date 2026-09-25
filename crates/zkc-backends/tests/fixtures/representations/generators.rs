/// Pinned upstream outputs, not an implementation of hash-to-point. Input is the
/// output of cn_fast_hash(H || "bulletproof_plus" || varint(index)); upstream
/// hash_to_p3 hashes this input again, maps it, and clears the cofactor.
/// Generated with Monero commit 4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5,
/// src/ringct/bulletproofs_plus.cc:get_exponent and rctOps.cpp:hash_to_p3.
/// Even indices select Hi, odd indices Gi. Test data, not runtime generator setup.
#[derive(Clone, Copy, Debug)]
pub struct MoneroGeneratorVector {
    pub index: usize,
    pub hash_to_p3_input_hex: &'static str,
    pub encoded_point_hex: &'static str,
}
pub const MONERO_GENERATOR_VECTORS: &[MoneroGeneratorVector] = &[
    MoneroGeneratorVector {
        index: 0,
        hash_to_p3_input_hex: "d76df7e68bc32eba02f368668444a48f7cfb50357b5c2d0dc9da49c34ef91fe3",
        encoded_point_hex: "48628df380a5016d25451aaa501731a11b72bf66dc41d81f719abd35ce92b0ed",
    },
    MoneroGeneratorVector {
        index: 1,
        hash_to_p3_input_hex: "4ef63d1888aa2fa6dc0bbe44007f6b8ccac356d67e8d27e39bfdc128aa883c0b",
        encoded_point_hex: "38c5d4db53aeb86f5a80def9be4953f2288ed5a44c66af723f463d0170829010",
    },
    MoneroGeneratorVector {
        index: 2,
        hash_to_p3_input_hex: "d6741d57bf8dc9fb7829803e547b680b7d935b7f6d9448b0cd3bd8dee8b38fa8",
        encoded_point_hex: "110d2b61f8c7c10861c3e4ffe7774faba632af94854aa29538517aefe6a39e48",
    },
    MoneroGeneratorVector {
        index: 3,
        hash_to_p3_input_hex: "499c63dc4c809871c504413fc1165f0cfcad4e69e9c81e5cac1b3f2e17acca99",
        encoded_point_hex: "8a6c817dabe90fdb50cc38677b23ffa7d64efeb00bbd53febe62e077de0db593",
    },
    MoneroGeneratorVector {
        index: 127,
        hash_to_p3_input_hex: "7b738646ddec49d4263600ab819c8556615912f5056d01982ae016542b9c5853",
        encoded_point_hex: "46e9e2d3586dfd893745c0957bfab3cc005a1a6c51ce25f065815603eab1160c",
    },
    MoneroGeneratorVector {
        index: 128,
        hash_to_p3_input_hex: "926ddc0c4d1bd7ae64c29945b772bb25d3ffcddf676f047b9e8f3bbb1c2612ef",
        encoded_point_hex: "27e947e7f5a975edb6f35f63c19df3a8a34d9c8112fa9f0ffe20109b8eb42585",
    },
    MoneroGeneratorVector {
        index: 2047,
        hash_to_p3_input_hex: "14f44d45414a87c9a69232278da60caf7d738546a6f655d6a94c01788d37ce4c",
        encoded_point_hex: "c844fd242df1f97224ec816f980096d005a5c78e6c1498f0fc57af4b08f5e7e8",
    },
];
