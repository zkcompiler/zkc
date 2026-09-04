from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest


ORACLE_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ORACLE_DIR))

import oracle  # noqa: E402


FOUNDATION = oracle.FOUNDATION_PROFILE
IDENTITY_KIND = oracle.IDENTITY_PROFILE_KIND
HASH_KIND = oracle.HASH_SUITE_KIND
REGIME_KIND = oracle.SEMANTIC_REGIME_KIND
IDENTITY_PROFILE = {
    "id_type": "prior-meta",
    "foundation_profile": FOUNDATION,
    "subject_kind": IDENTITY_KIND,
    "digest": oracle.SUPPORTED_IDENTITY_PROFILE_DIGEST,
}
HASH_SUITE = {
    "id_type": "prior-meta",
    "foundation_profile": FOUNDATION,
    "subject_kind": HASH_KIND,
    "digest": oracle.SUPPORTED_HASH_SUITE_DIGEST,
}
FROZEN_REGIME = {
    "id_type": "prior-meta",
    "foundation_profile": FOUNDATION,
    "subject_kind": REGIME_KIND,
    "digest": "0c537a1d1638992bd0c3efd2256ed4c3506ecb96bb6136b6084189de10b86bef",
}


def frame(value: bytes) -> bytes:
    return len(value).to_bytes(8, "big") + value


def base(case: str, operation: str) -> dict[str, object]:
    return {
        "case": case,
        "op": operation,
        "foundation_profile": FOUNDATION,
    }


def id_request(case: str, kind: str, value: object) -> dict[str, object]:
    request = base(case, "content_id")
    request.update(
        {
            "identity_profile": IDENTITY_PROFILE,
            "hash_suite": HASH_SUITE,
            "subject_kind": kind,
            "semantic_regime": FROZEN_REGIME,
            "value": value,
        }
    )
    return request


def prior_meta_request(case: str, kind: str, value: object) -> dict[str, object]:
    request = base(case, "prior_meta_id")
    request.update({"subject_kind": kind, "value": value})
    return request


def prior_reference(identifier: dict[str, str]) -> bytes:
    return (
        frame(identifier["foundation_profile"].encode("ascii"))
        + frame(identifier["subject_kind"].encode("ascii"))
        + bytes.fromhex(identifier["digest"])
    )


class CanonicalValueTests(unittest.TestCase):
    def encode(self, value: object) -> dict[str, object]:
        request = base("encode", "encode")
        request["value"] = value
        result = oracle.process_request(request)
        self.assertEqual(result["outcome"], "Completed", result)
        return result

    def test_exact_scalar_vectors(self) -> None:
        vectors = [
            ({"tag": "unit"}, b"\x00"),
            ({"tag": "bool", "value": False}, b"\x01"),
            ({"tag": "bool", "value": True}, b"\x02"),
            (
                {"tag": "nat", "value": "0"},
                b"\x03" + (1).to_bytes(8, "big") + b"\x00",
            ),
            (
                {"tag": "nat", "value": "256"},
                b"\x03" + (2).to_bytes(8, "big") + b"\x01\x00",
            ),
            (
                {"tag": "int", "value": "-7"},
                b"\x04\x01" + (1).to_bytes(8, "big") + b"\x07",
            ),
            (
                {"tag": "bytes", "value": "00ff"},
                b"\x05" + (2).to_bytes(8, "big") + b"\x00\xff",
            ),
            (
                {"tag": "symbol", "value": "pir.core"},
                b"\x06" + (8).to_bytes(8, "big") + b"pir.core",
            ),
        ]
        for value, expected in vectors:
            with self.subTest(value=value):
                self.assertEqual(self.encode(value)["canonical_hex"], expected.hex())

    def test_exact_composite_vector_and_decode_round_trip(self) -> None:
        symbol = b"\x06" + (8).to_bytes(8, "big") + b"pir.core"
        nat = b"\x03" + (1).to_bytes(8, "big") + b"\x00"
        sequence = b"\x07" + (2).to_bytes(8, "big") + frame(nat) + frame(b"\x02")
        variant = b"\x09" + (3).to_bytes(8, "big") + frame(sequence)
        expected = (
            b"\x08"
            + (2).to_bytes(8, "big")
            + (0).to_bytes(8, "big")
            + frame(symbol)
            + (2).to_bytes(8, "big")
            + frame(variant)
        )
        value = {
            "tag": "record",
            "fields": [
                {
                    "ordinal": "0",
                    "value": {"tag": "symbol", "value": "pir.core"},
                },
                {
                    "ordinal": "2",
                    "value": {
                        "tag": "variant",
                        "case": "3",
                        "value": {
                            "tag": "seq",
                            "items": [
                                {"tag": "nat", "value": "0"},
                                {"tag": "bool", "value": True},
                            ],
                        },
                    },
                },
            ],
        }
        encoded = self.encode(value)
        self.assertEqual(encoded["canonical_hex"], expected.hex())

        request = base("decode", "decode")
        request["canonical_hex"] = expected.hex()
        decoded = oracle.process_request(request)
        self.assertEqual(decoded["outcome"], "Completed")
        self.assertEqual(decoded["value"], value)
        self.assertEqual(decoded["canonical_hex"], expected.hex())

    def test_json_member_order_does_not_affect_identity(self) -> None:
        first_value = {"tag": "nat", "value": "9"}
        second_value = {"value": "9", "tag": "nat"}
        first = oracle.process_request(id_request("first", "pir.core", first_value))
        second = oracle.process_request(id_request("second", "pir.core", second_value))
        self.assertEqual(first["content_id"], second["content_id"])
        self.assertEqual(first["canonical_hex"], second["canonical_hex"])

    def test_noncanonical_binary_forms_refuse(self) -> None:
        leading_zero = b"\x03" + (2).to_bytes(8, "big") + b"\x00\x01"
        negative_zero = b"\x04\x01" + (1).to_bytes(8, "big") + b"\x00"
        unordered_record = (
            b"\x08"
            + (2).to_bytes(8, "big")
            + (1).to_bytes(8, "big")
            + frame(b"\x00")
            + (0).to_bytes(8, "big")
            + frame(b"\x00")
        )
        for encoded in (leading_zero, negative_zero, unordered_record):
            request = base("noncanonical", "decode")
            request["canonical_hex"] = encoded.hex()
            result = oracle.process_request(request)
            self.assertEqual(result["outcome"], "Malformed")
            self.assertEqual(result["code"], "NonCanonical")

    def test_noncanonical_fixture_scalar_forms_refuse(self) -> None:
        values = [
            {"tag": "nat", "value": "01"},
            {"tag": "int", "value": "-0"},
            {"tag": "bytes", "value": "AA"},
            {
                "tag": "record",
                "fields": [
                    {"ordinal": "1", "value": {"tag": "unit"}},
                    {"ordinal": "0", "value": {"tag": "unit"}},
                ],
            },
        ]
        for value in values:
            request = base("noncanonical", "encode")
            request["value"] = value
            result = oracle.process_request(request)
            self.assertEqual(result["outcome"], "Malformed", result)
            self.assertEqual(result["code"], "NonCanonical", result)

    def test_truncated_and_unknown_binary_forms_are_malformed(self) -> None:
        truncated = base("truncated", "decode")
        truncated["canonical_hex"] = "03000000000000000201"
        unknown = base("unknown-tag", "decode")
        unknown["canonical_hex"] = "ff"
        truncated_result = oracle.process_request(truncated)
        unknown_result = oracle.process_request(unknown)
        self.assertEqual(truncated_result["outcome"], "Malformed")
        self.assertEqual(unknown_result["outcome"], "Malformed")
        self.assertEqual(unknown_result["code"], "UnknownTag")


class TypedIdentityTests(unittest.TestCase):
    VALUE = {
        "tag": "record",
        "fields": [
            {"ordinal": "0", "value": {"tag": "symbol", "value": "schnorr"}},
            {"ordinal": "1", "value": {"tag": "nat", "value": "7"}},
        ],
    }

    def verify_request(
        self, case: str, kind: str, value: object, content_id: object
    ) -> dict[str, object]:
        request = base(case, "verify_id")
        request.update(
            {
                "expected_subject_kind": kind,
                "identity_profile": IDENTITY_PROFILE,
                "hash_suite": HASH_SUITE,
                "semantic_regime": FROZEN_REGIME,
                "value": value,
                "content_id": content_id,
            }
        )
        return request

    def test_regime_root_freezes_the_selected_foundation_mechanisms(self) -> None:
        requests = [
            json.loads(line)
            for line in (ORACLE_DIR / "cases" / "requests.jsonl")
            .read_text(encoding="utf-8")
            .splitlines()
        ]
        root = next(item for item in requests if item["case"] == "id-regime-root")
        root_fields = {
            int(field["ordinal"]): field["value"] for field in root["value"]["fields"]
        }
        self.assertEqual(
            root_fields[0],
            {"tag": "symbol", "value": "zkc.foundation.portable-semantics.v0"},
        )
        core_fields = {
            int(field["ordinal"]): field["value"] for field in root_fields[2]["fields"]
        }
        constructors = tuple(item["value"] for item in core_fields[0]["items"])
        self.assertEqual(
            constructors,
            (
                "unit",
                "bool",
                "nat",
                "int",
                "bytes",
                "symbol",
                "seq",
                "record",
                "variant",
                "literal",
                "variable",
                "let",
                "record-construct",
                "project",
                "inject",
                "case",
                "sequence-construct",
                "sequence-length",
                "fail",
                "strict-index",
                "bounded-append",
                "primitive-call",
                "bounded-iterate",
                "conditional",
            ),
        )
        self.assertNotIn("bounded-map", constructors)
        self.assertNotIn("bounded-fold", constructors)
        self.assertNotIn("bounded-find", constructors)
        self.assertNotIn("bounded-pairwise-reduce", constructors)
        law_source = bytes.fromhex(core_fields[1]["value"]).decode("ascii")
        self.assertTrue(law_source.startswith("zkc.foundation.semantic-core-law.v0\n"))
        law_octets = law_source.encode("ascii")
        self.assertEqual(len(law_octets), 45_933)
        self.assertEqual(
            hashlib.sha256(law_octets).hexdigest(),
            "f603cee6ce7acc601ca92a35b3de3787dcd9b9ea47a85486c8f4fb2732212658",
        )
        self.assertIn("source-encoding=ASCII-0x20..0x7e;", law_source)
        self.assertIn(
            "selected-limits=axis-octets<=1048576;meta-bytes<=1048576;",
            law_source,
        )
        self.assertIn("decl-ref-resolution=", law_source)
        self.assertIn("module-closure-measure=", law_source)
        self.assertIn("semantic-language-profile-body=", law_source)
        self.assertIn(
            "no-kind-is-prior-meta-or-any-foundation-standalone-semantic-kind",
            law_source,
        )
        self.assertIn("identity-body-mode-law=", law_source)
        self.assertIn("canonical-value-id-body(P,T,d):=", law_source)
        self.assertIn("external-operation-contract-id=", law_source)
        self.assertIn("effective-semantic-context=", law_source)
        self.assertIn("portable-source-authority-binding-body=", law_source)
        self.assertIn("primitive-ref-pair-law=", law_source)
        self.assertIn("evaluation-request-snapshot=", law_source)
        self.assertTrue(
            law_source.endswith(
                "no-provider-conformance;"
                "no-unconditional-hash-binding-or-collision-resistance;"
                "no-protocol-relation-analysis-compiler-or-endpoint-admission\n"
            )
        )
        self.assertEqual(root_fields[3]["items"], [])
        self.assertEqual(
            root_fields[5],
            {
                "tag": "symbol",
                "value": (
                    "language-profiles-and-extension-modules-"
                    "same-root-dag-v0"
                ),
            },
        )

        frozen = oracle.process_request(root)
        self.assertEqual(frozen["outcome"], "Completed", frozen)
        descriptor_octets = bytes.fromhex(frozen["canonical_hex"])
        self.assertEqual(len(descriptor_octets), 46_870)
        self.assertEqual(
            hashlib.sha256(descriptor_octets).hexdigest(),
            "f9a91f67c10a1efd92e40f6f7fb31cdb1ab37524a8ed961ac4b66124d1eeba06",
        )
        self.assertEqual(frozen["content_id"], FROZEN_REGIME)

    def test_exact_prior_meta_and_semantic_preimages(self) -> None:
        meta = oracle.process_request(
            prior_meta_request("meta", REGIME_KIND, {"tag": "unit"})
        )
        self.assertEqual(meta["outcome"], "Completed", meta)
        meta_body = bytes.fromhex(meta["canonical_hex"])
        expected_meta_preimage = (
            b"zkc/prior-meta-id/v0\x00"
            + frame(FOUNDATION.encode("ascii"))
            + frame(REGIME_KIND.encode("ascii"))
            + frame(meta_body)
        )
        self.assertEqual(meta["preimage_hex"], expected_meta_preimage.hex())
        self.assertEqual(
            meta["content_id"]["digest"],
            hashlib.sha256(expected_meta_preimage).hexdigest(),
        )

        result = oracle.process_request(id_request("identity", "pir.core", self.VALUE))
        self.assertEqual(result["outcome"], "Completed", result)
        body = bytes.fromhex(result["canonical_hex"])
        expected_preimage = (
            b"zkc/content-id/v0\x00"
            + frame(FOUNDATION.encode("ascii"))
            + frame(prior_reference(IDENTITY_PROFILE))
            + frame(prior_reference(HASH_SUITE))
            + frame(b"pir.core")
            + frame(prior_reference(FROZEN_REGIME))
            + frame(body)
        )
        self.assertEqual(result["preimage_hex"], expected_preimage.hex())
        self.assertEqual(
            result["content_id"]["digest"],
            hashlib.sha256(expected_preimage).hexdigest(),
        )

    def test_constructors_are_disjoint_and_prior_kinds_are_closed(self) -> None:
        self.assertEqual(
            oracle.PRIOR_META_KINDS,
            frozenset({IDENTITY_KIND, HASH_KIND, REGIME_KIND}),
        )

        ordinary_as_meta = oracle.process_request(
            prior_meta_request("ordinary-as-meta", "pir.core", {"tag": "unit"})
        )
        self.assertEqual(ordinary_as_meta["outcome"], "Malformed")
        self.assertEqual(ordinary_as_meta["code"], "WrongIdConstructor")

        meta_as_semantic = oracle.process_request(
            id_request("meta-as-semantic", REGIME_KIND, {"tag": "unit"})
        )
        self.assertEqual(meta_as_semantic["outcome"], "Malformed")
        self.assertEqual(meta_as_semantic["code"], "WrongIdConstructor")

        module = oracle.process_request(
            id_request(
                "module",
                oracle.SEMANTIC_MODULE_KIND,
                {"tag": "unit"},
            )
        )
        self.assertEqual(module["outcome"], "Completed", module)
        self.assertEqual(module["content_id"]["id_type"], "semantic-content")

    def test_kind_and_regime_are_semantic_identity_axes(self) -> None:
        core = oracle.process_request(id_request("core", "pir.core", self.VALUE))
        protocol = oracle.process_request(
            id_request("protocol", "pir.protocol", self.VALUE)
        )
        self.assertNotEqual(
            core["content_id"]["digest"], protocol["content_id"]["digest"]
        )

        alternate_regime = oracle.process_request(
            prior_meta_request(
                "alternate-regime",
                REGIME_KIND,
                {"tag": "bool", "value": True},
            )
        )["content_id"]
        changed = id_request("changed-regime", "pir.core", self.VALUE)
        changed["semantic_regime"] = alternate_regime
        qualified = oracle.process_request(changed)
        self.assertEqual(qualified["outcome"], "Completed", qualified)
        self.assertNotEqual(
            core["content_id"]["digest"], qualified["content_id"]["digest"]
        )

    def test_verify_accepts_exact_id_and_rejects_digest_mutation(self) -> None:
        built = oracle.process_request(id_request("built", "pir.core", self.VALUE))
        verify = self.verify_request(
            "verify", "pir.core", self.VALUE, built["content_id"]
        )
        accepted = oracle.process_request(verify)
        self.assertEqual(accepted["outcome"], "Completed", accepted)

        mutated = dict(verify)
        mutated_id = dict(built["content_id"])
        mutated_id["digest"] = "00" * 32
        mutated["content_id"] = mutated_id
        rejected = oracle.process_request(mutated)
        self.assertEqual(rejected["outcome"], "Mismatch")
        self.assertEqual(rejected["code"], "DigestMismatch")

    def test_wrong_kind_precedes_malformed_body(self) -> None:
        built = oracle.process_request(
            id_request("protocol", "pir.protocol", {"tag": "unit"})
        )
        verify = self.verify_request(
            "wrong-kind",
            "pir.core",
            {"missing": "tag"},
            built["content_id"],
        )
        result = oracle.process_request(verify)
        self.assertEqual(result["outcome"], "Mismatch", result)
        self.assertEqual(result["code"], "WrongKind")

    def test_unsupported_profile_and_noncanonical_digest_refuse(self) -> None:
        unsupported = id_request("unsupported", "pir.core", self.VALUE)
        future_profile = dict(IDENTITY_PROFILE)
        future_profile["digest"] = "00" * 32
        unsupported["identity_profile"] = future_profile
        result = oracle.process_request(unsupported)
        self.assertEqual(result["outcome"], "Unsupported", result)

        built = oracle.process_request(id_request("built", "pir.core", self.VALUE))
        claimed = dict(built["content_id"])
        claimed["digest"] = "AA" * 32
        verify = self.verify_request("uppercase", "pir.core", self.VALUE, claimed)
        result = oracle.process_request(verify)
        self.assertEqual(result["outcome"], "Malformed")
        self.assertEqual(result["code"], "NonCanonical")

        # Full typed-ID and construction-axis shape precedes evaluator support.
        # The unsupported identity profile must not mask a null regime in
        # either a construction request or its claimed ID.
        malformed_construction = dict(unsupported)
        malformed_construction["semantic_regime"] = None
        result = oracle.process_request(malformed_construction)
        self.assertEqual(result["outcome"], "Malformed")
        self.assertEqual(result["code"], "WrongShape")

        malformed_claim = dict(built["content_id"])
        malformed_claim["identity_profile"] = future_profile
        malformed_claim["semantic_regime"] = None
        verify = self.verify_request(
            "unsupported-does-not-mask-shape",
            "pir.core",
            self.VALUE,
            malformed_claim,
        )
        result = oracle.process_request(verify)
        self.assertEqual(result["outcome"], "Malformed")
        self.assertEqual(result["code"], "WrongShape")

    def test_wrong_explicit_axes_refuse_before_digest_or_body(self) -> None:
        built = oracle.process_request(id_request("built", "pir.core", self.VALUE))
        alternate_regime = oracle.process_request(
            prior_meta_request(
                "alternate-regime",
                REGIME_KIND,
                {"tag": "bool", "value": True},
            )
        )["content_id"]
        forged = dict(built["content_id"])
        forged["semantic_regime"] = alternate_regime
        verify = self.verify_request(
            "wrong-regime", "pir.core", {"missing": "tag"}, forged
        )
        refused = oracle.process_request(verify)
        self.assertEqual(refused["outcome"], "Mismatch", refused)
        self.assertEqual(refused["code"], "SemanticRegimeMismatch")

    def test_axis_reference_kinds_are_not_interchangeable(self) -> None:
        request = id_request("wrong-axis-kind", "pir.core", self.VALUE)
        request["semantic_regime"] = HASH_SUITE
        result = oracle.process_request(request)
        self.assertEqual(result["outcome"], "Malformed", result)
        self.assertEqual(result["code"], "WrongReferenceKind")

        coincident_digest = dict(FROZEN_REGIME)
        coincident_digest["subject_kind"] = HASH_KIND
        request["semantic_regime"] = coincident_digest
        result = oracle.process_request(request)
        self.assertEqual(result["outcome"], "Malformed", result)
        self.assertEqual(result["code"], "WrongReferenceKind")

    def test_prior_meta_verify_is_separate(self) -> None:
        built = oracle.process_request(
            prior_meta_request("built-root", REGIME_KIND, {"tag": "unit"})
        )
        verify = base("verify-root", "verify_prior_meta_id")
        verify.update(
            {
                "expected_subject_kind": REGIME_KIND,
                "value": {"tag": "unit"},
                "content_id": built["content_id"],
            }
        )
        accepted = oracle.process_request(verify)
        self.assertEqual(accepted["outcome"], "Completed", accepted)

        semantic_claim = oracle.process_request(
            id_request("semantic", "pir.core", {"tag": "unit"})
        )["content_id"]
        verify["content_id"] = semantic_claim
        refused = oracle.process_request(verify)
        self.assertEqual(refused["outcome"], "Malformed", refused)
        self.assertEqual(refused["code"], "UnknownField")


class ResourceAndTransportTests(unittest.TestCase):
    def test_edge_counter_checks_every_cumulative_addition(self) -> None:
        limits = oracle.Limits(max_work=5)
        counters = oracle.Counters()

        counters.add_edges(3, limits)
        counters.add_edges(2, limits)
        self.assertEqual(counters.edges, 5)

        with self.assertRaises(oracle.OracleError) as raised:
            counters.add_edges(1, limits)
        self.assertEqual(raised.exception.outcome, "ResourceExceeded")
        self.assertEqual(raised.exception.detail, "work 6 exceeds limit 5")
        self.assertEqual(counters.edges, 5)

    def test_decode_preflights_declared_children_before_scanning_arrays(self) -> None:
        for tag, label in ((b"\x07", "sequence"), (b"\x08", "record")):
            with self.subTest(kind=label, limit="nodes"):
                request = base(f"{label}-node-preflight", "decode")
                request.update(
                    {
                        "canonical_hex": (tag + (5).to_bytes(8, "big")).hex(),
                        "limits": {"max_nodes": 5},
                    }
                )
                result = oracle.process_request(request)
                self.assertEqual(result["outcome"], "ResourceExceeded", result)
                self.assertEqual(result["detail"], "nodes 6 exceeds limit 5")

            with self.subTest(kind=label, limit="work"):
                request = base(f"{label}-edge-preflight", "decode")
                request.update(
                    {
                        "canonical_hex": (tag + (5).to_bytes(8, "big")).hex(),
                        "limits": {"max_work": 4},
                    }
                )
                result = oracle.process_request(request)
                self.assertEqual(result["outcome"], "ResourceExceeded", result)
                self.assertEqual(result["detail"], "work 5 exceeds limit 4")

    def test_decode_node_preflight_has_exact_and_one_less_controls(self) -> None:
        unit = b"\x00"
        inner = b"\x07" + (2).to_bytes(8, "big") + frame(unit) + frame(unit)
        outer = b"\x07" + (1).to_bytes(8, "big") + frame(inner)

        exact = base("node-preflight-exact", "decode")
        exact.update(
            {
                "canonical_hex": outer.hex(),
                "limits": {"max_nodes": 4},
            }
        )
        accepted = oracle.process_request(exact)
        self.assertEqual(accepted["outcome"], "Completed", accepted)
        self.assertEqual(accepted["usage"]["nodes"], 4)

        one_less = base("node-preflight-one-less", "decode")
        one_less.update(
            {
                "canonical_hex": outer.hex(),
                "limits": {"max_nodes": 3},
            }
        )
        refused = oracle.process_request(one_less)
        self.assertEqual(refused["outcome"], "ResourceExceeded", refused)
        self.assertEqual(refused["detail"], "nodes 4 exceeds limit 3")

    def test_cumulative_wide_value_exhausts_before_emission(self) -> None:
        request = base("wide", "encode")
        request.update(
            {
                "value": {
                    "tag": "seq",
                    "items": [
                        {"tag": "bytes", "value": "00"},
                        {"tag": "bytes", "value": "01"},
                    ],
                },
                "limits": {"max_input_bytes": 20},
            }
        )
        result = oracle.process_request(request)
        self.assertEqual(result["outcome"], "ResourceExceeded")
        self.assertIn("input_bytes", result["detail"])

    def test_node_depth_output_and_work_limits_are_separate(self) -> None:
        cases = []

        nodes = base("nodes", "encode")
        nodes.update(
            {
                "value": {
                    "tag": "seq",
                    "items": [{"tag": "unit"}, {"tag": "unit"}],
                },
                "limits": {"max_nodes": 2},
            }
        )
        cases.append(nodes)

        depth = base("depth", "encode")
        depth.update(
            {
                "value": {
                    "tag": "seq",
                    "items": [{"tag": "seq", "items": [{"tag": "unit"}]}],
                },
                "limits": {"max_depth": 2},
            }
        )
        cases.append(depth)

        output = base("output", "encode")
        output.update(
            {
                "value": {"tag": "bytes", "value": "00"},
                "limits": {"max_output_bytes": 9},
            }
        )
        cases.append(output)

        work = base("work", "encode")
        work.update(
            {
                "value": {"tag": "nat", "value": "100"},
                "limits": {"max_work": 4},
            }
        )
        cases.append(work)

        for request in cases:
            with self.subTest(case=request["case"]):
                result = oracle.process_request(request)
                self.assertEqual(result["outcome"], "ResourceExceeded", result)

    def test_identity_preimage_is_charged_cumulatively(self) -> None:
        request = id_request("identity-input", "pir.core", {"tag": "unit"})
        request["limits"] = {"max_input_bytes": 64}
        result = oracle.process_request(request)
        self.assertEqual(result["outcome"], "ResourceExceeded")
        self.assertIn("input_bytes", result["detail"])

    def test_duplicate_json_keys_are_rejected_before_request_processing(self) -> None:
        line = (
            b'{"case":"first","case":"second","op":"encode",'
            b'"foundation_profile":"zkc.foundation.meta.v0",'
            b'"value":{"tag":"unit"}}'
        )
        result = oracle._line_result(line, 7)
        self.assertEqual(result["case"], "line-7")
        self.assertEqual(result["outcome"], "Malformed")
        self.assertEqual(result["code"], "InvalidJson")

    def test_request_shape_precedes_profile_support(self) -> None:
        request = base("precedence", "encode")
        request.update(
            {
                "foundation_profile": "future.profile",
                "value": {"tag": "unit"},
                "unexpected": True,
            }
        )
        result = oracle.process_request(request)
        self.assertEqual(result["outcome"], "Malformed")
        self.assertEqual(result["code"], "UnknownField")

        unknown_operation = {
            "case": "unknown-operation-precedence",
            "op": "future-operation",
            "foundation_profile": "future.profile",
            "unexpected": True,
        }
        result = oracle.process_request(unknown_operation)
        self.assertEqual(result["outcome"], "Unsupported")
        self.assertEqual(result["code"], "UnsupportedOperation")

    def test_jsonl_fixture_and_cli_outputs_match_frozen_results(self) -> None:
        request_path = ORACLE_DIR / "cases" / "requests.jsonl"
        expected_path = ORACLE_DIR / "cases" / "expected.jsonl"
        with request_path.open("rb") as stream:
            direct = list(oracle.run_json_lines(stream))
        expected = [json.loads(line) for line in expected_path.read_text().splitlines()]

        def frozen_projection(
            actual: list[dict[str, object]],
        ) -> list[dict[str, object]]:
            self.assertEqual(len(actual), len(expected))
            return [
                {key: item[key] for key in frozen}
                for item, frozen in zip(actual, expected, strict=True)
            ]

        self.assertEqual(frozen_projection(direct), expected)

        completed = subprocess.run(
            [sys.executable, str(ORACLE_DIR / "oracle.py"), str(request_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        cli = [json.loads(line) for line in completed.stdout.splitlines()]
        self.assertEqual(frozen_projection(cli), expected)

        boundary = json.loads(
            (ORACLE_DIR / "cases" / "natural-byte-bound.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(len(boundary["vectors"]), 2)
        for vector in boundary["vectors"]:
            magnitude_octets = vector["magnitude_octets"]
            natural = 1 << (8 * (magnitude_octets - 1))
            encoded_octets = 1 + 8 + len(oracle._minimal_magnitude(natural))
            observed = {
                "outcome": "Completed" if encoded_octets <= 1 << 20 else "Malformed",
                "encoded_octets": encoded_octets,
            }
            if observed["outcome"] == "Malformed":
                observed["code"] = "CanonicalByteBound"
            with self.subTest(case=vector["case"]):
                self.assertEqual(observed, vector["expected"])

    def test_jsonl_runner_has_no_blank_line_escape(self) -> None:
        results = list(oracle.run_json_lines(io.BytesIO(b"\n")))
        self.assertEqual(results[0]["outcome"], "Malformed")
        self.assertEqual(results[0]["code"], "InvalidJson")


if __name__ == "__main__":
    unittest.main()
