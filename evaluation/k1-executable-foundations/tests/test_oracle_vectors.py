from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import reference_model as model  # noqa: E402


def _datum(raw: object) -> model.Datum:
    if not isinstance(raw, dict):
        raise TypeError("fixture datum must be an object")
    tag = raw.get("tag")
    if tag == "unit":
        return model.UNIT
    if tag == "bool":
        return bool(raw["value"])
    if tag == "nat":
        return model.Nat(int(raw["value"]))
    if tag == "int":
        return model.IntValue(int(raw["value"]))
    if tag == "bytes":
        return model.BytesValue(bytes.fromhex(str(raw["value"])))
    if tag == "symbol":
        return model.Symbol(str(raw["value"]))
    if tag == "seq":
        return model.DatumSeq(tuple(_datum(item) for item in raw["items"]))
    if tag == "record":
        return model.DatumRecord(
            tuple(
                (int(field["ordinal"]), _datum(field["value"]))
                for field in raw["fields"]
            )
        )
    if tag == "variant":
        return model.DatumVariant(int(raw["case"]), _datum(raw["value"]))
    raise ValueError("missing or unknown fixture tag")


def _prior_meta_id(raw: object) -> model.PriorMetaId:
    if not isinstance(raw, dict) or raw.get("id_type") != "prior-meta":
        raise TypeError("fixture prior-meta ID has the wrong shape")
    return model.PriorMetaId(
        str(raw["foundation_profile"]),
        str(raw["subject_kind"]),
        bytes.fromhex(str(raw["digest"])),
    )


def _semantic_id(raw: object) -> model.TypedContentId:
    if not isinstance(raw, dict) or raw.get("id_type") != "semantic-content":
        raise TypeError("fixture semantic ID has the wrong shape")
    return model.TypedContentId(
        str(raw["foundation_profile"]),
        _prior_meta_id(raw["identity_profile"]),
        _prior_meta_id(raw["hash_suite"]),
        str(raw["subject_kind"]),
        _prior_meta_id(raw["semantic_regime"]),
        bytes.fromhex(str(raw["digest"])),
    )


def _prior_object(identifier: model.PriorMetaId) -> dict[str, str]:
    return {
        "id_type": "prior-meta",
        "foundation_profile": identifier.foundation_profile,
        "subject_kind": identifier.subject_kind,
        "digest": identifier.digest.hex(),
    }


def _semantic_object(identifier: model.TypedContentId) -> dict[str, object]:
    return {
        "id_type": "semantic-content",
        "foundation_profile": identifier.foundation_profile,
        "identity_profile": _prior_object(identifier.identity_profile),
        "hash_suite": _prior_object(identifier.hash_suite),
        "subject_kind": identifier.subject_kind,
        "semantic_regime": _prior_object(identifier.semantic_regime),
        "digest": identifier.digest.hex(),
    }


class IndependentOracleVectorParityTest(unittest.TestCase):
    def test_durable_law_source_is_exact_reference_source(self) -> None:
        document = (
            PACKAGE_ROOT.parents[1]
            / "docs-next"
            / "foundation"
            / "executable-foundations.md"
        ).read_bytes()
        marker = (
            b"`SemanticCoreLawSourceV0` is the ASCII encoding of the following "
            b"lines joined\nby LF, including one LF after the last line and no CR "
            b"octets:\n\n"
            b"<!-- zkc-foundation-source:semantic-core-law:start -->\n\n"
            b"```text\n"
        )
        start = document.index(marker) + len(marker)
        end = document.index(
            b"```\n\n"
            b"<!-- zkc-foundation-source:semantic-core-law:end -->\n\n"
            b"The byte string has length",
            start,
        )

        self.assertEqual(document[start:end], model.SEMANTIC_CORE_LAW_SOURCE)

    def test_all_frozen_oracle_records(self) -> None:
        cases = PACKAGE_ROOT / "oracle" / "cases"
        requests = [
            json.loads(line)
            for line in (cases / "requests.jsonl")
            .read_text(encoding="utf-8")
            .splitlines()
        ]
        expected = {
            item["case"]: item
            for item in (
                json.loads(line)
                for line in (cases / "expected.jsonl")
                .read_text(encoding="utf-8")
                .splitlines()
            )
        }
        self.assertEqual(len(requests), 24)

        for request in requests:
            name = request["case"]
            result = expected[name]
            with self.subTest(case=name):
                if name.startswith("encode-"):
                    body = model.encode_datum(_datum(request["value"]))
                    self.assertEqual(body.hex(), result["canonical_hex"])
                elif name == "decode-nat-zero":
                    decoded = model.decode_datum(
                        bytes.fromhex(request["canonical_hex"])
                    )
                    self.assertEqual(
                        model.encode_datum(decoded).hex(), result["canonical_hex"]
                    )
                elif name in (
                    "id-identity-profile",
                    "id-hash-suite",
                    "id-regime-root",
                ):
                    body = _datum(request["value"])
                    if name == "id-regime-root":
                        self.assertEqual(body, model.SEMANTIC_REGIME_DESCRIPTOR)
                    identifier = model.meta_object_id(
                        request["subject_kind"],
                        model.encode_datum(body),
                        foundation_profile=request["foundation_profile"],
                    )
                    self.assertEqual(_prior_object(identifier), result["content_id"])
                elif name in (
                    "id-core",
                    "id-semantic-module",
                    "id-semantic-language-profile",
                    "id-profiled-subject",
                ):
                    body = _datum(request["value"])
                    identifier = model.content_id(
                        request["subject_kind"],
                        model.encode_datum(body),
                        semantic_regime=_prior_meta_id(request["semantic_regime"]),
                        foundation_profile=request["foundation_profile"],
                        identity_profile=_prior_meta_id(request["identity_profile"]),
                        hash_suite=_prior_meta_id(request["hash_suite"]),
                    )
                    self.assertEqual(_semantic_object(identifier), result["content_id"])
                    if name == "id-semantic-module":
                        self.assertIsInstance(body, model.DatumRecord)
                        module_fields = dict(body.fields)
                        self.assertEqual(tuple(module_fields), (0, 1, 2))
                        self.assertEqual(module_fields[0], model.DatumSeq(()))
                        candidate = model.SemanticModuleCandidate(
                            model.Symbol("oracle.identity-contrast"),
                            (),
                            module_fields[1],
                            module_fields[2],
                        )
                        self.assertEqual(candidate.body(), model.encode_datum(body))
                        self.assertEqual(candidate.identity, identifier)
                    elif name == "id-semantic-language-profile":
                        self.assertIsInstance(body, model.DatumRecord)
                        profile_fields = dict(body.fields)
                        self.assertEqual(tuple(profile_fields), tuple(range(6)))
                        profile = model.SemanticLanguageProfile(
                            profile_fields[0],
                            profile_fields[1].value,
                            (),
                            tuple(profile_fields[3].values),
                            profile_fields[4],
                            profile_fields[5].value,
                        )
                        self.assertEqual(profile.body(), body)
                        self.assertEqual(profile.identity, identifier)
                    elif name == "id-profiled-subject":
                        self.assertIsInstance(body, model.DatumRecord)
                        profiled_fields = dict(body.fields)
                        self.assertEqual(tuple(profiled_fields), (0, 1))
                        self.assertIsInstance(profiled_fields[0], model.BytesValue)
                elif name == "wrong-kind":
                    # Kind precedence is checked without attempting to parse the
                    # deliberately malformed body.
                    supplied = _semantic_id(request["content_id"])
                    self.assertNotEqual(
                        supplied.subject_kind, request["expected_subject_kind"]
                    )
                    self.assertEqual(result["code"], "WrongKind")
                elif name in ("ordinary-as-prior-meta", "module-as-prior-meta"):
                    with self.assertRaises(model.CanonicalError):
                        model.meta_object_id(
                            request["subject_kind"],
                            model.encode_datum(_datum(request["value"])),
                        )
                    self.assertEqual(result["code"], "WrongIdConstructor")
                elif name == "prior-meta-as-semantic":
                    with self.assertRaises(model.CanonicalError):
                        model.content_id(
                            request["subject_kind"],
                            model.encode_datum(_datum(request["value"])),
                            semantic_regime=_prior_meta_id(request["semantic_regime"]),
                            identity_profile=_prior_meta_id(
                                request["identity_profile"]
                            ),
                            hash_suite=_prior_meta_id(request["hash_suite"]),
                        )
                    self.assertEqual(result["code"], "WrongIdConstructor")
                elif name == "null-regime":
                    with self.assertRaises(model.CanonicalError):
                        model.content_id(
                            request["subject_kind"],
                            model.encode_datum(_datum(request["value"])),
                            semantic_regime=None,
                            identity_profile=_prior_meta_id(
                                request["identity_profile"]
                            ),
                            hash_suite=_prior_meta_id(request["hash_suite"]),
                        )
                    self.assertEqual(result["outcome"], "Malformed")
                elif name == "wrong-axis-kind":
                    with self.assertRaises(model.CanonicalError):
                        model.content_id(
                            request["subject_kind"],
                            model.encode_datum(_datum(request["value"])),
                            semantic_regime=_prior_meta_id(request["semantic_regime"]),
                            identity_profile=_prior_meta_id(
                                request["identity_profile"]
                            ),
                            hash_suite=_prior_meta_id(request["hash_suite"]),
                        )
                    self.assertEqual(result["code"], "WrongReferenceKind")
                elif name in (
                    "noncanonical-leading-zero",
                    "unknown-binary-tag",
                ):
                    with self.assertRaises(model.CanonicalError):
                        model.decode_datum(bytes.fromhex(request["canonical_hex"]))
                    self.assertEqual(result["outcome"], "Malformed")
                elif name == "unsupported-profile":
                    with self.assertRaisesRegex(
                        model.CanonicalError, "identity profile"
                    ):
                        model.content_id(
                            request["subject_kind"],
                            model.encode_datum(_datum(request["value"])),
                            semantic_regime=_prior_meta_id(request["semantic_regime"]),
                            identity_profile=_prior_meta_id(
                                request["identity_profile"]
                            ),
                            hash_suite=_prior_meta_id(request["hash_suite"]),
                        )
                elif name == "resource-wide":
                    body = model.encode_datum(_datum(request["value"]))
                    self.assertGreater(len(body), request["limits"]["max_input_bytes"])
                    self.assertEqual(result["outcome"], "ResourceExceeded")
                elif name == "digest-mismatch":
                    supplied = _semantic_id(request["content_id"])
                    recomputed = model.content_id(
                        request["expected_subject_kind"],
                        model.encode_datum(_datum(request["value"])),
                        semantic_regime=_prior_meta_id(request["semantic_regime"]),
                        identity_profile=_prior_meta_id(request["identity_profile"]),
                        hash_suite=_prior_meta_id(request["hash_suite"]),
                    )
                    self.assertNotEqual(supplied.digest, recomputed.digest)
                elif name == "wrong-regime":
                    supplied = _semantic_id(request["content_id"])
                    expected_regime = _prior_meta_id(request["semantic_regime"])
                    self.assertNotEqual(supplied.semantic_regime, expected_regime)
                    self.assertEqual(result["code"], "SemanticRegimeMismatch")
                else:  # pragma: no cover - fixture growth must be classified
                    self.fail(f"unclassified oracle vector {name!r}")


if __name__ == "__main__":
    unittest.main()
