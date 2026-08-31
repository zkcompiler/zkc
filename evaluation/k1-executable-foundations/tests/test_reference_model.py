from __future__ import annotations

import copy
from dataclasses import replace
import hashlib
from pathlib import Path
import pickle
import sys
from types import MappingProxyType
import unittest
from unittest.mock import patch


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import reference_model as model  # noqa: E402


def value(value_type: model.ValueType, datum: model.Datum) -> model.CanonicalValue:
    return model.admit_value(value_type, datum)


def success(result: model.EvaluationResult) -> model.CanonicalValue:
    if result.outcome is not model.Outcome.COMPLETED:
        raise AssertionError(result)
    if not isinstance(result.completion, model.Success):
        raise AssertionError(result)
    return result.completion.value


def module(
    name: str,
    imports: tuple[model.TypedContentId, ...] = (),
    *,
    payload: model.Datum = model.UNIT,
) -> model.SemanticModuleCandidate:
    ordered = tuple(sorted(imports, key=lambda item: item.internal_reference()))
    local_declarations = model.DatumSeq(
        (
            model.DatumRecord(
                (
                    (0, model.Symbol("fixture-declaration")),
                    (
                        1,
                        model.DatumSeq(
                            (model.DatumRecord(((0, model.Symbol(name)),)),)
                        ),
                    ),
                )
            ),
            model.DatumRecord(
                (
                    (0, model.Symbol("value-domain")),
                    (
                        1,
                        model.DatumSeq(
                            tuple(
                                model.DatumRecord(((0, model.Symbol(name)),))
                                for _ in range(8)
                            )
                        ),
                    ),
                )
            ),
        )
    )
    return model.SemanticModuleCandidate(
        model.Symbol(name),
        ordered,
        local_declarations,
        payload,
    )


def language_profile(
    family: str,
    supported_subject_kinds: tuple[str, ...],
    law_source: bytes,
    profile_imports: tuple[model.TypedContentId, ...] = (),
    declaration_catalogs: model.DatumSeq | None = None,
) -> model.SemanticLanguageProfile:
    if declaration_catalogs is None:
        declaration_catalogs = model.DatumSeq(
            (
                model.DatumRecord(
                    (
                        (0, model.Symbol("fixture-profile-declaration")),
                        (
                            1,
                            model.DatumSeq(
                                (
                                    model.DatumRecord(
                                        ((0, model.Symbol(family)),)
                                    ),
                                )
                            ),
                        ),
                    )
                ),
            )
        )
    return model.SemanticLanguageProfile(
        model.Symbol(family),
        0,
        tuple(
            sorted(
                profile_imports,
                key=lambda item: item.internal_reference(),
            )
        ),
        tuple(model.Symbol(kind) for kind in sorted(supported_subject_kinds)),
        declaration_catalogs,
        law_source,
    )


def primitive(name: str, *arguments: model.Term) -> model.PrimitiveCall:
    return model.PrimitiveCall(model.PRIMITIVE_REFS_BY_KEY[(name, 1)], tuple(arguments))


def primitive_reference(
    declaration_module: model.TypedContentId, local_ordinal: int
) -> model.SemanticPrimitiveRef:
    declaration_body = model.DatumVariant(
        1,
        model.DatumRecord(
            (
                (0, model.BytesValue(declaration_module.internal_reference())),
                (1, model.Symbol("semantic-primitive")),
                (2, model.Nat(local_ordinal)),
            )
        ),
    )
    identifier = model.content_id(
        "foundation.semantic-primitive",
        model.encode_datum(declaration_body),
        semantic_regime=declaration_module.semantic_regime,
    )
    return model.SemanticPrimitiveRef(identifier, declaration_module, local_ordinal)


def malformed_content_id(
    template: model.TypedContentId,
) -> model.TypedContentId:
    identifier = object.__new__(model.TypedContentId)
    for field in (
        "foundation_profile",
        "identity_profile",
        "hash_suite",
        "subject_kind",
        "semantic_regime",
    ):
        object.__setattr__(identifier, field, getattr(template, field))
    object.__setattr__(identifier, "digest", b"short")
    return identifier


def malformed_prior_meta_id(
    template: model.PriorMetaId,
) -> model.PriorMetaId:
    identifier = object.__new__(model.PriorMetaId)
    object.__setattr__(
        identifier,
        "foundation_profile",
        template.foundation_profile,
    )
    object.__setattr__(identifier, "subject_kind", template.subject_kind)
    object.__setattr__(identifier, "digest", b"short")
    return identifier


class FoundationMetaProfileTest(unittest.TestCase):
    def test_frozen_tag_table_and_nested_roundtrip(self) -> None:
        cases = (
            (model.UNIT, "00"),
            (False, "01"),
            (True, "02"),
            (model.Nat(0), "03000000000000000100"),
            (model.Nat(256), "0300000000000000020100"),
            (model.IntValue(-7), "0401000000000000000107"),
            (model.BytesValue(b"zk"), "0500000000000000027a6b"),
            (model.Symbol("A"), "06000000000000000141"),
        )
        for datum, expected in cases:
            with self.subTest(datum=datum):
                body = model.encode_datum(datum)
                self.assertEqual(body.hex(), expected)
                self.assertEqual(model.decode_datum(body), datum)

        nested = model.DatumRecord(
            (
                (0, model.Symbol("pir.core")),
                (
                    3,
                    model.DatumSeq(
                        (
                            model.Nat(9),
                            model.DatumVariant(2, model.BytesValue(b"\x00\xff")),
                        )
                    ),
                ),
            )
        )
        self.assertEqual(model.decode_datum(model.encode_datum(nested)), nested)

    def test_noncanonical_spellings_are_rejected(self) -> None:
        def frame(body: bytes) -> bytes:
            return len(body).to_bytes(8, "big") + body

        unit = b"\x00"
        malformed = (
            b"\x03" + frame(b""),
            b"\x03" + frame(b"\x00\x01"),
            b"\x04\x01" + frame(b"\x00"),
            b"\x06" + frame(b"has space"),
            b"\x00\x00",
            (
                b"\x08"
                + (2).to_bytes(8, "big")
                + (1).to_bytes(8, "big")
                + frame(unit)
                + (1).to_bytes(8, "big")
                + frame(unit)
            ),
        )
        for body in malformed:
            with self.subTest(body=body.hex()):
                with self.assertRaises(model.CanonicalError):
                    model.decode_datum(body)

    def test_host_scalar_types_and_u64_aggregate_ordinals_are_exact(self) -> None:
        malformed_datums: tuple[object, ...] = (
            model.Nat(True),
            model.IntValue(False),
            model.BytesValue(bytearray(b"x")),
            model.Symbol(b"not-text"),
            model.DatumRecord(((True, model.UNIT),)),
            model.DatumRecord(((-1, model.UNIT),)),
            model.DatumRecord((((1 << 64), model.UNIT),)),
            model.DatumVariant(True, model.UNIT),
            model.DatumVariant(1 << 64, model.UNIT),
        )
        for datum in malformed_datums:
            with self.subTest(datum=datum):
                with self.assertRaises(model.CanonicalError):
                    model.encode_datum(datum)  # type: ignore[arg-type]

        malformed_schemas = (
            model.NatSchema(True),
            model.IntSchema(False, 1),
            model.BytesSchema(0, True),
            model.SymbolSchema(True),
            model.RecordSchema(((1 << 64, model.UNIT_VALUE),)),
            model.VariantSchema(((1 << 64, model.UNIT_VALUE),)),
        )
        for schema in malformed_schemas:
            with self.subTest(schema=schema):
                with self.assertRaises(model.CanonicalError):
                    model.validate_schema(schema)

        for digest in ("x" * 32, bytearray(32)):
            with self.subTest(digest=type(digest).__name__):
                with self.assertRaises(model.CanonicalError):
                    model.PriorMetaId(
                        model.FOUNDATION_PROFILE,
                        model.SEMANTIC_REGIME_KIND,
                        digest,  # type: ignore[arg-type]
                    )

        for ordinal in (-1, True, 1 << 64, "0"):
            with self.subTest(declaration_ordinal=ordinal):
                with self.assertRaises(model.CanonicalError):
                    model.ValueDomain(
                        model.SEMANTIC_REGIME_ID,
                        model.ROOT_VALUE_DOMAIN_KIND,
                        ordinal,  # type: ignore[arg-type]
                    )
                with self.assertRaises(model.CanonicalError):
                    model.SemanticPrimitiveRef(
                        model.PRIMITIVE_IDS_BY_KEY[("sha2-256", 1)],
                        model.FIXTURE_EXTENSION_MODULE_ID,
                        ordinal,  # type: ignore[arg-type]
                    )
                with self.assertRaises(model.ModelError):
                    model.SemanticFailureType(
                        model.FIXTURE_EXTENSION_MODULE_ID,
                        ordinal,  # type: ignore[arg-type]
                        model.UNIT_VALUE,
                    )

        original = model.PRIMITIVE_SEMANTIC_CATALOG[0]
        malformed_catalog = (
            (True, *original[1:]),
            *model.PRIMITIVE_SEMANTIC_CATALOG[1:],
        )
        with self.assertRaises(model.CanonicalError):
            model.primitive_catalog_datum(malformed_catalog)

    def test_meta_value_subclasses_and_scalar_subclasses_are_not_canonical(
        self,
    ) -> None:
        class UnitSubclass(model.Unit):
            pass

        class NatSubclass(model.Nat):
            pass

        class IntSubclass(model.IntValue):
            pass

        class BytesDatumSubclass(model.BytesValue):
            pass

        class SymbolSubclass(model.Symbol):
            pass

        class SeqSubclass(model.DatumSeq):
            pass

        class RecordSubclass(model.DatumRecord):
            pass

        class VariantSubclass(model.DatumVariant):
            pass

        class BytesSubclass(bytes):
            pass

        class StrSubclass(str):
            pass

        malformed_datums: tuple[object, ...] = (
            UnitSubclass(),
            NatSubclass(0),
            IntSubclass(0),
            BytesDatumSubclass(b"x"),
            SymbolSubclass("x"),
            SeqSubclass(()),
            RecordSubclass(()),
            VariantSubclass(0, model.UNIT),
            model.BytesValue(BytesSubclass(b"x")),
            model.Symbol(StrSubclass("x")),
        )
        for datum in malformed_datums:
            with self.subTest(datum=type(datum).__name__):
                with self.assertRaises(model.CanonicalError):
                    model.encode_datum(datum)  # type: ignore[arg-type]

        with self.assertRaises(model.CanonicalError):
            model.decode_datum(BytesSubclass(b"\x00"))

        malformed_literal = model.CanonicalAlgorithm(
            model.Symbol("HostSubclassLiteral"),
            (),
            model.Literal(model.CanonicalValue(model.UNIT_VALUE, UnitSubclass())),
        )
        result = model.Evaluator().evaluate(malformed_literal, ())
        self.assertEqual(result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(result.code, "K1-MALFORMED-MODEL")

    def test_wide_sequence_hits_cumulative_preflight(self) -> None:
        wide = model.DatumSeq(tuple(model.BytesValue(b"x" * 1024) for _ in range(1025)))
        with self.assertRaisesRegex(model.CanonicalError, "cumulative byte"):
            model.encode_datum(wide)

    def test_canonical_byte_and_node_boundaries_are_exact(self) -> None:
        exact_bytes = model.BytesValue(b"x" * (model.MAX_CANONICAL_BYTES - 9))
        exact_bytes_body = model.encode_datum(exact_bytes)
        self.assertEqual(len(exact_bytes_body), model.MAX_CANONICAL_BYTES)
        self.assertEqual(model.decode_datum(exact_bytes_body), exact_bytes)
        with self.assertRaisesRegex(model.CanonicalError, "byte bound"):
            model.encode_datum(model.BytesValue(b"x" * (model.MAX_CANONICAL_BYTES - 8)))

        exact_symbol = model.Symbol("x" * (model.MAX_CANONICAL_BYTES - 9))
        exact_symbol_body = model.encode_datum(exact_symbol)
        self.assertEqual(len(exact_symbol_body), model.MAX_CANONICAL_BYTES)
        self.assertEqual(model.decode_datum(exact_symbol_body), exact_symbol)
        with self.assertRaisesRegex(model.CanonicalError, "byte bound"):
            model.encode_datum(model.Symbol("x" * (model.MAX_CANONICAL_BYTES - 8)))

        exact_nodes = model.DatumSeq((model.UNIT,) * (model.MAX_CANONICAL_NODES - 1))
        exact_nodes_body = model.encode_datum(exact_nodes)
        self.assertEqual(model.decode_datum(exact_nodes_body), exact_nodes)

        over_count = model.MAX_CANONICAL_NODES
        over_nodes = model.DatumSeq((model.UNIT,) * over_count)
        over_nodes_body = (
            b"\x07"
            + over_count.to_bytes(8, "big")
            + (len(b"\x00").to_bytes(8, "big") + b"\x00") * over_count
        )
        with self.assertRaisesRegex(model.CanonicalError, "node bound"):
            model.encode_datum(over_nodes)
        with self.assertRaisesRegex(model.CanonicalError, "node bound"):
            model.decode_datum(over_nodes_body)

    def test_aggregate_child_edge_limit_is_enforced_by_encode_and_decode(self) -> None:
        exact_count = model.MAX_CANONICAL_EDGES
        exact = model.DatumSeq((model.UNIT,) * exact_count)
        exact_encoded = (
            b"\x07"
            + exact_count.to_bytes(8, "big")
            + (len(b"\x00").to_bytes(8, "big") + b"\x00") * exact_count
        )
        with patch.object(model, "MAX_CANONICAL_NODES", exact_count + 1):
            self.assertEqual(model.encode_datum(exact), exact_encoded)
            self.assertEqual(model.decode_datum(exact_encoded), exact)

        count = model.MAX_CANONICAL_EDGES + 1
        wide = model.DatumSeq((model.UNIT,) * count)
        encoded = (
            b"\x07"
            + count.to_bytes(8, "big")
            + (len(b"\x00").to_bytes(8, "big") + b"\x00") * count
        )
        with patch.object(model, "MAX_CANONICAL_NODES", count + 1):
            with self.assertRaisesRegex(model.CanonicalError, "child-edge"):
                model.encode_datum(wide)
            with self.assertRaisesRegex(model.CanonicalError, "child-edge"):
                model.decode_datum(encoded)

    def test_constitutional_depth_bound_is_executable_at_the_exact_edge(self) -> None:
        exact: model.Datum = model.UNIT
        for _ in range(model.MAX_CANONICAL_DEPTH):
            exact = model.DatumVariant(0, exact)
        encoded = model.encode_datum(exact)
        self.assertEqual(model.decode_datum(encoded), exact)
        with self.assertRaisesRegex(model.CanonicalError, "depth bound"):
            model.encode_datum(model.DatumVariant(0, exact))

        raw_over_depth = b"\x00"
        for _ in range(model.MAX_CANONICAL_DEPTH + 1):
            raw_over_depth = (
                b"\x09"
                + (0).to_bytes(8, "big")
                + len(raw_over_depth).to_bytes(8, "big")
                + raw_over_depth
            )
        with self.assertRaisesRegex(model.CanonicalError, "depth bound"):
            model.decode_datum(raw_over_depth)

    def test_semantic_schema_depth_is_stricter_than_meta_value_depth(self) -> None:
        nested = model.BYTES_8
        for _ in range(model.MAX_SCHEMA_DEPTH):
            nested = model.ValueType(
                model.SEQUENCE_DOMAIN,
                model.SeqSchema(nested, 1),
            )
        with self.assertRaisesRegex(model.CanonicalError, "schema exceeds depth"):
            model.ValueType(
                model.SEQUENCE_DOMAIN,
                model.SeqSchema(nested, 1),
            )

    def test_schema_admission_bounds_every_shaped_value(self) -> None:
        exact = model.ValueType(
            model.SEQUENCE_DOMAIN,
            model.SeqSchema(model.UNIT_VALUE, model.MAX_CANONICAL_NODES - 1),
        )
        self.assertLessEqual(
            model.maximum_encoded_size(exact.schema),
            model.MAX_CANONICAL_BYTES,
        )
        with self.assertRaisesRegex(model.CanonicalError, "canonical node bound"):
            model.ValueType(
                model.SEQUENCE_DOMAIN,
                model.SeqSchema(model.UNIT_VALUE, model.MAX_CANONICAL_NODES),
            )

        class ExplosiveCases(tuple):
            reads = 0

            def __len__(self) -> int:
                type(self).reads += 1
                raise AssertionError("tuple-subclass truthiness must not execute")

        with self.assertRaisesRegex(model.CanonicalError, "immutable tuple"):
            model.maximum_encoded_size(
                model.VariantSchema(ExplosiveCases(((0, model.UNIT_VALUE),)))
            )
        self.assertEqual(ExplosiveCases.reads, 0)

    def test_value_type_body_must_fit_the_constitutional_meta_profile(self) -> None:
        fields = tuple((ordinal, model.UNIT_VALUE) for ordinal in range(3000))
        schema = model.RecordSchema(fields)
        self.assertLessEqual(
            model.maximum_encoded_size(schema),
            model.MAX_CANONICAL_BYTES,
        )
        with self.assertRaisesRegex(model.CanonicalError, "canonical datum"):
            model.ValueType(model.RECORD_DOMAIN, schema)

    def test_prior_meta_and_semantic_id_constructors_are_disjoint(self) -> None:
        ordinary = model.content_id(
            "pir.core",
            model.encode_datum(model.Symbol("fixture")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assertIsInstance(model.SEMANTIC_REGIME_ID, model.PriorMetaId)
        self.assertIsInstance(ordinary, model.TypedContentId)
        self.assertNotEqual(type(model.SEMANTIC_REGIME_ID), type(ordinary))

        with self.assertRaises(model.CanonicalError):
            model.meta_object_id("pir.core", b"ordinary-content")
        with self.assertRaises(model.CanonicalError):
            model.content_id(
                model.IDENTITY_PROFILE_KIND,
                b"prior-kind-through-ordinary-constructor",
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        with self.assertRaises(model.CanonicalError):
            model.content_id(  # type: ignore[arg-type]
                "pir.core", b"null-regime", semantic_regime=None
            )
        with self.assertRaises(model.CanonicalError):
            model.content_id(
                "pir.core",
                b"wrong-regime-kind",
                semantic_regime=model.IDENTITY_PROFILE_ID,
            )
        with self.assertRaises(model.CanonicalError):
            model.content_id(
                "pir.core",
                b"wrong-identity-kind",
                semantic_regime=model.SEMANTIC_REGIME_ID,
                identity_profile=model.HASH_SUITE_ID,
            )
        coincident_wrong_kind = model.PriorMetaId(
            model.FOUNDATION_PROFILE,
            model.HASH_SUITE_KIND,
            model.SEMANTIC_REGIME_ID.digest,
        )
        with self.assertRaises(model.CanonicalError):
            model.content_id(
                "pir.core",
                model.encode_datum(model.UNIT),
                semantic_regime=coincident_wrong_kind,
            )

        class ExplosiveAxis(str):
            comparisons = 0
            __hash__ = str.__hash__

            def __eq__(self, _other: object) -> bool:
                ExplosiveAxis.comparisons += 1
                raise AssertionError("host comparison must not execute")

            def __ne__(self, _other: object) -> bool:
                ExplosiveAxis.comparisons += 1
                raise AssertionError("host comparison must not execute")

        valid_body = model.encode_datum(model.UNIT)
        with self.assertRaises(model.CanonicalError):
            model.meta_object_id(
                model.SEMANTIC_REGIME_KIND,
                valid_body,
                foundation_profile=ExplosiveAxis(model.FOUNDATION_PROFILE),
            )
        with self.assertRaises(model.CanonicalError):
            model.meta_object_id(ExplosiveAxis(model.SEMANTIC_REGIME_KIND), valid_body)
        with self.assertRaisesRegex(model.CanonicalError, "axis-length bound"):
            model.content_id(
                "x" * (model.MAX_CANONICAL_BYTES + 1),
                valid_body,
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        self.assertEqual(ExplosiveAxis.comparisons, 0)

    def test_content_id_binds_kind_body_and_regime(self) -> None:
        body = model.encode_datum(model.Symbol("fixture"))
        baseline = model.content_id(
            "pir.core", body, semantic_regime=model.SEMANTIC_REGIME_ID
        )
        same = model.content_id(
            "pir.core", body, semantic_regime=model.SEMANTIC_REGIME_ID
        )
        other_kind = model.content_id(
            "pir.protocol", body, semantic_regime=model.SEMANTIC_REGIME_ID
        )
        other_body = model.content_id(
            "pir.core",
            model.encode_datum(model.Symbol("fixture-2")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        other_regime = model.meta_object_id(
            model.SEMANTIC_REGIME_KIND,
            model.encode_datum(model.Symbol("other-regime")),
        )
        other_regime_subject = model.content_id(
            "pir.core", body, semantic_regime=other_regime
        )

        self.assertEqual(baseline, same)
        self.assertNotEqual(baseline, other_kind)
        self.assertNotEqual(baseline, other_body)
        self.assertNotEqual(baseline, other_regime_subject)

    def test_ordinary_id_authenticates_all_prior_axes_before_the_body(self) -> None:
        body = model.encode_datum(model.Symbol("authenticated-semantic-body"))
        identifier = model.content_id(
            "pir.core", body, semantic_regime=model.SEMANTIC_REGIME_ID
        )
        model.authenticate_content_id(
            identifier, body, model.FOUNDATION_PRIOR_META_PREIMAGES
        )

        mutation = model.encode_datum(model.Symbol("mutated-descriptor"))
        for field in (
            "identity_profile",
            "hash_suite",
            "semantic_regime",
        ):
            with self.subTest(axis=field):
                preimages = replace(
                    model.FOUNDATION_PRIOR_META_PREIMAGES,
                    **{field: mutation},
                )
                with self.assertRaisesRegex(
                    model.CanonicalError, "descriptor does not authenticate"
                ):
                    model.authenticate_content_id(identifier, body, preimages)

        with self.assertRaisesRegex(
            model.CanonicalError, "semantic body does not authenticate"
        ):
            model.authenticate_content_id(
                identifier,
                model.encode_datum(model.Symbol("different-semantic-body")),
                model.FOUNDATION_PRIOR_META_PREIMAGES,
            )

        # Exercise the ledger branch without claiming a real SHA-256
        # collision: retain strict descriptor validation, then substitute a
        # digest function that maps two canonical bodies to the same typed ID.
        ledger = model.AuthenticationLedger()
        real_meta_object_id = model.meta_object_id

        def synthetic_collision(kind: str, candidate: bytes) -> model.PriorMetaId:
            real_meta_object_id(kind, candidate)
            return model.IDENTITY_PROFILE_ID

        with patch.object(model, "meta_object_id", side_effect=synthetic_collision):
            model.authenticate_prior_meta_id(
                model.IDENTITY_PROFILE_ID,
                model.FOUNDATION_PRIOR_META_PREIMAGES.identity_profile,
                expected_kind=model.IDENTITY_PROFILE_KIND,
                ledger=ledger,
            )
            with self.assertRaises(model.HashBindingConflictError) as observed:
                model.authenticate_prior_meta_id(
                    model.IDENTITY_PROFILE_ID,
                    mutation,
                    expected_kind=model.IDENTITY_PROFILE_KIND,
                    ledger=ledger,
                )
        checker_failure = model.Evaluator._model_error_result(observed.exception)
        self.assertEqual(checker_failure.outcome, model.Outcome.CHECKER_FAILURE)
        self.assertEqual(checker_failure.code, "FOUNDATION-HASH-BINDING-CONFLICT")

        colliding_basis = replace(
            model.FOUNDATION_PRIOR_META_PREIMAGES,
            identity_profile=mutation,
        )

        def synthetic_identity_collision(
            kind: str, candidate: bytes
        ) -> model.PriorMetaId:
            validated = real_meta_object_id(kind, candidate)
            if kind == model.IDENTITY_PROFILE_KIND:
                return model.IDENTITY_PROFILE_ID
            return validated

        with patch.object(
            model,
            "meta_object_id",
            side_effect=synthetic_identity_collision,
        ):
            end_to_end = model.Evaluator().evaluate(
                object(),  # type: ignore[arg-type]
                (),
                prior_meta_preimages=colliding_basis,
            )
        self.assertEqual(end_to_end.outcome, model.Outcome.CHECKER_FAILURE)
        self.assertEqual(end_to_end.code, "FOUNDATION-HASH-BINDING-CONFLICT")

        capped = model.AuthenticationLedger()
        with patch.object(model, "MAX_AUTHENTICATION_LEDGER_ENTRIES", 0):
            with self.assertRaisesRegex(model.CanonicalError, "derived request bound"):
                model.authenticate_prior_meta_id(
                    model.IDENTITY_PROFILE_ID,
                    model.FOUNDATION_PRIOR_META_PREIMAGES.identity_profile,
                    expected_kind=model.IDENTITY_PROFILE_KIND,
                    ledger=capped,
                )
        self.assertEqual(capped.size, 0)

    def test_semantic_identity_bodies_must_be_strict_canonical_meta_values(
        self,
    ) -> None:
        noncanonical_zero = b"\x03" + (2).to_bytes(8, "big") + b"\x00\x00"
        with self.assertRaises(model.CanonicalError):
            model.content_id(
                "pir.core",
                noncanonical_zero,
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        with self.assertRaises(model.CanonicalError):
            model.meta_object_id(model.SEMANTIC_REGIME_KIND, noncanonical_zero)

    def test_domain_index_is_semantic_even_for_equal_bytes(self) -> None:
        owner = module("fixture.other-domain-owner")
        other_domain = model.ValueDomain(
            owner.identity,
            model.Symbol("value-domain"),
            0,
        )
        left_type = model.ValueType(model.BYTES_DOMAIN, model.BytesSchema(1, 1))
        right_type = model.ValueType(other_domain, model.BytesSchema(1, 1))
        left = value(left_type, model.BytesValue(b"x"))
        right = model._admit_shaped_value(right_type, model.BytesValue(b"x"))

        self.assertEqual(left.bytes(), right.bytes())
        self.assertNotEqual(left, right)
        self.assertNotEqual(
            model.value_type_datum(left_type), model.value_type_datum(right_type)
        )
        with self.assertRaises(model.UnsupportedValueDomainError):
            model.value_id("FixtureValue", right)

        same = value(left_type, model.BytesValue(b"x"))
        different = value(left_type, model.BytesValue(b"y"))
        wider_type = model.ValueType(model.BYTES_DOMAIN, model.BytesSchema(0, 2))
        wider = value(wider_type, model.BytesValue(b"x"))
        self.assertTrue(model.canonical_value_equal(left, same))
        self.assertFalse(model.canonical_value_equal(left, different))
        with self.assertRaises(model.CanonicalError):
            model.canonical_value_equal(left, wider)
        with self.assertRaises(model.CanonicalError):
            model.canonical_value_equal(left, right)

        malformed_supported = model.CanonicalValue(
            model.BYTES_32,
            model.BytesValue(b"not-thirty-two-octets"),
        )
        with self.assertRaises(model.ValueAdmissionRefusedError):
            model.value_id("FixtureValue", malformed_supported)


class SemanticModuleClosureTest(unittest.TestCase):
    def assert_control(
        self,
        outcome: model.Outcome,
        code: str,
        callback: object,
    ) -> None:
        with self.assertRaises(model._Control) as caught:
            callback()  # type: ignore[operator]
        self.assertEqual(caught.exception.outcome, outcome)
        self.assertEqual(caught.exception.code, code)

    def test_diamond_closure_counts_each_node_once_and_each_edge_once(self) -> None:
        leaf = module("fixture.leaf")
        left = module("fixture.left", (leaf.identity,))
        right = module("fixture.right", (leaf.identity,))
        root = module("fixture.root", (left.identity, right.identity))
        supplied = {item.identity: item for item in (root, left, right, leaf)}
        closure = model.authenticate_module_closure(
            (root.identity,), supplied, semantic_regime=model.SEMANTIC_REGIME_ID
        )
        self.assertEqual(closure, model.AuthenticatedModuleClosure(4, 4))

    def test_empty_closure_still_requires_the_selected_semantic_regime(self) -> None:
        for wrong_axis in (model.IDENTITY_PROFILE_ID, model.HASH_SUITE_ID):
            with self.subTest(axis=wrong_axis.subject_kind):
                self.assert_control(
                    model.Outcome.KIND_MISMATCH,
                    "K1-KIND-MODULE-REGIME",
                    lambda wrong_axis=wrong_axis: model.authenticate_module_closure(
                        (),
                        {},
                        semantic_regime=wrong_axis,
                    ),
                )

        self.assert_control(
            model.Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-REGIME",
            lambda: model.authenticate_module_closure(
                (),
                {},
                semantic_regime=malformed_prior_meta_id(model.SEMANTIC_REGIME_ID),
            ),
        )

        unsupported_regime = model.PriorMetaId(
            model.FOUNDATION_PROFILE,
            model.SEMANTIC_REGIME_KIND,
            b"\xff" * 32,
        )
        self.assert_control(
            model.Outcome.UNSUPPORTED,
            "K1-UNSUPPORTED-MODULE-REGIME",
            lambda: model.authenticate_module_closure(
                (),
                {},
                semantic_regime=unsupported_regime,
            ),
        )

        regime_fixture = model.CanonicalAlgorithm(
            model.Symbol("AlgorithmRegimeCarrierFixture"),
            (),
            model.Literal(value(model.UNIT_VALUE, model.UNIT)),
        )
        wrong_regime_kind = model.Evaluator().evaluate(
            replace(
                regime_fixture,
                semantic_regime=model.IDENTITY_PROFILE_ID,
            ),
            (),
        )
        self.assertEqual(wrong_regime_kind.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(wrong_regime_kind.code, "K1-KIND-ALGORITHM-REGIME")

        malformed_regime = model.Evaluator().evaluate(
            replace(
                regime_fixture,
                semantic_regime=malformed_prior_meta_id(model.SEMANTIC_REGIME_ID),
            ),
            (),
        )
        self.assertEqual(malformed_regime.outcome, model.Outcome.MALFORMED)
        self.assertEqual(malformed_regime.code, "K1-MALFORMED-MODEL")

        unsupported_unit = model.ValueType(
            model.ValueDomain(
                unsupported_regime,
                model.ROOT_VALUE_DOMAIN_KIND,
                0,
            ),
            model.UnitSchema(),
        )
        cross_regime_algorithm = model.CanonicalAlgorithm(
            model.Symbol("CrossRegimeAlgorithm"),
            (),
            model.Literal(model.CanonicalValue(unsupported_unit, model.UNIT)),
            semantic_regime=unsupported_regime,
        )
        algorithm_result = model.Evaluator().evaluate(cross_regime_algorithm, ())
        self.assertEqual(algorithm_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(algorithm_result.code, "K1-KIND-ALGORITHM-REGIME")

        cross_regime_input = model.CanonicalAlgorithm(
            model.Symbol("CrossRegimeInput"),
            (unsupported_unit,),
            model.Variable(0, unsupported_unit),
        )
        self.assertIsInstance(
            model.authenticate_algorithm_identity(cross_regime_input),
            model.TypedContentId,
        )
        input_result = model.Evaluator().evaluate(cross_regime_input, ())
        self.assertEqual(input_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(input_result.code, "K1-KIND-ALGORITHM-REGIME")

        cross_regime_literal = model.CanonicalAlgorithm(
            model.Symbol("CrossRegimeLiteral"),
            (),
            model.Literal(model.CanonicalValue(unsupported_unit, model.UNIT)),
        )
        self.assertIsInstance(
            model.authenticate_algorithm_identity(cross_regime_literal),
            model.TypedContentId,
        )
        literal_result = model.Evaluator().evaluate(cross_regime_literal, ())
        self.assertEqual(literal_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(literal_result.code, "K1-KIND-ALGORITHM-REGIME")

        foreign_module = model.content_id(
            model.SEMANTIC_MODULE_KIND,
            model.encode_datum(model.Symbol("foreign-module")),
            semantic_regime=unsupported_regime,
        )
        foreign_primitive = primitive_reference(foreign_module, 0)
        projection = model.build_lossy_projection_algorithm()
        self.assertIsInstance(projection.term, model.PrimitiveCall)
        cross_regime_primitive = replace(
            projection,
            term=replace(projection.term, primitive=foreign_primitive),
        )
        self.assertIsInstance(
            model.authenticate_algorithm_identity(cross_regime_primitive),
            model.TypedContentId,
        )
        primitive_result = model.Evaluator().evaluate(
            cross_regime_primitive,
            (value(model.BYTES_32, model.BytesValue(b"p" * 32)),),
        )
        self.assertEqual(primitive_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(primitive_result.code, "K1-KIND-ALGORITHM-REGIME")

        foreign_failure = model.SemanticFailureType(
            foreign_module,
            0,
            unsupported_unit,
        )
        cross_regime_failure = model.CanonicalAlgorithm(
            model.Symbol("CrossRegimeFailure"),
            (),
            model.Fail(
                foreign_failure,
                model.Literal(model.CanonicalValue(unsupported_unit, model.UNIT)),
                model.UNIT_VALUE,
            ),
        )
        self.assertIsInstance(
            model.authenticate_algorithm_identity(cross_regime_failure),
            model.TypedContentId,
        )
        failure_result = model.Evaluator().evaluate(cross_regime_failure, ())
        self.assertEqual(failure_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(failure_result.code, "K1-KIND-ALGORITHM-REGIME")

        mixed_regime_failure = model.SemanticFailureType(
            foreign_module,
            0,
            model.UNIT_VALUE,
        )
        mixed_regime_algorithm = model.CanonicalAlgorithm(
            model.Symbol("MixedRegimeFailureCoordinate"),
            (),
            model.Fail(
                mixed_regime_failure,
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                model.UNIT_VALUE,
            ),
        )
        mixed_failure_result = model.Evaluator().evaluate(
            mixed_regime_algorithm,
            (),
        )
        self.assertEqual(
            mixed_failure_result.outcome,
            model.Outcome.KIND_MISMATCH,
        )
        self.assertEqual(
            mixed_failure_result.code,
            "K1-KIND-ALGORITHM-REGIME",
        )

        cross_regime_contract = model.content_id(
            "foundation.evaluation-contract",
            model.encode_datum(model.Symbol("cross-regime-contract")),
            semantic_regime=unsupported_regime,
        )
        baseline_algorithm = model.CanonicalAlgorithm(
            model.Symbol("ContractRegimeFixture"),
            (),
            model.Literal(value(model.UNIT_VALUE, model.UNIT)),
        )
        contract_result = model.Evaluator().evaluate(
            baseline_algorithm,
            (),
            evaluation_contract=cross_regime_contract,
        )
        self.assertEqual(contract_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(contract_result.code, "K1-KIND-EVALUATION-CONTRACT")

        malformed_wrong_kind_contract = object.__new__(model.TypedContentId)
        for field in (
            "foundation_profile",
            "identity_profile",
            "hash_suite",
            "semantic_regime",
        ):
            object.__setattr__(
                malformed_wrong_kind_contract,
                field,
                getattr(cross_regime_contract, field),
            )
        object.__setattr__(
            malformed_wrong_kind_contract,
            "subject_kind",
            "foundation.not-an-evaluation-contract",
        )
        object.__setattr__(malformed_wrong_kind_contract, "digest", b"short")
        malformed_contract_result = model.Evaluator().evaluate(
            baseline_algorithm,
            (),
            evaluation_contract=malformed_wrong_kind_contract,
        )
        self.assertEqual(
            malformed_contract_result.outcome,
            model.Outcome.MALFORMED,
        )
        self.assertEqual(
            malformed_contract_result.code,
            "K1-MALFORMED-EVALUATION-CONTRACT",
        )

        foreign_inline_contract = object.__new__(model.EvaluationContractV0)
        for field in (
            "term_step_units",
            "iteration_item_units",
            "validation_precedence",
            "completion_measure",
            "static_bound_rule",
            "primitive_cost_rules",
        ):
            object.__setattr__(
                foreign_inline_contract,
                field,
                getattr(model.DEFAULT_EVALUATION_CONTRACT, field),
            )
        object.__setattr__(
            foreign_inline_contract,
            "semantic_regime",
            unsupported_regime,
        )
        inline_result = model.Evaluator().evaluate(
            baseline_algorithm,
            (),
            evaluation_contract=foreign_inline_contract,
        )
        self.assertEqual(inline_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(inline_result.code, "K1-KIND-EVALUATION-CONTRACT")

        wrong_kind_inline_contract = object.__new__(model.EvaluationContractV0)
        for field in (
            "term_step_units",
            "iteration_item_units",
            "validation_precedence",
            "completion_measure",
            "static_bound_rule",
            "primitive_cost_rules",
        ):
            object.__setattr__(
                wrong_kind_inline_contract,
                field,
                getattr(model.DEFAULT_EVALUATION_CONTRACT, field),
            )
        object.__setattr__(
            wrong_kind_inline_contract,
            "semantic_regime",
            model.IDENTITY_PROFILE_ID,
        )
        wrong_kind_inline_result = model.Evaluator().evaluate(
            baseline_algorithm,
            (),
            evaluation_contract=wrong_kind_inline_contract,
        )
        self.assertEqual(
            wrong_kind_inline_result.outcome,
            model.Outcome.KIND_MISMATCH,
        )
        self.assertEqual(
            wrong_kind_inline_result.code,
            "K1-KIND-EVALUATION-CONTRACT",
        )

        wrong_primitive_kind = model.content_id(
            "foundation.not-a-semantic-primitive",
            model.encode_datum(model.Symbol("wrong-cost-key")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        wrong_rule = model.PrimitiveCostRuleV0(
            wrong_primitive_kind,
            model.PrimitiveWorkFormulaV0(model.Symbol("fixed"), (), 0),
        )
        wrong_key_contract = object.__new__(model.EvaluationContractV0)
        for field in (
            "term_step_units",
            "iteration_item_units",
            "validation_precedence",
            "completion_measure",
            "static_bound_rule",
            "semantic_regime",
        ):
            object.__setattr__(
                wrong_key_contract,
                field,
                getattr(model.DEFAULT_EVALUATION_CONTRACT, field),
            )
        object.__setattr__(
            wrong_key_contract,
            "primitive_cost_rules",
            (wrong_rule,),
        )
        wrong_key_result = model.Evaluator().evaluate(
            baseline_algorithm,
            (),
            evaluation_contract=wrong_key_contract,
        )
        self.assertEqual(wrong_key_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(wrong_key_result.code, "K1-KIND-EVALUATION-CONTRACT")

        malformed_rule = object.__new__(model.PrimitiveCostRuleV0)
        object.__setattr__(
            malformed_rule,
            "primitive",
            malformed_content_id(model.DEFAULT_SUPPORTED_PRIMITIVES[0]),
        )
        object.__setattr__(
            malformed_rule,
            "formula",
            model.PrimitiveWorkFormulaV0(model.Symbol("fixed"), (), 0),
        )
        malformed_rule_contract = object.__new__(model.EvaluationContractV0)
        for field in (
            "term_step_units",
            "iteration_item_units",
            "validation_precedence",
            "completion_measure",
            "static_bound_rule",
            "semantic_regime",
        ):
            object.__setattr__(
                malformed_rule_contract,
                field,
                getattr(model.DEFAULT_EVALUATION_CONTRACT, field),
            )
        object.__setattr__(
            malformed_rule_contract,
            "primitive_cost_rules",
            (malformed_rule,),
        )
        malformed_rule_result = model.Evaluator().evaluate(
            baseline_algorithm,
            (),
            evaluation_contract=malformed_rule_contract,
        )
        self.assertEqual(malformed_rule_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            malformed_rule_result.code,
            "K1-MALFORMED-EVALUATION-CONTRACT",
        )

        valid_module = module("fixture.module-key-carrier")
        malformed_module = malformed_content_id(valid_module.identity)
        self.assert_control(
            model.Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-ROOTS",
            lambda: model.authenticate_module_closure(
                (malformed_module,),
                {},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )
        self.assert_control(
            model.Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-BUNDLE",
            lambda: model.authenticate_module_closure(
                (),
                {malformed_module: valid_module},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )

        wrong_bundle_kind = model.content_id(
            "foundation.portable-algorithm",
            model.encode_datum(model.Symbol("wrong-module-bundle-kind")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assert_control(
            model.Outcome.KIND_MISMATCH,
            "K1-KIND-MODULE",
            lambda: model.authenticate_module_closure(
                (),
                {wrong_bundle_kind: valid_module},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )
        self.assert_control(
            model.Outcome.KIND_MISMATCH,
            "K1-KIND-MODULE-REGIME",
            lambda: model.authenticate_module_closure(
                (),
                {foreign_module: valid_module},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )

        malformed_importer = model.SemanticModuleCandidate(
            model.Symbol("fixture.malformed-import-carrier"),
            (malformed_module,),
            model.DatumSeq(()),
        )
        asserted_importer = model.content_id(
            model.SEMANTIC_MODULE_KIND,
            model.encode_datum(model.Symbol("asserted-malformed-importer")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assert_control(
            model.Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-PREIMAGE",
            lambda: model.authenticate_module_closure(
                (asserted_importer,),
                {asserted_importer: malformed_importer},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )

    def test_deep_module_chain_is_not_limited_by_host_recursion(self) -> None:
        chain = [module("fixture.deep-0")]
        for index in range(1, 1100):
            chain.append(module(f"fixture.deep-{index}", (chain[-1].identity,)))
        supplied = {item.identity: item for item in chain}
        closure = model.authenticate_module_closure(
            (chain[-1].identity,),
            supplied,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assertEqual(closure, model.AuthenticatedModuleClosure(1100, 1099))

    def test_module_node_and_edge_limits_are_independent(self) -> None:
        leaf = module("fixture.limit-leaf")
        left = module("fixture.limit-left", (leaf.identity,))
        right = module("fixture.limit-right", (leaf.identity,))
        root = module("fixture.limit-root", (left.identity, right.identity))
        supplied = {item.identity: item for item in (root, left, right, leaf)}
        with patch.object(model, "MAX_MODULE_NODES", 3):
            self.assert_control(
                model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                "K1-LIMIT-MODULE-NODES",
                lambda: model.authenticate_module_closure(
                    (root.identity,),
                    supplied,
                    semantic_regime=model.SEMANTIC_REGIME_ID,
                ),
            )
        with patch.object(model, "MAX_MODULE_EDGES", 3):
            self.assert_control(
                model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                "K1-LIMIT-MODULE-EDGES",
                lambda: model.authenticate_module_closure(
                    (root.identity,),
                    supplied,
                    semantic_regime=model.SEMANTIC_REGIME_ID,
                ),
            )

        chain = [module("fixture.discovery-0")]
        for index in range(1, 4):
            chain.append(module(f"fixture.discovery-{index}", (chain[-1].identity,)))
        chain_supplied = {item.identity: item for item in chain}
        chain_root_id = chain[-1].identity
        authenticated: list[str] = []
        original_body = model.SemanticModuleCandidate.body

        def counted_body(candidate: model.SemanticModuleCandidate) -> bytes:
            authenticated.append(candidate.diagnostic_label.value)
            return original_body(candidate)

        with (
            patch.object(model, "MAX_MODULE_NODES", 3),
            patch.object(model.SemanticModuleCandidate, "body", counted_body),
        ):
            self.assert_control(
                model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                "K1-LIMIT-MODULE-NODES",
                lambda: model.authenticate_module_closure(
                    (chain_root_id,),
                    chain_supplied,
                    semantic_regime=model.SEMANTIC_REGIME_ID,
                ),
            )
        self.assertEqual(len(authenticated), 3)

    def test_module_bundle_entry_limit_precedes_key_scan_and_closure(self) -> None:
        extras = tuple(module(f"fixture.unrelated-{index}") for index in range(4))
        exact_bound = {item.identity: item for item in extras[:3]}
        over_bound = {item.identity: item for item in extras}
        with patch.object(model, "MAX_MODULE_BUNDLE_ENTRIES", 3):
            exact_result = model.Evaluator().evaluate(
                model.build_lossy_projection_algorithm(),
                (value(model.BYTES_32, model.BytesValue(b"p" * 32)),),
                modules=exact_bound,
            )
            over_result = model.Evaluator().evaluate(
                model.build_lossy_projection_algorithm(),
                (value(model.BYTES_32, model.BytesValue(b"p" * 32)),),
                modules=over_bound,
            )
        self.assertEqual(exact_result.outcome, model.Outcome.MISSING_DEPENDENCY)
        self.assertEqual(exact_result.code, "K1-MISSING-MODULE")
        self.assertEqual(
            over_result.outcome, model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED
        )
        self.assertEqual(over_result.code, "K1-LIMIT-MODULE-BUNDLE-ENTRIES")

    def test_module_bundle_key_cannot_impersonate_required_identifier(self) -> None:
        required = model.FIXTURE_EXTENSION_MODULE_ID

        class IdentifierAlias:
            comparisons = 0

            def __hash__(self) -> int:
                return hash(required)

            def __eq__(self, other: object) -> bool:
                type(self).comparisons += 1
                raise AssertionError("host equality must not execute")

        result = model.Evaluator().evaluate(
            model.build_lossy_projection_algorithm(),
            (value(model.BYTES_32, model.BytesValue(b"a" * 32)),),
            modules={IdentifierAlias(): model.FIXTURE_EXTENSION_MODULE_CANDIDATE},  # type: ignore[dict-item]
        )
        self.assertEqual(result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(result.code, "K1-MALFORMED-MODULE-BUNDLE")
        self.assertEqual(IdentifierAlias.comparisons, 0)

    def test_module_diagnostics_are_nonsemantic_but_declarations_and_payload_bind(
        self,
    ) -> None:
        baseline = module("fixture.module-identity", payload=model.Symbol("payload"))
        relabeled = replace(
            baseline, diagnostic_label=model.Symbol("different-diagnostic-label")
        )
        opaque_diagnostic = replace(baseline, diagnostic_label=object())  # type: ignore[arg-type]
        declaration_changed = module(
            "fixture.other-declaration", payload=model.Symbol("payload")
        )
        payload_changed = replace(
            baseline, domain_payload=model.Symbol("different-payload")
        )

        self.assertEqual(baseline.identity, relabeled.identity)
        self.assertEqual(baseline.identity, opaque_diagnostic.identity)
        self.assertEqual(baseline.body(), opaque_diagnostic.body())
        self.assertNotEqual(baseline.identity, declaration_changed.identity)
        self.assertNotEqual(baseline.identity, payload_changed.identity)
        other_regime = model.meta_object_id(
            model.SEMANTIC_REGIME_KIND,
            model.encode_datum(model.Symbol("other-module-regime")),
        )
        self.assertEqual(baseline.body(), relabeled.body())
        self.assertNotEqual(
            baseline.identity_for(other_regime),
            baseline.identity,
        )
        closure = model.authenticate_module_closure(
            (baseline.identity,),
            {baseline.identity: relabeled},
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assertEqual(closure.nodes, 1)

    def test_direct_catalog_helper_requires_canonical_catalog_carriers(self) -> None:
        baseline = module("fixture.catalog-carriers")

        class TextSubclass(str):
            pass

        aliased_kind = model.DatumSeq(
            (
                model.DatumRecord(
                    (
                        (0, model.Symbol(TextSubclass("fixture-declaration"))),
                        (1, model.DatumSeq(())),
                    )
                ),
            )
        )
        with self.assertRaises(model.CanonicalError):
            model.module_declaration_catalogs(
                replace(baseline, local_declarations=aliased_kind)
            )

        mutable_catalogs = model.DatumSeq([])  # type: ignore[arg-type]
        with self.assertRaises(model.ModelError):
            model.module_declaration_catalogs(
                replace(baseline, local_declarations=mutable_catalogs)
            )

    def test_missing_extra_and_wrong_preimage_fail_closed(self) -> None:
        leaf = module("fixture.leaf")
        root = module("fixture.root", (leaf.identity,))
        unrelated = module("fixture.unrelated")

        self.assert_control(
            model.Outcome.MISSING_DEPENDENCY,
            "K1-MISSING-MODULE",
            lambda: model.authenticate_module_closure(
                (root.identity,),
                {root.identity: root},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )
        self.assert_control(
            model.Outcome.REFUSED,
            "K1-REFUSED-EXTRA-MODULE",
            lambda: model.authenticate_module_closure(
                (root.identity,),
                {
                    root.identity: root,
                    leaf.identity: leaf,
                    unrelated.identity: unrelated,
                },
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )
        changed = replace(leaf, domain_payload=model.Symbol("changed-preimage"))
        self.assert_control(
            model.Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-PREIMAGE",
            lambda: model.authenticate_module_closure(
                (leaf.identity,),
                {leaf.identity: changed},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )

    def test_wrong_kind_and_cross_regime_imports_are_distinct(self) -> None:
        wrong_kind = model.content_id(
            "CanonicalAlgorithm",
            model.encode_datum(model.Symbol("wrong-kind")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assert_control(
            model.Outcome.KIND_MISMATCH,
            "K1-KIND-MODULE",
            lambda: model.authenticate_module_closure(
                (wrong_kind,), {}, semantic_regime=model.SEMANTIC_REGIME_ID
            ),
        )

        other_regime = model.meta_object_id(
            model.SEMANTIC_REGIME_KIND,
            model.encode_datum(model.Symbol("other-regime")),
        )
        foreign = module("fixture.foreign")
        foreign_id = foreign.identity_for(other_regime)
        self.assert_control(
            model.Outcome.KIND_MISMATCH,
            "K1-KIND-MODULE-REGIME",
            lambda: model.authenticate_module_closure(
                (foreign_id,),
                {foreign_id: foreign},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )

    def test_forged_cycle_is_rejected_at_the_preimage_before_traversal(self) -> None:
        fake_a = model.content_id(
            model.SEMANTIC_MODULE_KIND,
            model.encode_datum(model.Symbol("fake-a")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        fake_b = model.content_id(
            model.SEMANTIC_MODULE_KIND,
            model.encode_datum(model.Symbol("fake-b")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        candidate_a = module("fixture.a", (fake_b,))
        candidate_b = module("fixture.b", (fake_a,))
        self.assert_control(
            model.Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-PREIMAGE",
            lambda: model.authenticate_module_closure(
                (fake_a,),
                {fake_a: candidate_a, fake_b: candidate_b},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )

    def test_candidate_authenticates_before_any_import_is_traversed(self) -> None:
        absent = model.content_id(
            model.SEMANTIC_MODULE_KIND,
            model.encode_datum(model.Symbol("absent-child")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        candidate = module("fixture.importing-root", (absent,))
        forged_root = model.content_id(
            model.SEMANTIC_MODULE_KIND,
            model.encode_datum(model.Symbol("forged-root")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )

        self.assert_control(
            model.Outcome.MALFORMED,
            "K1-MALFORMED-MODULE-PREIMAGE",
            lambda: model.authenticate_module_closure(
                (forged_root,),
                {forged_root: candidate},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )
        self.assert_control(
            model.Outcome.MISSING_DEPENDENCY,
            "K1-MISSING-MODULE",
            lambda: model.authenticate_module_closure(
                (candidate.identity,),
                {candidate.identity: candidate},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )

    def test_extension_locality_rotates_only_subjects_that_use_the_module(self) -> None:
        base = module("fixture.extension", payload=model.Symbol("v1"))
        changed = module("fixture.extension", payload=model.Symbol("v2"))
        unrelated = module("fixture.unrelated")
        before_regime = model.SEMANTIC_REGIME_ID

        base_algorithm = model.build_module_dependent_algorithm(base.identity)
        same_algorithm = model.build_module_dependent_algorithm(base.identity)
        changed_algorithm = model.build_module_dependent_algorithm(changed.identity)

        self.assertEqual(model.SEMANTIC_REGIME_ID, before_regime)
        self.assertNotEqual(unrelated.identity, base.identity)
        self.assertEqual(base_algorithm.identity, same_algorithm.identity)
        self.assertNotEqual(base_algorithm.identity, changed_algorithm.identity)


class SemanticProfileAndAuthorityEnvelopeTest(unittest.TestCase):
    @staticmethod
    def semantic_id(kind: str, label: str) -> model.TypedContentId:
        return model.content_id(
            kind,
            model.encode_datum(model.Symbol(label)),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )

    @staticmethod
    def profile_fixture(
        law: bytes = b"analysis-kernel-law-v0",
    ) -> tuple[
        model.SemanticLanguageProfileId,
        dict[model.SemanticLanguageProfileId, model.SemanticLanguageProfile],
    ]:
        relations = language_profile(
            "zkc.relations.language",
            ("relations.artifact",),
            b"relations-law-v0",
        )
        analysis = language_profile(
            "zkc.analysis.kernel-language",
            ("analysis.goal", "analysis.judgment"),
            law,
            profile_imports=(relations.identity,),
        )
        return (
            analysis.identity,
            {
                analysis.identity: analysis,
                relations.identity: relations,
            },
        )

    def test_foundation_standalone_subject_catalog_is_exact(self) -> None:
        profile, _ = self.profile_fixture()
        canonical = value(model.BYTES_32, model.BytesValue(b"v" * 32))
        canonical_id = model.value_id("fixture.canonical-value", canonical)
        canonical_body = model.decode_datum(
            model.value_preimage("fixture.canonical-value", canonical)
        )
        self.assertIsInstance(canonical_body, model.DatumRecord)
        canonical_fields = dict(canonical_body.fields)
        self.assertEqual(tuple(canonical_fields), (0, 1, 2, 3))
        self.assertEqual(
            canonical_fields[0],
            model.Symbol("fixture.canonical-value"),
        )
        self.assertEqual(canonical_id.subject_kind, model.CANONICAL_VALUE_KIND)
        self.assertNotEqual(
            canonical_id,
            model.value_id("fixture.other-purpose", canonical),
        )

        external = model.ExternalOperationContract(
            model.Symbol("RemoteHashService"),
            model.SemanticFunctionType((model.BYTES_0_32,), model.BYTES_32),
        )
        standalone_ids = (
            profile,
            model.FIXTURE_EXTENSION_MODULE_ID,
            canonical_id,
            next(iter(model.PRIMITIVE_IDS_BY_KEY.values())),
            model.build_transcript_algorithm().identity,
            model.DEFAULT_EVALUATION_CONTRACT.identity,
            external.identity,
        )
        self.assertEqual(
            frozenset(identifier.subject_kind for identifier in standalone_ids),
            model.FOUNDATION_STANDALONE_SEMANTIC_SUBJECT_KINDS,
        )
        self.assertEqual(
            external.identity,
            model.content_id(
                model.EXTERNAL_OPERATION_CONTRACT_KIND,
                external.body(),
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )

    def test_profiled_subject_authenticates_exact_used_profile_closure(self) -> None:
        profile, supplied_profiles = self.profile_fixture()
        domain_body = model.DatumRecord(((0, model.Symbol("goal-7")),))
        identifier = model.profiled_content_id(
            "analysis.goal",
            profile,
            domain_body,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )

        context = model.authenticate_profiled_semantic_content(
            identifier,
            profile,
            domain_body,
            supplied_profiles,
            supported_profiles=(profile,),
        )
        repeated = model.effective_semantic_context(
            profile,
            supplied_profiles,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )

        self.assertEqual(context.selected_profile, profile)
        self.assertEqual(context.selected_profile_body.profile_family.value,
                         "zkc.analysis.kernel-language")
        self.assertEqual(len(context.authenticated_profiles), 2)
        self.assertTrue(model.semantic_contexts_are_identical(context, repeated))
        body = model.profiled_semantic_body(profile, domain_body)
        self.assertEqual(tuple(dict(body.fields)), (0, 1))
        self.assertEqual(
            dict(body.fields)[0],
            model.BytesValue(profile.internal_reference()),
        )

    def test_profile_change_rotates_only_dependent_profiled_subjects(self) -> None:
        profile_v0, profiles_v0 = self.profile_fixture(
            b"analysis-law-v0"
        )
        profile_v1, profiles_v1 = self.profile_fixture(
            b"analysis-law-v1"
        )
        unrelated = language_profile(
            "zkc.oir.endpoint-language",
            ("oir.endpoint-graph",),
            b"oir-law-v0",
        )
        domain_body = model.Symbol("same-domain-body")
        before = model.profiled_content_id(
            "analysis.goal",
            profile_v0,
            domain_body,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        after = model.profiled_content_id(
            "analysis.goal",
            profile_v1,
            domain_body,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )

        self.assertNotEqual(profile_v0, profile_v1)
        self.assertNotEqual(before, after)
        self.assertNotIn(unrelated.identity, profiles_v0)
        self.assertEqual(
            before,
            model.profiled_content_id(
                "analysis.goal",
                profile_v0,
                domain_body,
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )
        context_v0 = model.effective_semantic_context(
            profile_v0,
            profiles_v0,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        context_v1 = model.effective_semantic_context(
            profile_v1,
            profiles_v1,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assertFalse(
            model.semantic_contexts_are_identical(context_v0, context_v1)
        )

        new_subject = model.profiled_content_id(
            "analysis.goal",
            profile_v1,
            domain_body,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        with self.assertRaises(model._Control) as caught:
            model.authenticate_profiled_semantic_content(
                new_subject,
                profile_v1,
                domain_body,
                profiles_v1,
                supported_profiles=(profile_v0,),
            )
        self.assertIs(caught.exception.outcome, model.Outcome.UNSUPPORTED)
        self.assertEqual(caught.exception.code, "K1-UNSUPPORTED-PROFILE")

    def test_import_change_rotates_composition_profile_and_dependent_subject(self) -> None:
        upstream_v0 = language_profile(
            "zkc.relations.language",
            ("relations.artifact",),
            b"relations-law-v0",
        )
        upstream_v1 = replace(upstream_v0, semantic_law_source=b"relations-law-v1")
        selected_v0 = language_profile(
            "zkc.analysis.language",
            ("analysis.goal",),
            b"analysis-law",
            profile_imports=(upstream_v0.identity,),
        )
        selected_v1 = replace(
            selected_v0,
            profile_imports=(upstream_v1.identity,),
        )
        domain_body = model.Symbol("same-analysis-goal")

        self.assertNotEqual(upstream_v0.identity, upstream_v1.identity)
        self.assertNotEqual(selected_v0.identity, selected_v1.identity)
        self.assertNotEqual(
            model.profiled_content_id(
                "analysis.goal",
                selected_v0.identity,
                domain_body,
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
            model.profiled_content_id(
                "analysis.goal",
                selected_v1.identity,
                domain_body,
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
        )

    def test_one_selected_composition_profile_closes_both_language_imports(self) -> None:
        relations = language_profile(
            "zkc.relations.language",
            ("relations.artifact",),
            b"relations-law",
        )
        protocol = language_profile(
            "zkc.pir.language",
            ("pir.protocol",),
            b"pir-law",
        )
        imports = tuple(
            sorted(
                (relations.identity, protocol.identity),
                key=lambda item: item.internal_reference(),
            )
        )
        composition = language_profile(
            "zkc.analysis.protocol-relation-language",
            ("analysis.goal",),
            b"analysis-composition-law",
            profile_imports=imports,
        )
        supplied = {
            item.identity: item for item in (composition, relations, protocol)
        }

        context = model.effective_semantic_context(
            composition.identity,
            supplied,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assertEqual(context.selected_profile, composition.identity)
        self.assertEqual(len(context.authenticated_profiles), 3)

    def test_profile_closure_rejects_missing_and_extra_preimages(self) -> None:
        profile, supplied_profiles = self.profile_fixture()
        selected = supplied_profiles[profile]
        missing_import = {profile: selected}
        with self.assertRaises(model._Control) as caught:
            model.effective_semantic_context(
                profile,
                missing_import,
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.Outcome.MISSING_DEPENDENCY)
        self.assertEqual(caught.exception.code, "K1-MISSING-PROFILE")

        unrelated = language_profile(
            "zkc.unused.language",
            ("unused.subject",),
            b"unused-law-v0",
        )
        with self.assertRaises(model._Control) as caught:
            model.effective_semantic_context(
                profile,
                {**supplied_profiles, unrelated.identity: unrelated},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.Outcome.REFUSED)
        self.assertEqual(caught.exception.code, "K1-REFUSED-EXTRA-PROFILE")

    def test_profile_catalogs_and_local_or_imported_refs_are_exact(self) -> None:
        upstream_catalogs = model.DatumSeq(
            (
                model.DatumRecord(
                    (
                        (0, model.Symbol("relations.fact")),
                        (1, model.DatumSeq((model.Symbol("fact-law"),))),
                    )
                ),
            )
        )
        upstream = language_profile(
            "zkc.relations.language",
            ("relations.artifact",),
            b"relations-law",
            declaration_catalogs=upstream_catalogs,
        )
        local_catalogs = model.DatumSeq(
            (
                model.DatumRecord(
                    (
                        (0, model.Symbol("analysis.rule")),
                        (1, model.DatumSeq((model.Symbol("rule-law"),))),
                    )
                ),
            )
        )
        selected = language_profile(
            "zkc.analysis.language",
            ("analysis.judgment",),
            b"analysis-law",
            profile_imports=(upstream.identity,),
            declaration_catalogs=local_catalogs,
        )
        supplied = {
            selected.identity: selected,
            upstream.identity: upstream,
        }
        context = model.effective_semantic_context(
            selected.identity,
            supplied,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        local = model.ProfileLocalDeclarationRef("analysis.rule", 0)
        imported = model.ImportedProfileDeclarationRef(
            upstream.identity,
            "relations.fact",
            0,
        )
        self.assertEqual(
            model.resolve_profile_declaration(context, local),
            model.Symbol("rule-law"),
        )
        self.assertEqual(
            model.resolve_profile_declaration(context, imported),
            model.Symbol("fact-law"),
        )
        self.assertEqual(model.profile_declaration_ref_datum(local).case, 0)
        self.assertEqual(model.profile_declaration_ref_datum(imported).case, 1)
        with self.assertRaisesRegex(
            model.DeclarationAdmissionRefusedError,
            "self declarations must use",
        ):
            model.resolve_profile_declaration(
                context,
                model.ImportedProfileDeclarationRef(
                    selected.identity,
                    "analysis.rule",
                    0,
                ),
            )

        unsorted_catalogs = model.DatumSeq(
            (
                model.DatumRecord(
                    ((0, model.Symbol("z.kind")), (1, model.DatumSeq(())))
                ),
                model.DatumRecord(
                    ((0, model.Symbol("a.kind")), (1, model.DatumSeq(())))
                ),
            )
        )
        with self.assertRaisesRegex(model.ModelError, "sorted and unique"):
            language_profile(
                "zkc.bad.catalogs",
                ("bad.subject",),
                b"bad-law",
                declaration_catalogs=unsorted_catalogs,
            ).body()

    def test_profile_diamond_deep_walk_and_bounds_are_deterministic(self) -> None:
        base = language_profile("zkc.base", ("base.subject",), b"base-law")
        left = language_profile(
            "zkc.left",
            ("left.subject",),
            b"left-law",
            profile_imports=(base.identity,),
        )
        right = language_profile(
            "zkc.right",
            ("right.subject",),
            b"right-law",
            profile_imports=(base.identity,),
        )
        roots = tuple(
            sorted(
                (left.identity, right.identity),
                key=lambda item: item.internal_reference(),
            )
        )
        top = language_profile(
            "zkc.top",
            ("top.subject",),
            b"top-law",
            profile_imports=roots,
        )
        supplied = {
            item.identity: item for item in (top, left, right, base)
        }
        context = model.effective_semantic_context(
            top.identity,
            supplied,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assertEqual(len(context.authenticated_profiles), 4)

        previous = base
        deep: dict[model.TypedContentId, model.SemanticLanguageProfile] = {
            base.identity: base
        }
        for index in range(96):
            current = language_profile(
                f"zkc.deep-{index}",
                (f"deep.subject-{index}",),
                f"deep-law-{index}".encode("ascii"),
                profile_imports=(previous.identity,),
            )
            deep[current.identity] = current
            previous = current
        deep_context = model.effective_semantic_context(
            previous.identity,
            deep,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assertEqual(len(deep_context.authenticated_profiles), 97)

        with patch.object(model, "MAX_PROFILE_EDGES", 0):
            with self.assertRaises(model._Control) as caught:
                model.effective_semantic_context(
                    top.identity,
                    supplied,
                    semantic_regime=model.SEMANTIC_REGIME_ID,
                )
            self.assertIs(
                caught.exception.outcome,
                model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
            )
            self.assertEqual(caught.exception.code, "K1-LIMIT-PROFILE-EDGES")

        with patch.object(model, "MAX_PROFILE_NODES", 3):
            with self.assertRaises(model._Control) as caught:
                model.effective_semantic_context(
                    top.identity,
                    supplied,
                    semantic_regime=model.SEMANTIC_REGIME_ID,
                )
            self.assertIs(
                caught.exception.outcome,
                model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
            )
            self.assertEqual(caught.exception.code, "K1-LIMIT-PROFILE-NODES")

    def test_profile_bundle_preflight_and_forged_preimage_fail_closed(self) -> None:
        profile, supplied = self.profile_fixture()
        with patch.object(model, "MAX_PROFILE_BUNDLE_ENTRIES", 0):
            with self.assertRaises(model._Control) as caught:
                model.effective_semantic_context(
                    profile,
                    {object(): object()},  # type: ignore[dict-item]
                    semantic_regime=model.SEMANTIC_REGIME_ID,
                )
            self.assertIs(
                caught.exception.outcome,
                model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
            )
            self.assertEqual(caught.exception.code, "K1-LIMIT-PROFILE-BUNDLE")

        with self.assertRaises(model._Control) as caught:
            model.effective_semantic_context(
                profile,
                {object(): object()},  # type: ignore[dict-item]
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.Outcome.MALFORMED)
        self.assertEqual(caught.exception.code, "K1-MALFORMED-PROFILE-BUNDLE")

        wrong_kind = self.semantic_id("fixture.not-profile", "wrong-kind")
        with self.assertRaises(model._Control) as caught:
            model.effective_semantic_context(
                profile,
                {wrong_kind: supplied[profile]},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(caught.exception.code, "K1-KIND-PROFILE")

        forged = model.content_id(
            model.SEMANTIC_LANGUAGE_PROFILE_KIND,
            model.encode_datum(model.Symbol("forged")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        with self.assertRaises(model._Control) as caught:
            model.effective_semantic_context(
                forged,
                {forged: supplied[profile]},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.Outcome.MALFORMED)
        self.assertEqual(caught.exception.code, "K1-MALFORMED-PROFILE-PREIMAGE")

        fake_a = model.content_id(
            model.SEMANTIC_LANGUAGE_PROFILE_KIND,
            model.encode_datum(model.Symbol("fake-profile-a")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        fake_b = model.content_id(
            model.SEMANTIC_LANGUAGE_PROFILE_KIND,
            model.encode_datum(model.Symbol("fake-profile-b")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        candidate_a = language_profile(
            "zkc.fake-a",
            ("fake.a",),
            b"fake-a-law",
            profile_imports=(fake_b,),
        )
        candidate_b = language_profile(
            "zkc.fake-b",
            ("fake.b",),
            b"fake-b-law",
            profile_imports=(fake_a,),
        )
        with self.assertRaises(model._Control) as caught:
            model.effective_semantic_context(
                fake_a,
                {fake_a: candidate_a, fake_b: candidate_b},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.Outcome.MALFORMED)
        self.assertEqual(caught.exception.code, "K1-MALFORMED-PROFILE-PREIMAGE")

    def test_profile_formation_and_subject_support_fail_closed(self) -> None:
        with self.assertRaisesRegex(model.ModelError, "sorted-unique"):
            model.SemanticLanguageProfile(
                model.Symbol("zkc.bad.language"),
                0,
                (),
                (model.Symbol("z.subject"), model.Symbol("a.subject")),
                model.DatumSeq(()),
                b"law",
            ).body()
        with self.assertRaisesRegex(model.ModelError, "nonempty"):
            model.SemanticLanguageProfile(
                model.Symbol("zkc.bad.language"),
                0,
                (),
                (model.Symbol("bad.subject"),),
                model.DatumSeq(()),
                b"",
            ).body()
        for forbidden_kind in sorted(model.PROFILED_FORBIDDEN_SUBJECT_KINDS):
            with self.subTest(profile_forbidden_kind=forbidden_kind):
                with self.assertRaisesRegex(
                    model.ModelError,
                    "prior-meta or standalone Foundation subject kinds",
                ):
                    model.SemanticLanguageProfile(
                        model.Symbol("zkc.bad.language"),
                        0,
                        (),
                        (model.Symbol(forbidden_kind),),
                        model.DatumSeq(()),
                        b"law",
                    ).body()

        profile, supplied_profiles = self.profile_fixture()
        domain_body = model.Symbol("body")
        for forbidden_kind in sorted(model.PROFILED_FORBIDDEN_SUBJECT_KINDS):
            with self.subTest(profiled_id_forbidden_kind=forbidden_kind):
                with self.assertRaisesRegex(
                    model.DeclarationKindMismatchError,
                    "prior-meta or standalone Foundation subject kind",
                ):
                    model.profiled_content_id(
                        forbidden_kind,
                        profile,
                        domain_body,
                        semantic_regime=model.SEMANTIC_REGIME_ID,
                    )

                if forbidden_kind in model.FOUNDATION_STANDALONE_SEMANTIC_SUBJECT_KINDS:
                    externally_formed = model.content_id(
                        forbidden_kind,
                        model.encode_datum(
                            model.profiled_semantic_body(profile, domain_body)
                        ),
                        semantic_regime=model.SEMANTIC_REGIME_ID,
                    )
                    with self.assertRaises(model._Control) as caught:
                        model.authenticate_profiled_semantic_content(
                            externally_formed,
                            profile,
                            domain_body,
                            supplied_profiles,
                            supported_profiles=(profile,),
                        )
                    self.assertIs(
                        caught.exception.outcome,
                        model.Outcome.KIND_MISMATCH,
                    )
                    self.assertEqual(
                        caught.exception.code,
                        "K1-KIND-PROFILED-SUBJECT",
                    )

        unsupported = model.profiled_content_id(
            "pir.core",
            profile,
            domain_body,
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        with self.assertRaises(model._Control) as caught:
            model.authenticate_profiled_semantic_content(
                unsupported,
                profile,
                domain_body,
                supplied_profiles,
                supported_profiles=(profile,),
            )
        self.assertIs(caught.exception.outcome, model.Outcome.REFUSED)
        self.assertEqual(
            caught.exception.code,
            "K1-REFUSED-PROFILE-SUBJECT-KIND",
        )

        with self.assertRaises(model._Control) as caught:
            valid = model.profiled_content_id(
                "analysis.goal",
                profile,
                domain_body,
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
            model.authenticate_profiled_semantic_content(
                valid,
                profile,
                domain_body,
                supplied_profiles,
                supported_profiles=(),
            )
        self.assertIs(caught.exception.outcome, model.Outcome.UNSUPPORTED)
        self.assertEqual(caught.exception.code, "K1-UNSUPPORTED-PROFILE")

        other_regime = model.meta_object_id(
            model.SEMANTIC_REGIME_KIND,
            model.encode_datum(model.Symbol("other-regime")),
        )
        foreign = language_profile(
            "zkc.foreign.language",
            ("foreign.subject",),
            b"foreign-law",
        )
        foreign_id = foreign.identity_for(other_regime)
        with self.assertRaises(model._Control) as caught:
            model.effective_semantic_context(
                foreign_id,
                {foreign_id: foreign},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(caught.exception.code, "K1-KIND-PROFILE-REGIME")

        class HostileProfile(model.SemanticLanguageProfile):
            def body(self) -> model.DatumRecord:
                raise AssertionError("subclass body must not execute")

        exact_profile = supplied_profiles[profile]
        hostile = HostileProfile(
            exact_profile.profile_family,
            exact_profile.revision,
            exact_profile.profile_imports,
            exact_profile.supported_subject_kinds,
            exact_profile.declaration_catalogs,
            exact_profile.semantic_law_source,
        )
        with self.assertRaises(model._Control) as caught:
            model.effective_semantic_context(
                profile,
                {profile: hostile},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        self.assertIs(caught.exception.outcome, model.Outcome.MALFORMED)
        self.assertEqual(caught.exception.code, "K1-MALFORMED-PROFILE-PREIMAGE")

    def authority_fixture(self) -> model.PortableSourceAuthorityBinding:
        identifiers = {
            name: self.semantic_id(f"fixture.{name}", name)
            for name in (
                "source-coordinate",
                "binding-payload",
                "policy",
                "policy-closure",
                "capability-requirement",
                "no-policy-declaration",
            )
        }
        requirement = model.OwnerCapabilityRequirement(
            model.Symbol("relations"),
            model.Symbol("checked-result"),
            identifiers["capability-requirement"],
        )
        return model.PortableSourceAuthorityBinding(
            model.Symbol("relations"),
            model.Symbol("checked-result"),
            identifiers["source-coordinate"],
            identifiers["binding-payload"],
            model.BoundOwnerOperationPolicy(identifiers["policy"]),
            identifiers["policy-closure"],
            requirement,
        )

    def test_portable_authority_binding_is_exact_inert_and_sensitive(self) -> None:
        binding = self.authority_fixture()
        body = model.portable_source_authority_binding_body(binding)
        encoded = model.encode_datum(body)

        self.assertEqual(tuple(dict(body.fields)), tuple(range(7)))
        self.assertEqual(model.decode_datum(encoded), body)
        changed_owner_requirement = model.OwnerCapabilityRequirement(
            model.Symbol("pir"),
            binding.capability_family,
            binding.capability_requirement.owner_requirement,
        )
        changed_family_requirement = model.OwnerCapabilityRequirement(
            binding.owner_domain,
            model.Symbol("admitted-core"),
            binding.capability_requirement.owner_requirement,
        )
        variants = (
            replace(
                binding,
                owner_domain=model.Symbol("pir"),
                capability_requirement=changed_owner_requirement,
            ),
            replace(
                binding,
                capability_family=model.Symbol("admitted-core"),
                capability_requirement=changed_family_requirement,
            ),
            replace(
                binding,
                owner_source_coordinate=self.semantic_id(
                    "fixture.source-coordinate",
                    "changed-source-coordinate",
                ),
            ),
            replace(
                binding,
                owner_binding_payload=self.semantic_id(
                    "fixture.binding-payload",
                    "changed-binding-payload",
                ),
            ),
            replace(
                binding,
                operation_policy=model.BoundOwnerOperationPolicy(
                    self.semantic_id("fixture.policy", "changed-policy")
                ),
            ),
            replace(
                binding,
                owner_policy_closure=self.semantic_id(
                    "fixture.policy-closure",
                    "changed-policy-closure",
                ),
            ),
            replace(
                binding,
                capability_requirement=replace(
                    binding.capability_requirement,
                    owner_requirement=self.semantic_id(
                        "fixture.capability-requirement",
                        "changed-requirement",
                    ),
                ),
            ),
        )
        encodings = {
            model.encode_datum(model.portable_source_authority_binding_body(item))
            for item in (binding, *variants)
        }
        self.assertEqual(len(encodings), 1 + len(variants))

        class HostilePortableBinding(model.PortableSourceAuthorityBinding):
            def body(self) -> model.DatumRecord:
                raise AssertionError("subclass body must not execute")

        hostile = HostilePortableBinding(
            binding.owner_domain,
            binding.capability_family,
            binding.owner_source_coordinate,
            binding.owner_binding_payload,
            binding.operation_policy,
            binding.owner_policy_closure,
            binding.capability_requirement,
        )
        with self.assertRaisesRegex(model.ModelError, "only a portable"):
            model.portable_source_authority_binding_body(hostile)

    def test_authority_policy_and_owner_family_fail_closed(self) -> None:
        binding = self.authority_fixture()
        no_policy = replace(
            binding,
            operation_policy=model.OwnerDefinesNoOperationPolicy(
                self.semantic_id(
                    "fixture.no-policy-declaration",
                    "no-policy-declaration",
                ),
            ),
        )
        body = model.portable_source_authority_binding_body(no_policy)
        self.assertEqual(dict(body.fields)[4].case, 1)

        mismatched = replace(
            binding,
            capability_requirement=model.OwnerCapabilityRequirement(
                model.Symbol("pir"),
                binding.capability_family,
                binding.capability_requirement.owner_requirement,
            ),
        )
        with self.assertRaisesRegex(model.ModelError, "disagree on owner or family"):
            model.portable_source_authority_binding_body(mismatched)

    def test_authority_envelope_rejects_cross_regime_and_never_serializes_live_capability(self) -> None:
        binding = self.authority_fixture()
        other_regime = model.meta_object_id(
            model.SEMANTIC_REGIME_KIND,
            model.encode_datum(model.Symbol("authority-other-regime")),
        )
        foreign_closure = model.content_id(
            "fixture.policy-closure",
            model.encode_datum(model.Symbol("foreign")),
            semantic_regime=other_regime,
        )
        with self.assertRaisesRegex(
            model.DeclarationKindMismatchError,
            "crosses semantic regimes",
        ):
            model.portable_source_authority_binding_body(
                replace(binding, owner_policy_closure=foreign_closure)
            )

        local = model.OwnerLocalSourceAuthorityBinding(
            binding.owner_domain,
            binding.capability_family,
            object(),
            binding.owner_binding_payload,
            binding.operation_policy,
            binding.owner_policy_closure,
            binding.capability_requirement,
        )
        self.assertIsNone(
            model.validate_owner_local_source_authority_binding(local)
        )
        self.assertEqual(
            repr(local),
            "OwnerLocalSourceAuthorityBinding(<process-local>)",
        )
        with self.assertRaises(model.CanonicalError):
            model.encode_datum(local)  # type: ignore[arg-type]
        with self.assertRaisesRegex(model.ModelError, "only a portable"):
            model.portable_source_authority_binding_body(  # type: ignore[arg-type]
                local
            )
        with self.assertRaises(model.ModelError):
            copy.copy(local)
        with self.assertRaises(model.ModelError):
            copy.deepcopy(local)
        with self.assertRaises(model.ModelError):
            pickle.dumps(local)
        with self.assertRaises(TypeError):
            hash(local)


class AlgorithmIdentityAndAdmissionTest(unittest.TestCase):
    def test_term_node_and_depth_boundaries_are_exact(self) -> None:
        literal = model.Literal(value(model.UNIT_VALUE, model.UNIT))
        exact_nodes = model.SequenceConstruct(
            model.UNIT_VALUE,
            (literal,) * (model.MAX_TERM_NODES - 1),
            model.MAX_TERM_NODES - 1,
        )
        model.validate_term_structure(exact_nodes)
        with self.assertRaisesRegex(model.ModelError, "structural node bound"):
            model.validate_term_structure(
                model.SequenceConstruct(
                    model.UNIT_VALUE,
                    (literal,) * model.MAX_TERM_NODES,
                    model.MAX_TERM_NODES,
                )
            )

        exact_depth: model.Term = literal
        for _ in range(model.MAX_TERM_DEPTH):
            exact_depth = model.Let(literal, exact_depth)
        model.validate_term_structure(exact_depth)
        with self.assertRaisesRegex(model.ModelError, "structural depth bound"):
            model.validate_term_structure(model.Let(literal, exact_depth))

        invalid_child = model.Variable(-1, model.BYTES_32)
        with patch.object(model, "MAX_TERM_NODES", 2):
            with self.assertRaisesRegex(model.ModelError, "structural node bound"):
                model.validate_term_structure(model.Let(invalid_child, literal))

    def test_fixture_algorithms_pass_syntax_and_type_check(self) -> None:
        builders = (
            model.build_transcript_algorithm,
            model.build_rejection_find_algorithm,
            model.build_lossy_projection_algorithm,
            model.build_pairwise_hash_algorithm,
            model.build_mod_algorithm,
            model.build_unsupported_algorithm,
        )
        for builder in builders:
            with self.subTest(builder=builder.__name__):
                identifier = model.check_algorithm_syntax_and_types(builder())
                self.assertEqual(
                    identifier.subject_kind, "foundation.portable-algorithm"
                )

        missing_owner = module("fixture.syntax-check-is-not-admission").identity
        unresolved = model.CanonicalAlgorithm(
            model.Symbol("SyntaxCheckWithoutModuleAdmission"),
            (),
            model.Fail(
                model.SemanticFailureType(missing_owner, 0, model.UNIT_VALUE),
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                model.UNIT_VALUE,
            ),
        )
        model.check_algorithm_syntax_and_types(unresolved)
        result = model.Evaluator().evaluate(unresolved, ())
        self.assertEqual(result.outcome, model.Outcome.MISSING_DEPENDENCY)
        self.assertEqual(result.code, "K1-MISSING-MODULE")

    def test_function_output_and_failure_abi_are_derived_from_the_term(self) -> None:
        algorithm = model.build_mod_algorithm()
        function_type = algorithm.function_type
        self.assertEqual(function_type.inputs, (model.NAT_U64, model.NAT_U64))
        self.assertEqual(function_type.output, model.NAT_U64)
        self.assertEqual(function_type.failures, (model.ZERO_DIVISOR_FAILURE,))

        relabeled = replace(
            algorithm, diagnostic_label=model.Symbol("human-label-changed")
        )
        self.assertEqual(algorithm.identity, relabeled.identity)
        opaque_diagnostic = replace(algorithm, diagnostic_label=object())  # type: ignore[arg-type]
        self.assertEqual(algorithm.identity, opaque_diagnostic.identity)
        inputs = (
            value(model.NAT_U64, model.Nat(17)),
            value(model.NAT_U64, model.Nat(5)),
        )
        baseline = model.Evaluator().evaluate(
            algorithm,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        opaque = model.Evaluator().evaluate(
            opaque_diagnostic,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(baseline.outcome, model.Outcome.COMPLETED)
        self.assertEqual(opaque, baseline)

    def test_module_roots_are_derived_from_primitive_failure_and_value_types(
        self,
    ) -> None:
        primitive_algorithm = model.build_lossy_projection_algorithm()
        self.assertEqual(
            primitive_algorithm.module_dependencies,
            (model.FIXTURE_EXTENSION_MODULE_ID,),
        )
        missing_primitive_module = model.Evaluator().evaluate(
            primitive_algorithm,
            (value(model.BYTES_32, model.BytesValue(b"p" * 32)),),
        )
        self.assertEqual(
            missing_primitive_module.outcome, model.Outcome.MISSING_DEPENDENCY
        )

        failure_only = model.CanonicalAlgorithm(
            model.Symbol("FailureOnlyDependency"),
            (),
            model.Fail(
                model.ZERO_DIVISOR_FAILURE,
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                model.NAT_U64,
            ),
        )
        self.assertEqual(
            failure_only.module_dependencies,
            (model.FIXTURE_EXTENSION_MODULE_ID,),
        )
        failed = model.Evaluator().evaluate(
            failure_only,
            (),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(
            failed.completion,
            model.DomainFailure(
                model.ZERO_DIVISOR_FAILURE,
                value(model.UNIT_VALUE, model.UNIT),
            ),
        )

        declaration_module = module("fixture.value-type-owner")
        extension_domain = model.ValueDomain(
            declaration_module.identity,
            model.Symbol("value-domain"),
            7,
        )
        extension_type = model.ValueType(extension_domain, model.BytesSchema(1, 4))
        type_only = model.CanonicalAlgorithm(
            model.Symbol("TypeOnlyDependency"),
            (extension_type,),
            model.Variable(0, extension_type),
        )
        self.assertEqual(type_only.module_dependencies, (declaration_module.identity,))
        supplied = model.EncodedValue(
            extension_type,
            model.encode_datum(model.BytesValue(b"type")),
        )
        self.assertEqual(
            model.Evaluator().evaluate_encoded(type_only, (supplied,)).outcome,
            model.Outcome.MISSING_DEPENDENCY,
        )
        unsupported = model.Evaluator().evaluate_encoded(
            type_only,
            (supplied,),
            modules={declaration_module.identity: declaration_module},
        )
        self.assertEqual(unsupported.outcome, model.Outcome.UNSUPPORTED)
        self.assertEqual(unsupported.code, "K1-UNSUPPORTED-VALUE-DOMAIN")
        self.assertEqual(unsupported.charge, model.AbstractCharge())
        malformed_body = model.Evaluator().evaluate_encoded(
            type_only,
            (model.EncodedValue(extension_type, b"\xff"),),
            modules={declaration_module.identity: declaration_module},
        )
        self.assertEqual(malformed_body.outcome, model.Outcome.UNSUPPORTED)
        self.assertEqual(malformed_body.code, "K1-UNSUPPORTED-VALUE-DOMAIN")
        with self.assertRaises(model.UnsupportedValueDomainError):
            value(extension_type, model.BytesValue(b"type"))

        # The modulus call, its declared failure, and all root-owned value
        # types still induce the fixture extension exactly once.
        self.assertEqual(
            model.build_mod_algorithm().module_dependencies,
            (model.FIXTURE_EXTENSION_MODULE_ID,),
        )

    def test_literal_constitutional_canonicality_precedes_domain_support_but_schema_admission_follows(
        self,
    ) -> None:
        owner = module("fixture.unsupported-literal-domain")
        unsupported_type = model.ValueType(
            model.ValueDomain(
                owner.identity,
                model.Symbol("value-domain"),
                7,
            ),
            model.BytesSchema(1, 4),
        )
        malformed_literal = model.Literal(
            model.CanonicalValue(unsupported_type, model.Nat(0))
        )
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("UnsupportedDomainBeforeMalformedLiteral"),
            (),
            malformed_literal,
        )

        over_limit_algorithm = model.CanonicalAlgorithm(
            model.Symbol("ConstitutionalLiteralBeforeUnsupportedDomain"),
            (),
            model.Literal(
                model.CanonicalValue(
                    unsupported_type,
                    model.BytesValue(b"x" * (model.MAX_CANONICAL_BYTES + 1)),
                )
            ),
        )

        over_limit_result = model.Evaluator().evaluate(
            over_limit_algorithm,
            (),
            modules={owner.identity: owner},
        )
        self.assertEqual(over_limit_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(over_limit_result.code, "K1-MALFORMED-MODEL")
        self.assertEqual(over_limit_result.charge, model.AbstractCharge())

        result = model.Evaluator().evaluate(
            algorithm,
            (),
            modules={owner.identity: owner},
        )

        self.assertEqual(result.outcome, model.Outcome.UNSUPPORTED)
        self.assertEqual(result.code, "K1-UNSUPPORTED-VALUE-DOMAIN")
        self.assertEqual(result.charge, model.AbstractCharge())

        refused_literal = model.CanonicalAlgorithm(
            model.Symbol("SupportedDomainLiteralAdmissionRefusal"),
            (),
            model.Literal(
                model.CanonicalValue(model.BYTES_32, model.BytesValue(b"short"))
            ),
        )
        refused_result = model.Evaluator().evaluate(refused_literal, ())
        self.assertEqual(refused_result.outcome, model.Outcome.REFUSED)
        self.assertEqual(refused_result.code, "K1-REFUSED-LITERAL-ADMISSION")
        self.assertEqual(refused_result.charge, model.AbstractCharge())

    def test_value_domain_owner_must_resolve_an_exact_local_declaration(self) -> None:
        owner = module("fixture.missing-value-domain")
        supplied_modules = {owner.identity: owner}
        nonexistent_domain = model.ValueDomain(
            owner.identity,
            model.MODULE_VALUE_DOMAIN_KIND,
            999,
        )
        nonexistent_type = model.ValueType(
            nonexistent_domain, model.BytesSchema(32, 32)
        )
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("NonexistentDomainDeclaration"),
            (nonexistent_type,),
            model.Variable(0, nonexistent_type),
        )
        supplied = model.EncodedValue(
            nonexistent_type,
            model.encode_datum(model.BytesValue(b"x" * 32)),
        )
        self.assertEqual(
            model.authenticate_module_closure(
                algorithm.module_dependencies,
                supplied_modules,
                semantic_regime=model.SEMANTIC_REGIME_ID,
            ),
            model.AuthenticatedModuleClosure(1, 0),
        )
        with self.assertRaisesRegex(model.ModelError, "declaration ordinal is absent"):
            model.authenticate_algorithm_declaration_references(
                algorithm, supplied_modules
            )

        result = model.Evaluator().evaluate_encoded(
            algorithm,
            (supplied,),
            modules=supplied_modules,
        )
        self.assertEqual(result.outcome, model.Outcome.REFUSED)
        self.assertEqual(result.code, "K1-REFUSED-DECLARATION-ADMISSION")
        self.assertEqual(result.charge, model.AbstractCharge())

        absent_root_type = model.ValueType(
            model.ValueDomain(
                model.SEMANTIC_REGIME_ID,
                model.ROOT_VALUE_DOMAIN_KIND,
                999,
            ),
            model.UnitSchema(),
        )
        absent_root_result = model.Evaluator().evaluate(
            model.CanonicalAlgorithm(
                model.Symbol("AbsentRootDeclaration"),
                (absent_root_type,),
                model.Variable(0, absent_root_type),
            ),
            (),
        )
        self.assertEqual(absent_root_result.outcome, model.Outcome.REFUSED)
        self.assertEqual(
            absent_root_result.code,
            "K1-REFUSED-DECLARATION-ADMISSION",
        )

        wrong_root_schema = model.ValueType(
            model.ValueDomain(
                model.SEMANTIC_REGIME_ID,
                model.ROOT_VALUE_DOMAIN_KIND,
                0,
            ),
            model.BoolSchema(),
        )
        wrong_root_result = model.Evaluator().evaluate(
            model.CanonicalAlgorithm(
                model.Symbol("WrongRootDeclarationType"),
                (wrong_root_schema,),
                model.Variable(0, wrong_root_schema),
            ),
            (),
        )
        self.assertEqual(wrong_root_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(wrong_root_result.code, "K1-KIND-DECLARATION")

        malformed_catalog = model.DatumRecord(
            (
                (0, model.Symbol("value-domain")),
                (1, model.DatumSeq((model.UNIT,))),
            )
        )
        malformed_owner = replace(
            owner,
            local_declarations=model.DatumSeq(
                (owner.local_declarations.values[0], malformed_catalog)
            ),
        )
        malformed_type = model.ValueType(
            model.ValueDomain(
                malformed_owner.identity,
                model.MODULE_VALUE_DOMAIN_KIND,
                0,
            ),
            model.BytesSchema(32, 32),
        )
        malformed_algorithm = model.CanonicalAlgorithm(
            model.Symbol("MalformedValueDomainDeclaration"),
            (malformed_type,),
            model.Variable(0, malformed_type),
        )
        malformed_result = model.Evaluator().evaluate_encoded(
            malformed_algorithm,
            (
                model.EncodedValue(
                    malformed_type,
                    model.encode_datum(model.BytesValue(b"x" * 32)),
                ),
            ),
            modules={malformed_owner.identity: malformed_owner},
        )
        self.assertEqual(malformed_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(malformed_result.code, "K1-MALFORMED-DECLARATION")
        self.assertEqual(malformed_result.charge, model.AbstractCharge())

        absent_type = model.ValueType(
            model.ValueDomain(
                malformed_owner.identity,
                model.MODULE_VALUE_DOMAIN_KIND,
                999,
            ),
            model.BytesSchema(32, 32),
        )
        for ordered_inputs in (
            (malformed_type, absent_type),
            (absent_type, malformed_type),
        ):
            with self.subTest(
                absent_coordinate_position=ordered_inputs.index(absent_type)
            ):
                two_boundary_defects = model.CanonicalAlgorithm(
                    model.Symbol("ResolveAllDeclarationsBeforeInterpretation"),
                    ordered_inputs,
                    model.Variable(0, ordered_inputs[0]),
                )
                with self.assertRaisesRegex(
                    model.DeclarationAdmissionRefusedError,
                    "declaration ordinal is absent",
                ):
                    model.authenticate_algorithm_declaration_references(
                        two_boundary_defects,
                        {malformed_owner.identity: malformed_owner},
                    )
                precedence_result = model.Evaluator().evaluate(
                    two_boundary_defects,
                    (),
                    modules={malformed_owner.identity: malformed_owner},
                )
                self.assertEqual(precedence_result.outcome, model.Outcome.REFUSED)
                self.assertEqual(
                    precedence_result.code,
                    "K1-REFUSED-DECLARATION-ADMISSION",
                )

    def test_module_domain_shape_aliases_do_not_gain_root_eliminators(self) -> None:
        owner = module("fixture.opaque-shape-owner")

        def opaque(ordinal: int, schema: model.Schema) -> model.ValueType:
            return model.ValueType(
                model.ValueDomain(
                    owner.identity,
                    model.Symbol("value-domain"),
                    ordinal,
                ),
                schema,
            )

        opaque_record = opaque(0, model.RecordSchema(((0, model.BYTES_8),)))
        opaque_bool = opaque(1, model.BOOL_SCHEMA)
        opaque_sequence = opaque(2, model.SeqSchema(model.BYTES_8, 1))
        opaque_variant = opaque(3, model.VariantSchema(((0, model.UNIT_VALUE),)))
        unit_literal = model.Literal(value(model.UNIT_VALUE, model.UNIT))

        cases = (
            (
                model.CanonicalAlgorithm(
                    model.Symbol("OpaqueRecordProject"),
                    (opaque_record,),
                    model.Project(model.Variable(0, opaque_record), 0),
                ),
                model.EncodedValue(
                    opaque_record,
                    model.encode_datum(
                        model.DatumRecord(((0, model.BytesValue(b"x" * 8)),))
                    ),
                ),
                "root record",
            ),
            (
                model.CanonicalAlgorithm(
                    model.Symbol("OpaqueBooleanConditional"),
                    (opaque_bool,),
                    model.Conditional(
                        model.Variable(0, opaque_bool), unit_literal, unit_literal
                    ),
                ),
                model.EncodedValue(opaque_bool, model.encode_datum(False)),
                "root Boolean",
            ),
            (
                model.CanonicalAlgorithm(
                    model.Symbol("OpaqueSequenceLength"),
                    (opaque_sequence,),
                    model.SequenceLength(model.Variable(0, opaque_sequence)),
                ),
                model.EncodedValue(
                    opaque_sequence,
                    model.encode_datum(model.DatumSeq(())),
                ),
                "root sequence",
            ),
            (
                model.CanonicalAlgorithm(
                    model.Symbol("OpaqueVariantCase"),
                    (opaque_variant,),
                    model.Case(
                        model.Variable(0, opaque_variant),
                        ((0, model.Variable(0, model.UNIT_VALUE)),),
                    ),
                ),
                model.EncodedValue(
                    opaque_variant,
                    model.encode_datum(model.DatumVariant(0, model.UNIT)),
                ),
                "root tagged sum",
            ),
        )
        for algorithm, supplied, detail in cases:
            with self.subTest(detail=detail):
                result = model.Evaluator().evaluate_encoded(
                    algorithm,
                    (supplied,),
                    modules={owner.identity: owner},
                )
                self.assertEqual(result.outcome, model.Outcome.REFUSED)
                self.assertEqual(result.code, "K1-REFUSED-ALGORITHM-TYPING")
                self.assertIn(detail, result.detail)

        opaque_injection = model.CanonicalAlgorithm(
            model.Symbol("OpaqueVariantInject"),
            (),
            model.Inject(0, unit_literal, opaque_variant),
        )
        injected = model.Evaluator().evaluate(
            opaque_injection,
            (),
            modules={owner.identity: owner},
        )
        self.assertEqual(injected.outcome, model.Outcome.REFUSED)
        self.assertEqual(injected.code, "K1-REFUSED-ALGORITHM-TYPING")
        self.assertIn("root tagged sum", injected.detail)

    def test_exact_primitive_id_cannot_be_replaced_by_a_matching_name(self) -> None:
        exact = model.build_lossy_projection_algorithm()
        spoof_id = model.content_id(
            "foundation.semantic-primitive",
            model.encode_datum(model.Symbol("bytes.take")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        exact_ref = model.PRIMITIVE_REFS_BY_KEY[("bytes.take", 1)]
        spoof = model.SemanticPrimitiveRef(
            spoof_id,
            exact_ref.declaration_module,
            exact_ref.local_ordinal,
        )
        self.assertNotEqual(spoof.identifier, exact_ref.identifier)
        malformed = replace(
            exact,
            term=model.PrimitiveCall(
                spoof,
                (
                    model.Variable(0, model.BYTES_32),
                    model.Literal(value(model.NAT_U64, model.Nat(27))),
                ),
            ),
        )
        with self.assertRaisesRegex(
            model.CanonicalError, "semantic body does not authenticate"
        ):
            model.check_algorithm_syntax_and_types(malformed)
        result = model.Evaluator().evaluate(
            malformed,
            (value(model.BYTES_32, model.BytesValue(b"x" * 32)),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(result.outcome, model.Outcome.MALFORMED)

        wrong_identifier_kind = model.content_id(
            "foundation.portable-algorithm",
            model.encode_datum(model.Symbol("wrong-primitive-id-kind")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        wrong_identifier = replace(spoof, identifier=wrong_identifier_kind)
        wrong_identifier_algorithm = replace(
            exact,
            term=replace(exact.term, primitive=wrong_identifier),
        )
        wrong_identifier_result = model.Evaluator().evaluate(
            wrong_identifier_algorithm,
            (value(model.BYTES_32, model.BytesValue(b"x" * 32)),),
        )
        self.assertEqual(
            wrong_identifier_result.outcome,
            model.Outcome.KIND_MISMATCH,
        )
        self.assertEqual(
            wrong_identifier_result.code,
            "K1-KIND-DECLARATION",
        )

        wrong_owner_kind = model.content_id(
            "foundation.portable-algorithm",
            model.encode_datum(model.Symbol("wrong-primitive-owner-kind")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        wrong_owner_reference = replace(
            spoof,
            declaration_module=wrong_owner_kind,
        )
        wrong_owner_algorithm = replace(
            exact,
            term=replace(exact.term, primitive=wrong_owner_reference),
        )
        wrong_owner_result = model.Evaluator().evaluate(
            wrong_owner_algorithm,
            (value(model.BYTES_32, model.BytesValue(b"x" * 32)),),
        )
        self.assertEqual(wrong_owner_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(wrong_owner_result.code, "K1-KIND-DECLARATION")

    def test_primitive_reference_owner_and_ordinal_are_authenticated(self) -> None:
        algorithm = model.build_lossy_projection_algorithm()
        self.assertIsInstance(algorithm.term, model.PrimitiveCall)
        exact = model.PRIMITIVE_REFS_BY_KEY[("bytes.take", 1)]
        alternate_owner = module("fixture.alternate-primitive-owner").identity
        mismatches = (
            replace(exact, declaration_module=alternate_owner),
            replace(exact, local_ordinal=exact.local_ordinal + 1),
        )

        for mismatch in mismatches:
            with self.subTest(reference=mismatch):
                with self.assertRaisesRegex(
                    model.CanonicalError, "semantic body does not authenticate"
                ):
                    model.authenticate_primitive_reference(mismatch)
                malformed = replace(
                    algorithm,
                    term=replace(algorithm.term, primitive=mismatch),
                )
                self.assertIsInstance(malformed.identity, model.TypedContentId)
                result = model.Evaluator().evaluate(
                    malformed,
                    (value(model.BYTES_32, model.BytesValue(b"x" * 32)),),
                )
                self.assertEqual(result.outcome, model.Outcome.MALFORMED)
                self.assertEqual(result.code, "K1-MALFORMED-MODEL")

        # Exercise transaction grouping without claiming a real SHA-256
        # collision.  Both distinct canonical reference bodies authenticate
        # under the substituted digest, so the second observation must be a
        # checker failure before module resolution or term typing.
        colliding = replace(exact, local_ordinal=exact.local_ordinal + 1)
        collision_algorithm = model.CanonicalAlgorithm(
            model.Symbol("SyntheticPrimitiveReferenceCollision"),
            (),
            model.Let(
                model.PrimitiveCall(exact, ()),
                model.PrimitiveCall(colliding, ()),
            ),
        )
        real_content_id = model.content_id

        def synthetic_content_collision(
            subject_kind: str,
            body: bytes,
            **axes: object,
        ) -> model.TypedContentId:
            authenticated = real_content_id(  # type: ignore[arg-type]
                subject_kind,
                body,
                **axes,
            )
            if subject_kind == "foundation.semantic-primitive":
                return exact.identifier
            return authenticated

        with patch.object(
            model,
            "content_id",
            side_effect=synthetic_content_collision,
        ):
            collision_result = model.Evaluator().evaluate(
                collision_algorithm,
                (),
            )
        self.assertEqual(
            collision_result.outcome,
            model.Outcome.CHECKER_FAILURE,
        )
        self.assertEqual(
            collision_result.code,
            "FOUNDATION-HASH-BINDING-CONFLICT",
        )

    def test_primitive_sources_authenticate_or_rotate_the_full_identity_chain(
        self,
    ) -> None:
        key = ("bytes.take", 1)
        declaration = model.PRIMITIVE_DECLARATIONS_BY_KEY[key]
        original_entry = model.PRIMITIVE_CATALOG_BY_KEY[key]
        original_algorithm = model.build_lossy_projection_algorithm()
        self.assertIsInstance(original_algorithm.term, model.PrimitiveCall)

        for field in ("type_rule_source", "operation_law_source"):
            with self.subTest(runtime_field=field):
                forged = replace(
                    declaration,
                    **{field: getattr(declaration, field) + b"-forged"},
                )
                self.assertEqual(forged.owning_module, declaration.owning_module)
                self.assertEqual(forged.identifier, declaration.identifier)
                with self.assertRaisesRegex(
                    model.ModelError, "authenticated module entry"
                ):
                    model.authenticate_primitive_declaration(forged)

        wrong_kind_identifier = model.content_id(
            "foundation.not-a-semantic-primitive",
            model.encode_datum(model.primitive_reference_datum(original_entry)),
            semantic_regime=declaration.identifier.semantic_regime,
        )
        with self.assertRaisesRegex(model.ModelError, "wrong subject kind"):
            model.authenticate_primitive_declaration(
                replace(declaration, identifier=wrong_kind_identifier)
            )

        for source_index, field in (
            (3, "type-rule"),
            (4, "operation-law"),
        ):
            with self.subTest(rotated_field=field):
                changed_entry = (
                    *original_entry[:source_index],
                    original_entry[source_index] + b"-rotated",
                    *original_entry[source_index + 1 :],
                )
                changed_catalog = tuple(
                    changed_entry if entry == original_entry else entry
                    for entry in model.PRIMITIVE_SEMANTIC_CATALOG
                )
                local_declarations = model.DatumSeq(
                    (
                        model.DatumRecord(
                            (
                                (0, model.Symbol("semantic-failure")),
                                (1, model.FIXTURE_FAILURE_CATALOG),
                            )
                        ),
                        model.DatumRecord(
                            (
                                (0, model.Symbol("semantic-primitive")),
                                (1, model.primitive_catalog_datum(changed_catalog)),
                            )
                        ),
                    )
                )
                changed_module = model.SemanticModuleCandidate(
                    model.Symbol(f"fixture.{field}-rotated"),
                    (),
                    local_declarations,
                )
                changed_reference = primitive_reference(
                    changed_module.identity, original_entry[0]
                )
                model.authenticate_primitive_reference(changed_reference)
                closure = model.authenticate_module_closure(
                    (changed_module.identity,),
                    {changed_module.identity: changed_module},
                    semantic_regime=model.SEMANTIC_REGIME_ID,
                )
                self.assertEqual(closure, model.AuthenticatedModuleClosure(1, 0))

                changed_algorithm = replace(
                    original_algorithm,
                    term=replace(
                        original_algorithm.term,
                        primitive=changed_reference,
                    ),
                )
                self.assertNotEqual(
                    changed_module.identity, model.FIXTURE_EXTENSION_MODULE_ID
                )
                self.assertNotEqual(
                    changed_reference.identifier,
                    model.PRIMITIVE_REFS_BY_KEY[key].identifier,
                )
                self.assertNotEqual(
                    changed_algorithm.identity, original_algorithm.identity
                )
                self.assertEqual(
                    changed_algorithm.module_dependencies,
                    (changed_module.identity,),
                )
                with self.assertRaisesRegex(model.ModelError, "semantic registry"):
                    model.check_algorithm_syntax_and_types(changed_algorithm)

        primitive_body = model.primitive_catalog_datum().values[0]

        def primitive_module(
            name: str,
            primitive_declaration: model.Datum,
            failures: tuple[model.Datum, ...] = (),
        ) -> model.SemanticModuleCandidate:
            catalogs: list[model.Datum] = []
            if failures:
                catalogs.append(
                    model.DatumRecord(
                        (
                            (0, model.Symbol("semantic-failure")),
                            (1, model.DatumSeq(failures)),
                        )
                    )
                )
            catalogs.append(
                model.DatumRecord(
                    (
                        (0, model.Symbol("semantic-primitive")),
                        (1, model.DatumSeq((primitive_declaration,))),
                    )
                )
            )
            return model.SemanticModuleCandidate(
                model.Symbol(name),
                (),
                model.DatumSeq(tuple(catalogs)),
            )

        cases: tuple[
            tuple[str, model.SemanticModuleCandidate, model.Outcome, str], ...
        ] = (
            (
                "malformed-body",
                primitive_module("fixture.malformed-primitive-body", model.UNIT),
                model.Outcome.MALFORMED,
                "K1-MALFORMED-DECLARATION",
            ),
            (
                "valid-unsupported-body",
                primitive_module("fixture.valid-unknown-primitive", primitive_body),
                model.Outcome.UNSUPPORTED,
                "K1-UNSUPPORTED-PRIMITIVE-DECLARATION",
            ),
        )
        for label, candidate, outcome, code in cases:
            with self.subTest(primitive_body=label):
                reference = primitive_reference(candidate.identity, 0)
                changed_algorithm = replace(
                    original_algorithm,
                    term=replace(original_algorithm.term, primitive=reference),
                )
                result = model.Evaluator().evaluate(
                    changed_algorithm,
                    (value(model.BYTES_32, model.BytesValue(b"b" * 32)),),
                    modules={candidate.identity: candidate},
                )
                self.assertEqual(result.outcome, outcome)
                self.assertEqual(result.code, code)
                self.assertEqual(result.charge, model.AbstractCharge())

        primitive_fields = dict(primitive_body.fields)

        def failure_reference(ordinal: int) -> model.DatumRecord:
            return model.DatumRecord(
                (
                    (0, model.Symbol("semantic-failure")),
                    (1, model.Nat(ordinal)),
                )
            )

        def with_failure_references(
            declaration_body: model.DatumRecord,
            references: tuple[model.Datum, ...],
        ) -> model.DatumRecord:
            return replace(
                declaration_body,
                fields=tuple(
                    (ordinal, value)
                    if ordinal != 4
                    else (4, model.DatumSeq(references))
                    for ordinal, value in declaration_body.fields
                ),
            )

        primitive_with_missing_failure = model.DatumRecord(
            tuple(
                (ordinal, value)
                if ordinal != 4
                else (
                    4,
                    model.DatumSeq(
                        (
                            model.DatumRecord(
                                (
                                    (0, model.Symbol("semantic-failure")),
                                    (1, model.Nat(999)),
                                )
                            ),
                        )
                    ),
                )
                for ordinal, value in primitive_body.fields
            )
        )
        self.assertEqual(primitive_fields[4], model.DatumSeq(()))
        missing_failure_owner = primitive_module(
            "fixture.primitive-missing-failure",
            primitive_with_missing_failure,
        )
        missing_failure_ref = primitive_reference(missing_failure_owner.identity, 0)
        missing_failure_result = model.Evaluator().evaluate(
            replace(
                original_algorithm,
                term=replace(
                    original_algorithm.term,
                    primitive=missing_failure_ref,
                ),
            ),
            (value(model.BYTES_32, model.BytesValue(b"f" * 32)),),
            modules={missing_failure_owner.identity: missing_failure_owner},
        )
        self.assertEqual(missing_failure_result.outcome, model.Outcome.REFUSED)
        self.assertEqual(
            missing_failure_result.code,
            "K1-REFUSED-DECLARATION-ADMISSION",
        )

        malformed_failure_owner = primitive_module(
            "fixture.primitive-malformed-failure",
            replace(
                primitive_with_missing_failure,
                fields=tuple(
                    (ordinal, value)
                    if ordinal != 4
                    else (
                        4,
                        model.DatumSeq(
                            (
                                model.DatumRecord(
                                    (
                                        (0, model.Symbol("semantic-failure")),
                                        (1, model.Nat(0)),
                                    )
                                ),
                            )
                        ),
                    )
                    for ordinal, value in primitive_with_missing_failure.fields
                ),
            ),
            (model.UNIT,),
        )
        malformed_failure_ref = primitive_reference(
            malformed_failure_owner.identity,
            0,
        )
        malformed_failure_result = model.Evaluator().evaluate(
            replace(
                original_algorithm,
                term=replace(
                    original_algorithm.term,
                    primitive=malformed_failure_ref,
                ),
            ),
            (value(model.BYTES_32, model.BytesValue(b"g" * 32)),),
            modules={malformed_failure_owner.identity: malformed_failure_owner},
        )
        self.assertEqual(malformed_failure_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            malformed_failure_result.code,
            "K1-MALFORMED-DECLARATION",
        )

        for position, references in enumerate(
            (
                (model.UNIT, failure_reference(999)),
                (failure_reference(999), model.UNIT),
            )
        ):
            with self.subTest(
                complete_primitive_reference_formation=position,
            ):
                candidate = primitive_module(
                    f"fixture.primitive-malformed-ref-{position}",
                    with_failure_references(primitive_body, references),
                )
                reference = primitive_reference(candidate.identity, 0)
                result = model.Evaluator().evaluate(
                    replace(
                        original_algorithm,
                        term=replace(original_algorithm.term, primitive=reference),
                    ),
                    (value(model.BYTES_32, model.BytesValue(b"h" * 32)),),
                    modules={candidate.identity: candidate},
                )
                self.assertEqual(result.outcome, model.Outcome.MALFORMED)
                self.assertEqual(result.code, "K1-MALFORMED-DECLARATION")
                self.assertEqual(result.charge, model.AbstractCharge())

        for position, references in enumerate(
            (
                (failure_reference(0), failure_reference(999)),
                (failure_reference(999), failure_reference(0)),
            )
        ):
            with self.subTest(
                complete_primitive_coordinate_resolution=position,
            ):
                candidate = primitive_module(
                    f"fixture.primitive-refused-before-target-{position}",
                    with_failure_references(primitive_body, references),
                    (model.UNIT,),
                )
                reference = primitive_reference(candidate.identity, 0)
                result = model.Evaluator().evaluate(
                    replace(
                        original_algorithm,
                        term=replace(original_algorithm.term, primitive=reference),
                    ),
                    (value(model.BYTES_32, model.BytesValue(b"i" * 32)),),
                    modules={candidate.identity: candidate},
                )
                self.assertEqual(result.outcome, model.Outcome.REFUSED)
                self.assertEqual(
                    result.code,
                    "K1-REFUSED-DECLARATION-ADMISSION",
                )
                self.assertEqual(result.charge, model.AbstractCharge())

    def test_provider_rebinding_does_not_change_operation_contract_identity(
        self,
    ) -> None:
        contract = model.ExternalOperationContract(
            model.Symbol("RemoteHashService"),
            model.SemanticFunctionType((model.BYTES_0_32,), model.BYTES_32),
        )
        left = model.ExternalOperationBinding(contract, model.Symbol("provider-a"))
        right = model.ExternalOperationBinding(contract, model.Symbol("provider-b"))
        self.assertEqual(left.contract.identity, right.contract.identity)

        evaluator = model.Evaluator()
        for subject in (contract, left, right):
            result = evaluator.evaluate(subject, ())
            self.assertEqual(result.outcome, model.Outcome.KIND_MISMATCH)
            self.assertEqual(result.code, "K1-KIND-SUBJECT")
            self.assertEqual(result.charge, model.AbstractCharge())
            self.assertIsNone(result.completion)

        malformed_binding = model.ExternalOperationBinding(  # type: ignore[arg-type]
            object(),
            object(),
        )
        malformed_result = evaluator.evaluate(malformed_binding, ())
        self.assertEqual(malformed_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            malformed_result.code,
            "K1-MALFORMED-SUBJECT-CARRIER",
        )
        self.assertEqual(malformed_result.charge, model.AbstractCharge())
        self.assertIsNone(malformed_result.completion)

        with self.assertRaisesRegex(
            model.ModelError, "inputs must use an immutable tuple"
        ):
            model.SemanticFunctionType(  # type: ignore[arg-type]
                [model.BYTES_0_32],
                model.BYTES_32,
            )

    def test_algorithm_identity_refuses_mutable_input_headers(self) -> None:
        mutable_inputs = [model.BYTES_0_32]
        algorithm = model.CanonicalAlgorithm(  # type: ignore[arg-type]
            model.Symbol("MutableInputHeader"),
            mutable_inputs,
            model.Variable(0, model.BYTES_0_32),
        )
        with self.assertRaisesRegex(model.ModelError, "immutable value-type sequence"):
            _ = algorithm.identity
        with self.assertRaisesRegex(model.ModelError, "immutable value-type sequence"):
            _ = algorithm.function_type
        with self.assertRaisesRegex(model.ModelError, "immutable value-type sequence"):
            _ = algorithm.module_dependencies
        mutable_inputs.append(model.BYTES_32)
        with self.assertRaisesRegex(model.ModelError, "immutable value-type sequence"):
            _ = algorithm.identity

    def test_ill_typed_term_is_refused_before_input_arity(self) -> None:
        good = model.build_lossy_projection_algorithm()
        ill_typed = replace(good, term=model.Variable(0, model.NAT_U64))
        result = model.Evaluator().evaluate(ill_typed, ())
        self.assertEqual(result.outcome, model.Outcome.REFUSED)
        self.assertEqual(result.code, "K1-REFUSED-ALGORITHM-TYPING")

    def test_algorithm_kind_must_be_an_exact_symbol_before_input_arity(self) -> None:
        good = model.build_lossy_projection_algorithm()
        malformed = replace(good, algorithm_kind=model.Nat(0))
        result = model.Evaluator().evaluate(malformed, ())
        self.assertEqual(result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(result.code, "K1-MALFORMED-MODEL")
        self.assertIn("algorithm kind must be an exact symbol", result.detail)


class ExactFixtureExecutionTest(unittest.TestCase):
    def setUp(self) -> None:
        self.evaluator = model.Evaluator()

    def test_transcript_state_passing_fold_matches_direct_hash_chain(self) -> None:
        algorithm = model.build_transcript_algorithm()
        state = bytes(range(32))
        messages = (b"statement", b"commitment", b"query")
        message_type = algorithm.function_type.inputs[1]
        result = self.evaluator.evaluate(
            algorithm,
            (
                value(model.BYTES_32, model.BytesValue(state)),
                value(
                    message_type,
                    model.DatumSeq(tuple(model.BytesValue(item) for item in messages)),
                ),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        expected = state
        for message in messages:
            expected = hashlib.sha256(expected + message).digest()
        self.assertEqual(success(result).datum, model.BytesValue(expected))

    def test_transcript_runtime_message_and_order_changes_preserve_algorithm_id(
        self,
    ) -> None:
        algorithm = model.build_transcript_algorithm()
        identity = algorithm.identity
        initial_state = b"t" * 32
        message_type = algorithm.function_type.inputs[1]

        def run(messages: tuple[bytes, ...]) -> model.EvaluationResult:
            result = self.evaluator.evaluate(
                algorithm,
                (
                    value(model.BYTES_32, model.BytesValue(initial_state)),
                    value(
                        message_type,
                        model.DatumSeq(
                            tuple(model.BytesValue(item) for item in messages)
                        ),
                    ),
                ),
                modules=model.FIXTURE_MODULE_PREIMAGES,
            )
            self.assertEqual(algorithm.identity, identity)
            expected = initial_state
            for message in messages:
                expected = hashlib.sha256(expected + message).digest()
            self.assertEqual(success(result).datum, model.BytesValue(expected))
            return result

        baseline_result = run((b"a", b"bc"))
        reframed_result = run((b"ab", b"c"))
        reordered_result = run((b"bc", b"a"))
        baseline = success(baseline_result)
        changed = success(reframed_result)
        reordered = success(reordered_result)
        self.assertNotEqual(baseline, reordered)
        self.assertNotEqual(baseline, changed)
        self.assertNotEqual(reordered, changed)
        self.assertEqual(baseline_result.charge, reframed_result.charge)
        self.assertEqual(baseline_result.charge, reordered_result.charge)

    def test_bounded_rejection_find_returns_first_acceptable_candidate(self) -> None:
        algorithm = model.build_rejection_find_algorithm()
        seed = bytes(reversed(range(32)))
        retry_count = 12
        limit = 1 << 63
        result = self.evaluator.evaluate(
            algorithm,
            (
                value(model.BYTES_32, model.BytesValue(seed)),
                value(model.NAT_16, model.Nat(retry_count)),
                value(model.NAT_U64, model.Nat(limit)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        candidates = tuple(
            hashlib.sha256(seed + counter.to_bytes(8, "big")).digest()
            for counter in range(retry_count)
        )
        expected = next(
            item for item in candidates if int.from_bytes(item[:8], "big") < limit
        )
        self.assertEqual(
            success(result).datum,
            model.DatumVariant(1, model.BytesValue(expected)),
        )

    def test_bounded_rejection_find_has_explicit_exhaustion_value(self) -> None:
        result = self.evaluator.evaluate(
            model.build_rejection_find_algorithm(),
            (
                value(model.BYTES_32, model.BytesValue(b"s" * 32)),
                value(model.NAT_16, model.Nat(4)),
                value(model.NAT_U64, model.Nat(0)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(success(result).datum, model.DatumVariant(0, model.UNIT))

    def test_nested_sampler_multiple_draws_match_direct_retry_calculation(
        self,
    ) -> None:
        algorithm = model.build_nested_sampler_algorithm()
        seed = b"\x00" * 32
        draw_count = 3
        retry_count = 4
        limit = 7_568_850_110_727_146_249

        expected: list[bytes] = []
        attempts = 0
        for draw_index in range(draw_count):
            for retry_index in range(retry_count):
                attempts += 1
                candidate = hashlib.sha256(
                    seed
                    + draw_index.to_bytes(8, "big")
                    + retry_index.to_bytes(8, "big")
                ).digest()
                if int.from_bytes(candidate[:8], "big") < limit:
                    expected.append(candidate)
                    break
            else:  # pragma: no cover - the constants above falsify this branch
                self.fail(f"draw {draw_index} unexpectedly exhausted")

        result = self.evaluator.evaluate(
            algorithm,
            (
                value(model.BYTES_32, model.BytesValue(seed)),
                value(model.NAT_16, model.Nat(draw_count)),
                value(model.NAT_16, model.Nat(retry_count)),
                value(model.NAT_U64, model.Nat(limit)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(
            success(result).datum,
            model.DatumSeq(tuple(model.BytesValue(item) for item in expected)),
        )
        self.assertEqual(result.charge.iteration_items, draw_count + attempts)

    def test_nested_sampler_exhaustion_is_typed_and_iteration_limit_is_exact(
        self,
    ) -> None:
        algorithm = model.build_nested_sampler_algorithm()
        inputs = (
            value(model.BYTES_32, model.BytesValue(b"e" * 32)),
            value(model.NAT_16, model.Nat(1)),
            value(model.NAT_16, model.Nat(4)),
            value(model.NAT_U64, model.Nat(0)),
        )
        expected_failure = model.DomainFailure(
            model.SAMPLING_EXHAUSTED_FAILURE,
            value(model.NAT_INDEX_16, model.Nat(0)),
        )
        exact_limits = replace(model.DEFAULT_LIMITS, maximum_iteration_items=5)
        exact = self.evaluator.evaluate(
            algorithm,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
            limits=exact_limits,
        )
        self.assertEqual(exact.outcome, model.Outcome.COMPLETED)
        self.assertEqual(exact.completion, expected_failure)
        self.assertEqual(exact.charge.iteration_items, 5)

        one_less = self.evaluator.evaluate(
            algorithm,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
            limits=replace(exact_limits, maximum_iteration_items=4),
        )
        self.assertEqual(one_less.outcome, model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED)
        self.assertEqual(one_less.code, "K1-LIMIT-EVALUATION")
        self.assertEqual(one_less.charge.iteration_items, 4)

    def test_merkle_path_state_fold_is_explicit_and_bounded(self) -> None:
        algorithm = model.build_pairwise_hash_algorithm()
        leaf = b"l" * 32
        siblings = (b"a" * 32, b"b" * 32, b"c" * 32)
        result = self.evaluator.evaluate(
            algorithm,
            (
                value(model.BYTES_32, model.BytesValue(leaf)),
                value(
                    algorithm.function_type.inputs[1],
                    model.DatumSeq(tuple(model.BytesValue(item) for item in siblings)),
                ),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        expected = leaf
        for sibling in siblings:
            expected = hashlib.sha256(expected + sibling).digest()
        self.assertEqual(success(result).datum, model.BytesValue(expected))

    def test_strict_paired_fold_covers_alignment_and_both_mismatch_directions(
        self,
    ) -> None:
        algorithm = model.build_strict_paired_fold_algorithm()
        left_type, right_type = algorithm.function_type.inputs

        def supplied(
            left: tuple[bytes, ...], right: tuple[bytes, ...]
        ) -> tuple[model.CanonicalValue, model.CanonicalValue]:
            return (
                value(
                    left_type,
                    model.DatumSeq(tuple(model.BytesValue(item) for item in left)),
                ),
                value(
                    right_type,
                    model.DatumSeq(tuple(model.BytesValue(item) for item in right)),
                ),
            )

        left = (b"a" * 32, b"b" * 32)
        right = (b"1" * 8, b"2" * 8)
        aligned = self.evaluator.evaluate(
            algorithm,
            supplied(left, right),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        expected_type = model.ValueType(
            model.SEQUENCE_DOMAIN,
            model.SeqSchema(
                model.ValueType(
                    model.RECORD_DOMAIN,
                    model.RecordSchema(((0, model.BYTES_32), (1, model.BYTES_8))),
                ),
                4,
            ),
        )
        self.assertEqual(algorithm.function_type.output, expected_type)
        self.assertEqual(
            success(aligned).datum,
            model.DatumSeq(
                tuple(
                    model.DatumRecord(
                        ((0, model.BytesValue(a)), (1, model.BytesValue(b)))
                    )
                    for a, b in zip(left, right)
                )
            ),
        )

        right_shorter = self.evaluator.evaluate(
            algorithm,
            supplied(left, right[:1]),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(
            right_shorter.completion,
            model.DomainFailure(
                model.INDEX_OUT_OF_RANGE_FAILURE,
                value(model.NAT_U64, model.Nat(1)),
            ),
        )

        right_longer = self.evaluator.evaluate(
            algorithm,
            supplied(left[:1], right),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(
            right_longer.completion,
            model.DomainFailure(
                model.INDEX_OUT_OF_RANGE_FAILURE,
                value(model.NAT_U64, model.Nat(1)),
            ),
        )

        both_empty = self.evaluator.evaluate(
            algorithm,
            supplied((), ()),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(success(both_empty).datum, model.DatumSeq(()))

    def test_oriented_path_runtime_bits_and_law_mutations_are_separate(
        self,
    ) -> None:
        normal = model.build_oriented_path_algorithm()
        reversed_law = model.build_oriented_path_algorithm(reverse_orientation_law=True)
        other_prefix = model.build_oriented_path_algorithm(domain_prefix=b"\x02")
        leaf = b"l" * 32
        sibling = b"s" * 32
        path_type = normal.function_type.inputs[1]

        def run(
            algorithm: model.CanonicalAlgorithm, sibling_left: bool
        ) -> model.CanonicalValue:
            path = model.DatumSeq(
                (
                    model.DatumRecord(
                        (
                            (0, model.BytesValue(sibling)),
                            (1, sibling_left),
                        )
                    ),
                )
            )
            return success(
                self.evaluator.evaluate(
                    algorithm,
                    (
                        value(model.BYTES_32, model.BytesValue(leaf)),
                        value(path_type, path),
                    ),
                    modules=model.FIXTURE_MODULE_PREIMAGES,
                )
            )

        left_result = run(normal, True)
        right_result = run(normal, False)
        self.assertEqual(
            normal.identity, model.build_oriented_path_algorithm().identity
        )
        self.assertNotEqual(left_result, right_result)
        self.assertEqual(
            left_result.datum,
            model.BytesValue(hashlib.sha256(b"\x01" + sibling + leaf).digest()),
        )
        self.assertEqual(
            right_result.datum,
            model.BytesValue(hashlib.sha256(b"\x01" + leaf + sibling).digest()),
        )

        self.assertNotEqual(normal.identity, reversed_law.identity)
        self.assertEqual(run(reversed_law, True), right_result)
        self.assertEqual(run(reversed_law, False), left_result)

        self.assertNotEqual(normal.identity, other_prefix.identity)
        prefixed_result = run(other_prefix, True)
        self.assertEqual(
            prefixed_result.datum,
            model.BytesValue(hashlib.sha256(b"\x02" + sibling + leaf).digest()),
        )
        self.assertNotEqual(prefixed_result, left_result)

    def test_lossy_projection_is_explicit_and_exact(self) -> None:
        source = bytes(range(32))
        result = self.evaluator.evaluate(
            model.build_lossy_projection_algorithm(),
            (value(model.BYTES_32, model.BytesValue(source)),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        projected = success(result)
        self.assertEqual(projected.datum, model.BytesValue(source[:27]))
        self.assertNotEqual(
            projected.bytes(),
            value(model.BYTES_32, model.BytesValue(source)).bytes(),
        )

    def test_lossy_projection_has_an_explicit_collision_and_exact_output_type(
        self,
    ) -> None:
        algorithm = model.build_lossy_projection_algorithm()
        expected_output = model.BYTES_27
        self.assertEqual(algorithm.function_type.output, expected_output)

        shared_prefix = bytes(range(27))
        left_input = value(model.BYTES_32, model.BytesValue(shared_prefix + b"left!"))
        right_input = value(model.BYTES_32, model.BytesValue(shared_prefix + b"right"))
        self.assertNotEqual(left_input, right_input)
        left = success(
            self.evaluator.evaluate(
                algorithm,
                (left_input,),
                modules=model.FIXTURE_MODULE_PREIMAGES,
            )
        )
        right = success(
            self.evaluator.evaluate(
                algorithm,
                (right_input,),
                modules=model.FIXTURE_MODULE_PREIMAGES,
            )
        )
        self.assertEqual(left.value_type, expected_output)
        self.assertEqual(left, right)
        self.assertEqual(left.datum, model.BytesValue(shared_prefix))

    def test_modulus_partiality_is_a_typed_completed_failure(self) -> None:
        algorithm = model.build_mod_algorithm()
        failed = self.evaluator.evaluate(
            algorithm,
            (
                value(model.NAT_U64, model.Nat(5)),
                value(model.NAT_U64, model.Nat(0)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(failed.outcome, model.Outcome.COMPLETED)
        self.assertEqual(
            failed.completion,
            model.DomainFailure(
                model.ZERO_DIVISOR_FAILURE,
                value(model.ZERO_DIVISOR_FAILURE.payload_type, model.UNIT),
            ),
        )
        self.assertEqual(
            failed.charge.result_bytes,
            len(
                model.encode_datum(
                    model.completion_datum(algorithm.function_type, failed.completion)
                )
            ),
        )

        completed = self.evaluator.evaluate(
            algorithm,
            (
                value(model.NAT_U64, model.Nat(17)),
                value(model.NAT_U64, model.Nat(5)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(success(completed).datum, model.Nat(2))
        assert completed.completion is not None
        self.assertEqual(
            completed.charge.result_bytes,
            len(
                model.encode_datum(
                    model.completion_datum(
                        algorithm.function_type,
                        completed.completion,
                    )
                )
            ),
        )

    def test_unsupported_primitive_is_admitted_but_not_executed(self) -> None:
        algorithm = model.build_unsupported_algorithm()
        model.check_algorithm_syntax_and_types(algorithm)
        result = self.evaluator.evaluate(
            algorithm,
            (value(model.BYTES_0_32, model.BytesValue(b"abc")),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(result.outcome, model.Outcome.UNSUPPORTED)

    def test_nested_bounded_iterators_preserve_outer_bindings(self) -> None:
        iteration_type = model.iteration_result_type(model.BYTES_32, model.BYTES_32)
        counter = primitive("u64.to-be", model.Variable(1, model.NAT_INDEX_16))
        step = primitive(
            "sha2-256",
            primitive(
                "bytes.concat",
                model.Variable(2, model.BYTES_32),
                counter,
            ),
        )
        inner = model.BoundedIterate(
            model.RangeIterationSource(model.Variable(5, model.NAT_16)),
            model.Variable(2, model.BYTES_32),
            model.Inject(0, step, iteration_type),
        )
        outer_body = model.Case(
            inner,
            (
                (
                    0,
                    model.Inject(0, model.Variable(0, model.BYTES_32), iteration_type),
                ),
                (
                    1,
                    model.Inject(0, model.Variable(0, model.BYTES_32), iteration_type),
                ),
            ),
        )
        outer = model.BoundedIterate(
            model.RangeIterationSource(model.Variable(1, model.NAT_16)),
            model.Variable(0, model.BYTES_32),
            outer_body,
        )
        term = model.Case(
            outer,
            (
                (0, model.Variable(0, model.BYTES_32)),
                (1, model.Variable(0, model.BYTES_32)),
            ),
        )
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("NestedBoundedIteration"),
            (model.BYTES_32, model.NAT_16, model.NAT_16),
            term,
        )

        seed = b"n" * 32
        outer_count = 2
        inner_count = 3
        result = self.evaluator.evaluate(
            algorithm,
            (
                value(model.BYTES_32, model.BytesValue(seed)),
                value(model.NAT_16, model.Nat(outer_count)),
                value(model.NAT_16, model.Nat(inner_count)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        expected = seed
        for _ in range(outer_count):
            for counter_value in range(inner_count):
                expected = hashlib.sha256(
                    expected + counter_value.to_bytes(8, "big")
                ).digest()
        self.assertEqual(success(result).datum, model.BytesValue(expected))
        self.assertEqual(
            result.charge.iteration_items,
            outer_count + outer_count * inner_count,
        )

    def test_bounded_iterator_source_precedes_initial_state(self) -> None:
        iteration_type = model.iteration_result_type(
            model.UNIT_VALUE,
            model.UNIT_VALUE,
        )
        source = model.Fail(
            model.ZERO_DIVISOR_FAILURE,
            model.Literal(value(model.UNIT_VALUE, model.UNIT)),
            model.NAT_16,
        )
        initial = model.Fail(
            model.SEQUENCE_CAPACITY_FAILURE,
            model.Literal(value(model.UNIT_VALUE, model.UNIT)),
            model.UNIT_VALUE,
        )
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("IteratorSourcePrecedence"),
            (),
            model.BoundedIterate(
                model.RangeIterationSource(source),
                initial,
                model.Inject(
                    0,
                    model.Variable(2, model.UNIT_VALUE),
                    iteration_type,
                ),
            ),
        )
        result = model.Evaluator().evaluate(
            algorithm,
            (),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(result.outcome, model.Outcome.COMPLETED)
        self.assertIsInstance(result.completion, model.DomainFailure)
        assert isinstance(result.completion, model.DomainFailure)
        self.assertEqual(
            result.completion.failure_type,
            model.ZERO_DIVISOR_FAILURE,
        )

    def test_range_iteration_is_lazy_across_an_immediate_break(self) -> None:
        iteration_type = model.iteration_result_type(model.UNIT_VALUE, model.UNIT_VALUE)
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("LazyImmediateBreak"),
            (model.NAT_16,),
            model.BoundedIterate(
                model.RangeIterationSource(model.Variable(0, model.NAT_16)),
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                model.Inject(
                    1,
                    model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                    iteration_type,
                ),
            ),
        )
        pulled: list[int] = []
        builtin_range = range

        def observed_range(stop: int) -> object:
            if stop != 16:
                return builtin_range(stop)

            def observed_items() -> object:
                for index in builtin_range(stop):
                    pulled.append(index)
                    if len(pulled) > 1:
                        raise AssertionError("range was materialized past early break")
                    yield index

            return observed_items()

        with patch.object(model, "range", observed_range, create=True):
            result = model.Evaluator().evaluate(
                algorithm, (value(model.NAT_16, model.Nat(16)),)
            )
        self.assertEqual(success(result).datum, model.DatumVariant(1, model.UNIT))
        self.assertEqual(pulled, [0])


class SequenceCapacityTest(unittest.TestCase):
    def test_spare_capacity_is_typed_and_append_exhaustion_is_semantic(self) -> None:
        first_value = model.Literal(value(model.BYTES_32, model.BytesValue(b"a" * 32)))
        second_value = model.Literal(value(model.BYTES_32, model.BytesValue(b"b" * 32)))
        third_value = model.Literal(value(model.BYTES_32, model.BytesValue(b"c" * 32)))
        empty = model.SequenceConstruct(model.BYTES_32, (), 2)
        once = model.BoundedAppend(empty, first_value, model.SEQUENCE_CAPACITY_FAILURE)
        twice = model.BoundedAppend(once, second_value, model.SEQUENCE_CAPACITY_FAILURE)
        three_times = model.BoundedAppend(
            twice, third_value, model.SEQUENCE_CAPACITY_FAILURE
        )
        output_type = model.ValueType(
            model.SEQUENCE_DOMAIN, model.SeqSchema(model.BYTES_32, 2)
        )

        successful = model.CanonicalAlgorithm(
            model.Symbol("AppendWithinSpareCapacity"), (), twice
        )
        self.assertEqual(successful.function_type.output, output_type)
        self.assertEqual(
            successful.function_type.failures,
            (model.SEQUENCE_CAPACITY_FAILURE,),
        )
        completed = model.Evaluator().evaluate(
            successful,
            (),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(
            success(completed).datum,
            model.DatumSeq((model.BytesValue(b"a" * 32), model.BytesValue(b"b" * 32))),
        )

        exhausted = model.Evaluator().evaluate(
            model.CanonicalAlgorithm(
                model.Symbol("AppendPastSpareCapacity"), (), three_times
            ),
            (),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(exhausted.outcome, model.Outcome.COMPLETED)
        self.assertEqual(
            exhausted.completion,
            model.DomainFailure(
                model.SEQUENCE_CAPACITY_FAILURE,
                value(model.UNIT_VALUE, model.UNIT),
            ),
        )

    def test_capacity_is_authenticated_and_invalid_capacity_refuses(self) -> None:
        capacity_one = model.CanonicalAlgorithm(
            model.Symbol("CapacityIdentity"),
            (),
            model.SequenceConstruct(model.BYTES_32, (), 1),
        )
        capacity_two = replace(
            capacity_one,
            term=model.SequenceConstruct(model.BYTES_32, (), 2),
        )
        self.assertNotEqual(capacity_one.identity, capacity_two.identity)

        element = model.Literal(value(model.BYTES_32, model.BytesValue(b"x" * 32)))
        for invalid in (-1, True, 0, model.MAX_CANONICAL_NODES + 1):
            with self.subTest(capacity=invalid):
                malformed = model.CanonicalAlgorithm(
                    model.Symbol("InvalidSequenceCapacity"),
                    (),
                    model.SequenceConstruct(model.BYTES_32, (element,), invalid),
                )
                with self.assertRaises((model.CanonicalError, model.ModelError)):
                    model.check_algorithm_syntax_and_types(malformed)


class HeterogeneousStructureTest(unittest.TestCase):
    def test_record_construct_and_projection_preserve_exact_field_types(self) -> None:
        record_term = model.RecordConstruct(
            (
                (0, model.Variable(0, model.NAT_U64)),
                (1, model.Variable(1, model.BYTES_32)),
                (2, model.Variable(2, model.BOOL)),
            )
        )
        record_type = model.ValueType(
            model.RECORD_DOMAIN,
            model.RecordSchema(
                (
                    (0, model.NAT_U64),
                    (1, model.BYTES_32),
                    (2, model.BOOL),
                )
            ),
        )
        inputs = (
            value(model.NAT_U64, model.Nat(9)),
            value(model.BYTES_32, model.BytesValue(b"r" * 32)),
            value(model.BOOL, True),
        )
        record_algorithm = model.CanonicalAlgorithm(
            model.Symbol("HeterogeneousRecord"),
            (model.NAT_U64, model.BYTES_32, model.BOOL),
            record_term,
        )
        self.assertEqual(record_algorithm.function_type.output, record_type)
        self.assertEqual(
            success(model.Evaluator().evaluate(record_algorithm, inputs)).datum,
            model.DatumRecord(
                (
                    (0, model.Nat(9)),
                    (1, model.BytesValue(b"r" * 32)),
                    (2, True),
                )
            ),
        )

        projection = model.CanonicalAlgorithm(
            model.Symbol("HeterogeneousProjection"),
            record_algorithm.inputs,
            model.Project(record_term, 1),
        )
        self.assertEqual(projection.function_type.output, model.BYTES_32)
        self.assertEqual(
            success(model.Evaluator().evaluate(projection, inputs)).datum,
            model.BytesValue(b"r" * 32),
        )

    def test_heterogeneous_sum_case_is_exact_and_exhaustive(self) -> None:
        sum_type = model.ValueType(
            model.VARIANT_DOMAIN,
            model.VariantSchema(
                (
                    (0, model.BYTES_32),
                    (1, model.NAT_U64),
                    (2, model.UNIT_VALUE),
                )
            ),
        )
        identity_case = model.Case(
            model.Variable(0, sum_type),
            (
                (0, model.Inject(0, model.Variable(0, model.BYTES_32), sum_type)),
                (1, model.Inject(1, model.Variable(0, model.NAT_U64), sum_type)),
                (
                    2,
                    model.Inject(2, model.Variable(0, model.UNIT_VALUE), sum_type),
                ),
            ),
        )
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("HeterogeneousSumIdentity"), (sum_type,), identity_case
        )
        for datum in (
            model.DatumVariant(0, model.BytesValue(b"s" * 32)),
            model.DatumVariant(1, model.Nat(11)),
            model.DatumVariant(2, model.UNIT),
        ):
            with self.subTest(case=datum.case):
                supplied = value(sum_type, datum)
                self.assertEqual(
                    success(model.Evaluator().evaluate(algorithm, (supplied,))),
                    supplied,
                )

        nonexhaustive = replace(
            algorithm,
            term=model.Case(
                model.Variable(0, sum_type),
                identity_case.branches[:-1],
            ),
        )
        result = model.Evaluator().evaluate(
            nonexhaustive,
            (value(sum_type, model.DatumVariant(0, model.BytesValue(b"s" * 32))),),
        )
        self.assertEqual(result.outcome, model.Outcome.REFUSED)
        self.assertEqual(result.code, "K1-REFUSED-ALGORITHM-TYPING")


class SemanticFailureAbiTest(unittest.TestCase):
    @staticmethod
    def failure_module(
        name: str,
        payload_type: model.ValueType,
        imports: tuple[model.TypedContentId, ...] = (),
    ) -> model.SemanticModuleCandidate:
        return model.SemanticModuleCandidate(
            model.Symbol(name),
            imports,
            model.DatumSeq(
                (
                    model.DatumRecord(
                        (
                            (0, model.Symbol("semantic-failure")),
                            (
                                1,
                                model.DatumSeq(
                                    (
                                        model.DatumRecord(
                                            (
                                                (0, model.Symbol("CustomFailure")),
                                                (
                                                    1,
                                                    model.declaration_value_type_datum(
                                                        payload_type
                                                    ),
                                                ),
                                            )
                                        ),
                                    )
                                ),
                            ),
                        )
                    ),
                )
            ),
        )

    def test_failure_declaration_is_resolved_in_its_owner_import_scope(self) -> None:
        owner = self.failure_module("fixture.local-failure", model.UNIT_VALUE)
        failure = model.SemanticFailureType(owner.identity, 0, model.UNIT_VALUE)
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("ModuleLocalFailure"),
            (),
            model.Fail(
                failure,
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                model.UNIT_VALUE,
            ),
        )
        completed = model.Evaluator().evaluate(
            algorithm,
            (),
            modules={owner.identity: owner},
        )
        self.assertEqual(completed.outcome, model.Outcome.COMPLETED)
        self.assertEqual(
            completed.completion,
            model.DomainFailure(failure, value(model.UNIT_VALUE, model.UNIT)),
        )

        local_type_body = model.DatumRecord(
            (
                (
                    0,
                    model.DatumVariant(
                        0,
                        model.DatumRecord(
                            (
                                (0, model.Symbol("value-domain")),
                                (1, model.Nat(0)),
                            )
                        ),
                    ),
                ),
                (1, model.DatumVariant(0, model.UNIT)),
            )
        )
        aggregate = model.SemanticModuleCandidate(
            model.Symbol("fixture.aggregate-local-type"),
            (),
            model.DatumSeq(
                (
                    model.DatumRecord(
                        (
                            (0, model.Symbol("semantic-failure")),
                            (
                                1,
                                model.DatumSeq(
                                    (
                                        model.DatumRecord(
                                            (
                                                (0, model.Symbol("LocalFailure")),
                                                (1, local_type_body),
                                            )
                                        ),
                                    )
                                ),
                            ),
                        )
                    ),
                    model.DatumRecord(
                        (
                            (0, model.Symbol("value-domain")),
                            (
                                1,
                                model.DatumSeq(
                                    (
                                        model.DatumRecord(
                                            ((0, model.Symbol("OpaqueUnit")),)
                                        ),
                                    )
                                ),
                            ),
                        )
                    ),
                )
            ),
        )
        local_payload_type = model.ValueType(
            model.ValueDomain(
                aggregate.identity,
                model.Symbol("value-domain"),
                0,
            ),
            model.UnitSchema(),
        )
        local_failure = model.SemanticFailureType(
            aggregate.identity,
            0,
            local_payload_type,
        )
        model.authenticate_failure_reference(
            local_failure,
            {aggregate.identity: aggregate},
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        durable_self_spelling = model.declaration_value_type_datum(local_payload_type)
        with self.assertRaisesRegex(
            model.ModelError,
            "same-module declaration references must use local ordinals",
        ):
            model.lift_declaration_value_type_datum(
                durable_self_spelling,
                aggregate.identity,
                {aggregate.identity: aggregate},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )

        def durable_type(
            case: int,
            owner_bytes: bytes,
            kind: model.Symbol,
        ) -> model.DatumRecord:
            return model.DatumRecord(
                (
                    (
                        0,
                        model.DatumVariant(
                            1,
                            model.DatumVariant(
                                case,
                                model.DatumRecord(
                                    (
                                        (0, model.BytesValue(owner_bytes)),
                                        (1, kind),
                                        (2, model.Nat(0)),
                                    )
                                ),
                            ),
                        ),
                    ),
                    (1, model.DatumVariant(0, model.UNIT)),
                )
            )

        for case, kind, label in (
            (0, model.ROOT_VALUE_DOMAIN_KIND, "root"),
            (1, model.MODULE_VALUE_DOMAIN_KIND, "module"),
        ):
            with self.subTest(malformed_durable_owner=label):
                with self.assertRaisesRegex(
                    model.ModelError,
                    f"durable {label} declaration reference is malformed",
                ):
                    model.lift_declaration_value_type_datum(
                        durable_type(case, b"x", kind),
                        aggregate.identity,
                        {aggregate.identity: aggregate},
                        semantic_regime=model.SEMANTIC_REGIME_ID,
                    )

        malformed_prior_references = (
            model._frame(b"fixture.wrong-foundation")
            + model._frame(model.SEMANTIC_REGIME_KIND.encode("ascii"))
            + b"\x31" * 32,
            model._frame(model.FOUNDATION_PROFILE.encode("ascii"))
            + model._frame(b"foundation.unknown-prior-kind")
            + b"\x32" * 32,
        )
        for index, owner_bytes in enumerate(malformed_prior_references):
            with self.subTest(malformed_prior_axis=index):
                with self.assertRaisesRegex(
                    model.ModelError,
                    "durable root declaration reference is malformed",
                ):
                    model.lift_declaration_value_type_datum(
                        durable_type(
                            0,
                            owner_bytes,
                            model.ROOT_VALUE_DOMAIN_KIND,
                        ),
                        aggregate.identity,
                        {aggregate.identity: aggregate},
                        semantic_regime=model.SEMANTIC_REGIME_ID,
                    )

        def raw_content_reference(
            foundation: bytes,
            identity_profile: bytes,
        ) -> bytes:
            return (
                model._frame(foundation)
                + model._frame(identity_profile)
                + model._frame(model.HASH_SUITE_ID.internal_reference())
                + model._frame(model.SEMANTIC_MODULE_KIND.encode("ascii"))
                + model._frame(model.SEMANTIC_REGIME_ID.internal_reference())
                + b"\x33" * 32
            )

        malformed_content_references = (
            raw_content_reference(
                b"fixture.wrong-foundation",
                model.IDENTITY_PROFILE_ID.internal_reference(),
            ),
            raw_content_reference(
                model.FOUNDATION_PROFILE.encode("ascii"),
                model.HASH_SUITE_ID.internal_reference(),
            ),
        )
        for index, owner_bytes in enumerate(malformed_content_references):
            with self.subTest(malformed_content_axis=index):
                with self.assertRaisesRegex(
                    model.ModelError,
                    "durable module declaration reference is malformed",
                ):
                    model.lift_declaration_value_type_datum(
                        durable_type(
                            1,
                            owner_bytes,
                            model.MODULE_VALUE_DOMAIN_KIND,
                        ),
                        aggregate.identity,
                        {aggregate.identity: aggregate},
                        semantic_regime=model.SEMANTIC_REGIME_ID,
                    )

        wrong_kind_owner = model.content_id(
            "foundation.portable-algorithm",
            model.encode_datum(model.UNIT),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        with self.assertRaisesRegex(
            model.DeclarationKindMismatchError,
            "not a semantic module",
        ):
            model.lift_declaration_value_type_datum(
                durable_type(
                    1,
                    wrong_kind_owner.internal_reference(),
                    model.MODULE_VALUE_DOMAIN_KIND,
                ),
                aggregate.identity,
                {aggregate.identity: aggregate},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )

        foreign_regime = model.PriorMetaId(
            model.FOUNDATION_PROFILE,
            model.SEMANTIC_REGIME_KIND,
            b"\x7f" * 32,
        )
        foreign_module = model.content_id(
            model.SEMANTIC_MODULE_KIND,
            model.encode_datum(model.UNIT),
            semantic_regime=foreign_regime,
        )
        with self.assertRaisesRegex(
            model.DeclarationKindMismatchError,
            "crosses semantic regimes",
        ):
            model.lift_declaration_value_type_datum(
                durable_type(
                    1,
                    foreign_module.internal_reference(),
                    model.MODULE_VALUE_DOMAIN_KIND,
                ),
                aggregate.identity,
                {aggregate.identity: aggregate},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )

        foreign = module("fixture.foreign-failure-payload")
        foreign_type = model.ValueType(
            model.ValueDomain(
                foreign.identity,
                model.Symbol("value-domain"),
                0,
            ),
            model.UnitSchema(),
        )
        unscoped_owner = self.failure_module(
            "fixture.unscoped-failure",
            foreign_type,
        )
        unscoped_failure = model.SemanticFailureType(
            unscoped_owner.identity,
            0,
            foreign_type,
        )
        unscoped_algorithm = model.CanonicalAlgorithm(
            model.Symbol("UnscopedFailureReference"),
            (),
            model.Fail(
                unscoped_failure,
                model.Literal(model._admit_shaped_value(foreign_type, model.UNIT)),
                model.UNIT_VALUE,
            ),
        )
        rejected = model.Evaluator().evaluate(
            unscoped_algorithm,
            (),
            modules={
                unscoped_owner.identity: unscoped_owner,
                foreign.identity: foreign,
            },
        )
        self.assertEqual(rejected.outcome, model.Outcome.REFUSED)
        self.assertEqual(rejected.code, "K1-REFUSED-DECLARATION-ADMISSION")
        self.assertIn("outside the declaring module's import closure", rejected.detail)

        precedence_owner = module("fixture.nested-dvt-precedence")
        absent_child = model.DatumRecord(
            (
                (
                    0,
                    model.DatumVariant(
                        0,
                        model.DatumRecord(
                            (
                                (0, model.Symbol("value-domain")),
                                (1, model.Nat(999)),
                            )
                        ),
                    ),
                ),
                (1, model.DatumVariant(0, model.UNIT)),
            )
        )
        for position, children in enumerate(
            (
                (model.UNIT, absent_child),
                (absent_child, model.UNIT),
            )
        ):
            with self.subTest(recursive_dvt_formation=position):
                record_body = model.DatumRecord(
                    (
                        (
                            0,
                            model.DatumVariant(
                                1,
                                model.RECORD_DOMAIN.datum(),
                            ),
                        ),
                        (
                            1,
                            model.DatumVariant(
                                7,
                                model.DatumSeq(
                                    tuple(
                                        model.DatumRecord(
                                            (
                                                (0, model.Nat(ordinal)),
                                                (1, child),
                                            )
                                        )
                                        for ordinal, child in enumerate(children)
                                    )
                                ),
                            ),
                        ),
                    )
                )
                with self.assertRaisesRegex(
                    model.ModelError,
                    "declaration-local value type has the wrong exact record shape",
                ):
                    model.lift_declaration_value_type_datum(
                        record_body,
                        precedence_owner.identity,
                        {precedence_owner.identity: precedence_owner},
                        semantic_regime=model.SEMANTIC_REGIME_ID,
                    )

        formed_unit_type = model.declaration_value_type_datum(model.UNIT_VALUE)
        for ordinals in ((1, 0), (0, 0)):
            with self.subTest(declaration_schema_ordinals=ordinals):
                malformed_record_order = model.DatumRecord(
                    (
                        (
                            0,
                            model.DatumVariant(
                                1,
                                model.RECORD_DOMAIN.datum(),
                            ),
                        ),
                        (
                            1,
                            model.DatumVariant(
                                7,
                                model.DatumSeq(
                                    tuple(
                                        model.DatumRecord(
                                            (
                                                (0, model.Nat(ordinal)),
                                                (1, formed_unit_type),
                                            )
                                        )
                                        for ordinal in ordinals
                                    )
                                ),
                            ),
                        ),
                    )
                )
                with self.assertRaisesRegex(
                    model.ModelError,
                    "ordinals are not strictly increasing",
                ):
                    model.lift_declaration_value_type_datum(
                        malformed_record_order,
                        precedence_owner.identity,
                        {precedence_owner.identity: precedence_owner},
                        semantic_regime=model.SEMANTIC_REGIME_ID,
                    )

        invalid_schema_child = model.DatumRecord(
            (
                (
                    0,
                    model.DatumVariant(1, model.NAT_DOMAIN.datum()),
                ),
                (1, model.DatumVariant(2, model.Nat(1 << 256))),
            )
        )
        with self.assertRaisesRegex(
            model.DeclarationAdmissionRefusedError,
            "declaration schema or lifted value type failed admission",
        ):
            model.lift_declaration_value_type_datum(
                invalid_schema_child,
                precedence_owner.identity,
                {precedence_owner.identity: precedence_owner},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )
        for position, children in enumerate(
            (
                (invalid_schema_child, absent_child),
                (absent_child, invalid_schema_child),
            )
        ):
            with self.subTest(context_free_dsb_admission=position):
                record_body = model.DatumRecord(
                    (
                        (
                            0,
                            model.DatumVariant(
                                1,
                                model.RECORD_DOMAIN.datum(),
                            ),
                        ),
                        (
                            1,
                            model.DatumVariant(
                                7,
                                model.DatumSeq(
                                    tuple(
                                        model.DatumRecord(
                                            (
                                                (0, model.Nat(ordinal)),
                                                (1, child),
                                            )
                                        )
                                        for ordinal, child in enumerate(children)
                                    )
                                ),
                            ),
                        ),
                    )
                )
                with self.assertRaisesRegex(
                    model.DeclarationAdmissionRefusedError,
                    "module declaration ordinal is absent",
                ):
                    model.lift_declaration_value_type_datum(
                        record_body,
                        precedence_owner.identity,
                        {precedence_owner.identity: precedence_owner},
                        semantic_regime=model.SEMANTIC_REGIME_ID,
                    )

    def test_non_value_declaration_cannot_be_used_as_a_local_domain(self) -> None:
        invalid_local_type = model.DatumRecord(
            (
                (
                    0,
                    model.DatumVariant(
                        0,
                        model.DatumRecord(
                            (
                                (0, model.Symbol("semantic-failure")),
                                (1, model.Nat(0)),
                            )
                        ),
                    ),
                ),
                (1, model.DatumVariant(0, model.UNIT)),
            )
        )
        owner = model.SemanticModuleCandidate(
            model.Symbol("fixture.invalid-local-domain-kind"),
            (),
            model.DatumSeq(
                (
                    model.DatumRecord(
                        (
                            (0, model.Symbol("semantic-failure")),
                            (
                                1,
                                model.DatumSeq(
                                    (
                                        model.DatumRecord(
                                            (
                                                (0, model.Symbol("RecursiveFailure")),
                                                (1, invalid_local_type),
                                            )
                                        ),
                                    )
                                ),
                            ),
                        )
                    ),
                )
            ),
        )
        invalid_payload = model.ValueType(
            model.ValueDomain(
                owner.identity,
                model.Symbol("semantic-failure"),
                0,
            ),
            model.UnitSchema(),
        )
        failure = model.SemanticFailureType(owner.identity, 0, invalid_payload)
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("InvalidLocalDomainKind"),
            (),
            model.Fail(
                failure,
                model.Literal(model._admit_shaped_value(invalid_payload, model.UNIT)),
                model.UNIT_VALUE,
            ),
        )
        result = model.Evaluator().evaluate(
            algorithm,
            (),
            modules={owner.identity: owner},
        )
        self.assertEqual(result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(result.code, "K1-KIND-DECLARATION")
        self.assertIn("wrong declaration kind", result.detail)

    def test_local_type_lift_rechecks_the_expanded_durable_body_bound(self) -> None:
        maximum_natural = (1 << 256) - 1
        local_domain = model.DatumVariant(
            0,
            model.DatumRecord(
                (
                    (0, model.Symbol("value-domain")),
                    (1, model.Nat(0)),
                )
            ),
        )
        local_natural = model.DatumRecord(
            (
                (0, local_domain),
                (1, model.DatumVariant(2, model.Nat(maximum_natural))),
            )
        )
        root_record = model.DatumVariant(
            1,
            model.ValueDomain(
                model.SEMANTIC_REGIME_ID,
                model.ROOT_VALUE_DOMAIN_KIND,
                7,
            ).datum(),
        )

        def local_record(field_count: int) -> model.DatumRecord:
            return model.DatumRecord(
                (
                    (0, root_record),
                    (
                        1,
                        model.DatumVariant(
                            7,
                            model.DatumSeq(
                                tuple(
                                    model.DatumRecord(
                                        ((0, model.Nat(index)), (1, local_natural))
                                    )
                                    for index in range(field_count)
                                )
                            ),
                        ),
                    ),
                )
            )

        def aggregate(
            field_count: int,
        ) -> tuple[model.SemanticModuleCandidate, model.Datum]:
            payload = local_record(field_count)
            candidate = model.SemanticModuleCandidate(
                model.Symbol("fixture.local-type-expansion"),
                (),
                model.DatumSeq(
                    (
                        model.DatumRecord(
                            (
                                (0, model.Symbol("semantic-failure")),
                                (
                                    1,
                                    model.DatumSeq(
                                        (
                                            model.DatumRecord(
                                                (
                                                    (0, model.Symbol("WideFailure")),
                                                    (1, payload),
                                                )
                                            ),
                                        )
                                    ),
                                ),
                            )
                        ),
                        model.DatumRecord(
                            (
                                (0, model.Symbol("value-domain")),
                                (
                                    1,
                                    model.DatumSeq(
                                        (
                                            model.DatumRecord(
                                                ((0, model.Symbol("OpaqueNatural")),)
                                            ),
                                        )
                                    ),
                                ),
                            )
                        ),
                    )
                ),
            )
            self.assertLess(len(candidate.body()), model.MAX_CANONICAL_BYTES)
            return candidate, payload

        exact_candidate, exact_body = aggregate(1548)
        lifted = model.lift_declaration_value_type_datum(
            exact_body,
            exact_candidate.identity,
            {exact_candidate.identity: exact_candidate},
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        self.assertEqual(
            len(model.encode_datum(model.value_type_datum(lifted))),
            1_048_033,
        )

        over_candidate, over_body = aggregate(1549)
        with self.assertRaisesRegex(
            model.DeclarationAdmissionRefusedError,
            "lifted declaration value type exceeds a constitutional body bound",
        ):
            model.lift_declaration_value_type_datum(
                over_body,
                over_candidate.identity,
                {over_candidate.identity: over_candidate},
                semantic_regime=model.SEMANTIC_REGIME_ID,
            )

        over_failure = model.SemanticFailureType(
            over_candidate.identity,
            0,
            model.UNIT_VALUE,
        )
        over_algorithm = model.CanonicalAlgorithm(
            model.Symbol("ExpandedDeclarationTypeRefusal"),
            (),
            model.Fail(
                over_failure,
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                model.UNIT_VALUE,
            ),
        )
        refused = model.Evaluator().evaluate(
            over_algorithm,
            (),
            modules={over_candidate.identity: over_candidate},
        )
        self.assertEqual(refused.outcome, model.Outcome.REFUSED)
        self.assertEqual(refused.code, "K1-REFUSED-DECLARATION-ADMISSION")

    def test_strict_index_declares_and_returns_its_exact_failure(self) -> None:
        sequence_type = model.ValueType(
            model.SEQUENCE_DOMAIN, model.SeqSchema(model.BYTES_32, 2)
        )
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("StrictIndexFixture"),
            (sequence_type, model.NAT_U64),
            model.StrictIndex(
                model.Variable(0, sequence_type),
                model.Variable(1, model.NAT_U64),
                model.INDEX_OUT_OF_RANGE_FAILURE,
            ),
        )
        self.assertEqual(
            algorithm.function_type.failures,
            (model.INDEX_OUT_OF_RANGE_FAILURE,),
        )
        index = value(model.NAT_U64, model.Nat(1))
        result = model.Evaluator().evaluate(
            algorithm,
            (
                value(
                    sequence_type,
                    model.DatumSeq((model.BytesValue(b"a" * 32),)),
                ),
                index,
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(
            result.completion,
            model.DomainFailure(model.INDEX_OUT_OF_RANGE_FAILURE, index),
        )

    def test_wrong_failure_payload_is_refused_at_typing(self) -> None:
        ill_typed = model.CanonicalAlgorithm(
            model.Symbol("WrongFailurePayload"),
            (),
            model.Fail(
                model.ZERO_DIVISOR_FAILURE,
                model.Literal(value(model.NAT_U64, model.Nat(0))),
                model.NAT_U64,
            ),
        )
        result = model.Evaluator().evaluate(
            ill_typed, (), modules=model.FIXTURE_MODULE_PREIMAGES
        )
        self.assertEqual(result.outcome, model.Outcome.REFUSED)
        self.assertEqual(result.code, "K1-REFUSED-ALGORITHM-TYPING")

        owner = self.failure_module(
            "fixture.failure-declaration-payload-compatibility",
            model.UNIT_VALUE,
        )
        incompatible_failure = model.SemanticFailureType(
            owner.identity,
            0,
            model.NAT_U64,
        )
        incompatible_algorithm = model.CanonicalAlgorithm(
            model.Symbol("FailureDeclarationPayloadCompatibility"),
            (),
            model.Fail(
                incompatible_failure,
                model.Literal(value(model.NAT_U64, model.Nat(0))),
                model.UNIT_VALUE,
            ),
        )
        incompatible_result = model.Evaluator().evaluate(
            incompatible_algorithm,
            (),
            modules={owner.identity: owner},
        )
        self.assertEqual(incompatible_result.outcome, model.Outcome.REFUSED)
        self.assertEqual(
            incompatible_result.code,
            "K1-REFUSED-DECLARATION-ADMISSION",
        )
        self.assertIn(
            "payload disagrees with its module declaration",
            incompatible_result.detail,
        )

    def test_one_failure_declaration_cannot_claim_two_payload_types(self) -> None:
        unit_failure = model.SemanticFailureType(
            model.FIXTURE_EXTENSION_MODULE_ID,
            0,
            model.UNIT_VALUE,
        )
        bytes_failure = model.SemanticFailureType(
            model.FIXTURE_EXTENSION_MODULE_ID,
            0,
            model.BYTES_0_32,
        )
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("ConflictingFailurePayloads"),
            (),
            model.Conditional(
                model.Literal(value(model.BOOL, True)),
                model.Fail(
                    unit_failure,
                    model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                    model.UNIT_VALUE,
                ),
                model.Fail(
                    bytes_failure,
                    model.Literal(value(model.BYTES_0_32, model.BytesValue(b""))),
                    model.UNIT_VALUE,
                ),
            ),
        )
        with self.assertRaisesRegex(
            model.ModelError,
            "conflicting payload types",
        ):
            _ = algorithm.function_type
        with self.assertRaisesRegex(
            model.ModelError,
            "conflicting payload types",
        ):
            model.check_algorithm_syntax_and_types(algorithm)

    def test_undeclared_or_wrongly_typed_runtime_failure_is_checker_failure(
        self,
    ) -> None:
        base = model.CanonicalAlgorithm(
            model.Symbol("NoDeclaredFailures"),
            (),
            model.Literal(value(model.NAT_U64, model.Nat(7))),
        )
        undeclared_type = model.SemanticFailureType(
            model.FIXTURE_EXTENSION_MODULE_ID, 99, model.UNIT_VALUE
        )

        class UndeclaredFailureEvaluator(model.Evaluator):
            def _eval(self, term: object, env: object, meter: object) -> object:
                raise model._SemanticFailure(
                    model.DomainFailure(
                        undeclared_type,
                        value(model.UNIT_VALUE, model.UNIT),
                    )
                )

        undeclared = UndeclaredFailureEvaluator().evaluate(base, ())
        self.assertEqual(undeclared.outcome, model.Outcome.CHECKER_FAILURE)
        self.assertEqual(undeclared.code, "K1-CHECKER-FAILURE-SEMANTIC-FAILURE")

        class WrongPayloadEvaluator(model.Evaluator):
            def _eval(self, term: object, env: object, meter: object) -> object:
                raise model._SemanticFailure(
                    model.DomainFailure(
                        model.ZERO_DIVISOR_FAILURE,
                        value(model.NAT_U64, model.Nat(0)),
                    )
                )

        wrong = WrongPayloadEvaluator().evaluate(
            model.build_mod_algorithm(),
            (),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(wrong.outcome, model.Outcome.KIND_MISMATCH)
        wrong = WrongPayloadEvaluator().evaluate(
            model.build_mod_algorithm(),
            (
                value(model.NAT_U64, model.Nat(1)),
                value(model.NAT_U64, model.Nat(1)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(wrong.outcome, model.Outcome.CHECKER_FAILURE)
        self.assertEqual(wrong.code, "K1-CHECKER-FAILURE-SEMANTIC-FAILURE")

        class AliasValueType:
            comparisons = 0

            def __eq__(self, _other: object) -> bool:
                AliasValueType.comparisons += 1
                return True

            def __ne__(self, _other: object) -> bool:
                AliasValueType.comparisons += 1
                return False

        class ForgedSuccessEvaluator(model.Evaluator):
            def _eval(self, term: object, env: object, meter: object) -> object:
                return model.CanonicalValue(
                    AliasValueType(),  # type: ignore[arg-type]
                    model.Nat(7),
                )

        forged_success = ForgedSuccessEvaluator().evaluate(base, ())
        self.assertEqual(forged_success.outcome, model.Outcome.CHECKER_FAILURE)
        self.assertEqual(forged_success.code, "K1-CHECKER-FAILURE")
        self.assertEqual(AliasValueType.comparisons, 0)

        class AliasFailureType:
            comparisons = 0
            local_ordinal = 999
            payload_type = model.UNIT_VALUE

            def __eq__(self, _other: object) -> bool:
                AliasFailureType.comparisons += 1
                return True

            def __ne__(self, _other: object) -> bool:
                AliasFailureType.comparisons += 1
                return False

        class ForgedFailureEvaluator(model.Evaluator):
            def _eval(self, term: object, env: object, meter: object) -> object:
                raise model._SemanticFailure(
                    model.DomainFailure(
                        AliasFailureType(),  # type: ignore[arg-type]
                        value(model.UNIT_VALUE, model.UNIT),
                    )
                )

        forged_failure = ForgedFailureEvaluator().evaluate(
            model.build_mod_algorithm(),
            (
                value(model.NAT_U64, model.Nat(1)),
                value(model.NAT_U64, model.Nat(1)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(forged_failure.outcome, model.Outcome.CHECKER_FAILURE)
        self.assertEqual(
            forged_failure.code,
            "K1-CHECKER-FAILURE-SEMANTIC-FAILURE",
        )
        self.assertEqual(AliasFailureType.comparisons, 0)

        incomplete_failure = object.__new__(model.DomainFailure)
        object.__setattr__(
            incomplete_failure,
            "failure_type",
            model.ZERO_DIVISOR_FAILURE,
        )

        class IncompleteFailureEvaluator(model.Evaluator):
            def _eval(self, term: object, env: object, meter: object) -> object:
                raise model._SemanticFailure(incomplete_failure)

        incomplete = IncompleteFailureEvaluator().evaluate(
            model.build_mod_algorithm(),
            (
                value(model.NAT_U64, model.Nat(1)),
                value(model.NAT_U64, model.Nat(1)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(incomplete.outcome, model.Outcome.CHECKER_FAILURE)
        self.assertEqual(
            incomplete.code,
            "K1-CHECKER-FAILURE-SEMANTIC-FAILURE",
        )


class SharedNoncompletionVocabularyTest(unittest.TestCase):
    def test_cannot_answer_is_distinct_and_never_completion(self) -> None:
        shared_noncompletion = (
            model.Outcome.UNSUPPORTED,
            model.Outcome.MISSING_DEPENDENCY,
            model.Outcome.CANNOT_ANSWER,
            model.Outcome.KIND_MISMATCH,
            model.Outcome.MALFORMED,
            model.Outcome.REFUSED,
            model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
            model.Outcome.CHECKER_FAILURE,
        )

        self.assertEqual(len(shared_noncompletion), len(set(shared_noncompletion)))
        self.assertEqual(
            set(model.Outcome),
            {model.Outcome.COMPLETED, *shared_noncompletion},
        )
        self.assertNotIn(model.Outcome.COMPLETED, shared_noncompletion)
        self.assertIsNot(
            model.Outcome.CANNOT_ANSWER,
            model.Outcome.MISSING_DEPENDENCY,
        )
        self.assertEqual(model.Outcome.CANNOT_ANSWER.value, "CannotAnswer")
        self.assertIn(
            b"CannotAnswer-means-an-exact-supported-and-structurally-formed-"
            b"operation-cannot-obtain-a-required-semantic-premise,live-read,or-"
            b"authority-needed-to-answer-and-is-neither-a-missing-named-durable-"
            b"preimage-nor-a-negative-semantic-conclusion",
            model.SEMANTIC_CORE_LAW_SOURCE,
        )


class EvaluationContractAndLimitTest(unittest.TestCase):
    def transcript_case(
        self,
    ) -> tuple[model.CanonicalAlgorithm, tuple[model.CanonicalValue, ...]]:
        algorithm = model.build_transcript_algorithm()
        return algorithm, (
            value(model.BYTES_32, model.BytesValue(b"t" * 32)),
            value(
                algorithm.function_type.inputs[1],
                model.DatumSeq((model.BytesValue(b"message"),)),
            ),
        )

    def test_evaluation_contract_and_request_limits_do_not_change_semantics_id(
        self,
    ) -> None:
        algorithm, inputs = self.transcript_case()
        identity = algorithm.identity
        changed_contract = replace(model.DEFAULT_EVALUATION_CONTRACT, term_step_units=2)
        self.assertNotEqual(
            model.DEFAULT_EVALUATION_CONTRACT.identity,
            changed_contract.identity,
        )
        evaluator = model.Evaluator(
            supported_contracts=(
                model.DEFAULT_EVALUATION_CONTRACT,
                changed_contract,
            )
        )
        baseline = evaluator.evaluate(
            algorithm, inputs, modules=model.FIXTURE_MODULE_PREIMAGES
        )
        by_contract_id = evaluator.evaluate(
            algorithm,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
            evaluation_contract=model.DEFAULT_EVALUATION_CONTRACT.identity,
        )
        changed = evaluator.evaluate(
            algorithm,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
            evaluation_contract=changed_contract,
        )
        roomy = evaluator.evaluate(
            algorithm,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
            limits=model.DeterministicLimits(
                1_000_000, 1_000_000, 1_000_000, 1_000_000
            ),
        )
        self.assertEqual(identity, algorithm.identity)
        self.assertEqual(by_contract_id.completion, baseline.completion)
        self.assertEqual(by_contract_id.charge, baseline.charge)
        self.assertEqual(baseline.completion, changed.completion)
        self.assertEqual(baseline.completion, roomy.completion)
        self.assertEqual(changed.charge.steps, baseline.charge.steps * 2)

    def test_exact_resource_envelope_completes_and_each_one_less_fails(self) -> None:
        algorithm, inputs = self.transcript_case()
        evaluator = model.Evaluator()
        baseline = evaluator.evaluate(
            algorithm, inputs, modules=model.FIXTURE_MODULE_PREIMAGES
        )
        self.assertEqual(baseline.outcome, model.Outcome.COMPLETED)
        capacity = model.maximum_completion_size(algorithm.function_type)
        exact = model.DeterministicLimits(
            baseline.charge.steps,
            baseline.charge.iteration_items,
            baseline.charge.primitive_work,
            capacity,
        )
        accepted = evaluator.evaluate(
            algorithm,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
            limits=exact,
        )
        self.assertEqual(accepted.outcome, model.Outcome.COMPLETED)
        self.assertEqual(accepted.charge, baseline.charge)

        dimensions = (
            "maximum_steps",
            "maximum_iteration_items",
            "maximum_primitive_work",
        )
        charge_fields = ("steps", "iteration_items", "primitive_work")
        for limit_field, charge_field in zip(dimensions, charge_fields):
            with self.subTest(limit=limit_field):
                one_less = replace(
                    exact, **{limit_field: getattr(exact, limit_field) - 1}
                )
                rejected = evaluator.evaluate(
                    algorithm,
                    inputs,
                    modules=model.FIXTURE_MODULE_PREIMAGES,
                    limits=one_less,
                )
                self.assertEqual(
                    rejected.outcome,
                    model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
                )
                self.assertEqual(rejected.code, "K1-LIMIT-EVALUATION")
                self.assertLessEqual(
                    getattr(rejected.charge, charge_field),
                    getattr(one_less, limit_field),
                )

    def test_result_capacity_is_preflighted_before_term_evaluation(self) -> None:
        algorithm, inputs = self.transcript_case()

        class SpyEvaluator(model.Evaluator):
            calls = 0

            def _eval(self, term: object, env: object, meter: object) -> object:
                self.calls += 1
                return super()._eval(term, env, meter)  # type: ignore[arg-type]

        evaluator = SpyEvaluator()
        capacity = model.maximum_completion_size(algorithm.function_type)
        limits = replace(model.DEFAULT_LIMITS, maximum_result_bytes=capacity - 1)
        result = evaluator.evaluate(
            algorithm,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
            limits=limits,
        )
        self.assertEqual(result.outcome, model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED)
        self.assertEqual(result.code, "K1-LIMIT-RESULT-CAPACITY")
        self.assertEqual(result.charge, model.AbstractCharge())
        self.assertEqual(evaluator.calls, 0)

        maximum_bytes_type = model.ValueType(
            model.BYTES_DOMAIN,
            model.BytesSchema(0, model.MAX_CANONICAL_BYTES - 9),
        )
        inadmissible_completion = model.CanonicalAlgorithm(
            model.Symbol("CompletionSchemaAdmissionFixture"),
            (),
            model.Literal(value(maximum_bytes_type, model.BytesValue(b""))),
        )
        schema_result = evaluator.evaluate(inadmissible_completion, ())
        self.assertEqual(schema_result.outcome, model.Outcome.REFUSED)
        self.assertEqual(
            schema_result.code,
            "K1-REFUSED-COMPLETION-SCHEMA-ADMISSION",
        )
        self.assertEqual(schema_result.charge, model.AbstractCharge())
        self.assertEqual(evaluator.calls, 0)

    def test_iteration_charge_precedes_item_admission_and_body_work(self) -> None:
        sequence_type = model.ValueType(
            model.SEQUENCE_DOMAIN,
            model.SeqSchema(model.BYTES_8, 1),
        )
        loop_result = model.ValueType(
            model.VARIANT_DOMAIN,
            model.VariantSchema(((0, model.UNIT_VALUE), (1, model.UNIT_VALUE))),
        )
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("ChargeBeforeIteratorItem"),
            (sequence_type,),
            model.BoundedIterate(
                model.SequenceIterationSource(model.Variable(0, sequence_type)),
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                model.Inject(
                    0,
                    model.Variable(2, model.UNIT_VALUE),
                    loop_result,
                ),
            ),
        )
        inputs = (
            value(
                sequence_type,
                model.DatumSeq((model.BytesValue(b"x" * 8),)),
            ),
        )
        exact_admit_value = model.admit_value

        def reject_early_item_admission(
            value_type: model.ValueType,
            datum: model.Datum,
        ) -> model.CanonicalValue:
            if value_type == model.BYTES_8 and datum == model.BytesValue(b"x" * 8):
                raise AssertionError("iterator item admitted before its charge")
            return exact_admit_value(value_type, datum)

        limits = replace(model.DEFAULT_LIMITS, maximum_iteration_items=0)
        with patch.object(
            model,
            "admit_value",
            side_effect=reject_early_item_admission,
        ):
            result = model.Evaluator().evaluate(algorithm, inputs, limits=limits)
        self.assertEqual(result.outcome, model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED)
        self.assertEqual(result.code, "K1-LIMIT-EVALUATION")
        self.assertEqual(result.charge.iteration_items, 0)
        self.assertEqual(result.charge.steps, 3)

    def test_invalid_limit_shapes_are_malformed(self) -> None:
        algorithm, inputs = self.transcript_case()
        invalid = (-1, True, "10", 1.5, float("nan"), float("inf"))
        for field in (
            "maximum_steps",
            "maximum_iteration_items",
            "maximum_primitive_work",
            "maximum_result_bytes",
        ):
            for bad in invalid:
                with self.subTest(field=field, bad=bad):
                    limits = replace(model.DEFAULT_LIMITS, **{field: bad})
                    result = model.Evaluator().evaluate(
                        algorithm,
                        inputs,
                        modules=model.FIXTURE_MODULE_PREIMAGES,
                        limits=limits,
                    )
                    self.assertEqual(result.outcome, model.Outcome.MALFORMED)
                    self.assertEqual(result.code, "K1-MALFORMED-LIMITS")

    def test_memory_error_escapes_without_false_checker_classification(self) -> None:
        algorithm = model.CanonicalAlgorithm(
            model.Symbol("MemoryErrorFixture"),
            (),
            model.Literal(value(model.UNIT_VALUE, model.UNIT)),
        )

        class ExhaustedEvaluator(model.Evaluator):
            def _eval(self, term: object, env: object, meter: object) -> object:
                raise MemoryError("host exhausted")

        with self.assertRaises(MemoryError):
            ExhaustedEvaluator().evaluate(algorithm, ())

    def test_validation_precedence_is_stable_under_multiple_defects(self) -> None:
        wrong_contract_kind = model.content_id(
            "not-an-evaluation-contract",
            model.encode_datum(model.Symbol("wrong-contract")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        bad_basis = replace(
            model.FOUNDATION_PRIOR_META_PREIMAGES,
            identity_profile=model.encode_datum(
                model.Symbol("forged-identity-profile")
            ),
        )
        invalid_limits = replace(model.DEFAULT_LIMITS, maximum_steps=-1)
        first = model.Evaluator().evaluate(
            object(),
            (),
            limits=invalid_limits,
            prior_meta_preimages=bad_basis,
            evaluation_contract=wrong_contract_kind,
        )
        self.assertEqual(first.code, "K1-MALFORMED-LIMITS")

        prior_meta_first = model.Evaluator().evaluate(
            object(),
            (),
            prior_meta_preimages=bad_basis,
            evaluation_contract=wrong_contract_kind,
        )
        self.assertEqual(prior_meta_first.code, "K1-MALFORMED-PRIOR-META-BASIS")

        supported_basis_subject = model.CanonicalAlgorithm(
            model.Symbol("EvaluatorPriorMetaSupportFixture"),
            (),
            model.Literal(value(model.UNIT_VALUE, model.UNIT)),
        )
        with patch.object(model, "FOUNDATION_PRIOR_META_PREIMAGES", bad_basis):
            evaluator_basis_failure = model.Evaluator().evaluate(
                supported_basis_subject,
                (),
                prior_meta_preimages=model.PriorMetaPreimageBundle(
                    model.encode_datum(model.IDENTITY_PROFILE_DESCRIPTOR),
                    model.encode_datum(model.HASH_SUITE_DESCRIPTOR),
                    model.encode_datum(model.SEMANTIC_REGIME_DESCRIPTOR),
                ),
            )
        self.assertEqual(
            evaluator_basis_failure.outcome,
            model.Outcome.CHECKER_FAILURE,
        )
        self.assertEqual(
            evaluator_basis_failure.code,
            "K1-CHECKER-PRIOR-META-SUPPORT",
        )
        self.assertEqual(evaluator_basis_failure.charge, model.AbstractCharge())

        contract_first = model.Evaluator().evaluate(
            object(), (), evaluation_contract=wrong_contract_kind
        )
        self.assertEqual(contract_first.code, "K1-KIND-EVALUATION-CONTRACT")

        subject_first = model.Evaluator().evaluate(object(), ())
        self.assertEqual(subject_first.outcome, model.Outcome.MALFORMED)
        self.assertEqual(subject_first.code, "K1-MALFORMED-SUBJECT-CARRIER")

        malformed_contract = model.Evaluator().evaluate(
            model.CanonicalAlgorithm(
                model.Symbol("MalformedContractCarrierFixture"),
                (),
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
            ),
            (),
            evaluation_contract=object(),  # type: ignore[arg-type]
        )
        self.assertEqual(malformed_contract.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            malformed_contract.code,
            "K1-MALFORMED-EVALUATION-CONTRACT",
        )

        structurally_malformed = model.CanonicalAlgorithm(
            model.Symbol("MalformedStructuralIdentity"),
            (),
            object(),  # type: ignore[arg-type]
        )
        structural_first = model.Evaluator().evaluate(
            structurally_malformed,
            (),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(structural_first.code, "K1-MALFORMED-MODEL")

        projection = model.build_lossy_projection_algorithm()
        self.assertIsInstance(projection.term, model.PrimitiveCall)
        ill_typed_primitive = replace(
            projection,
            term=replace(
                projection.term,
                arguments=(),
            ),
        )
        module_first = model.Evaluator().evaluate(ill_typed_primitive, ())
        self.assertEqual(module_first.code, "K1-MISSING-MODULE")

        typing_first = model.Evaluator().evaluate(
            ill_typed_primitive,
            (),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(typing_first.code, "K1-REFUSED-ALGORITHM-TYPING")

        input_header_last = model.Evaluator().evaluate(
            projection,
            (),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(input_header_last.code, "K1-KIND-ARITY")

    def test_unknown_contract_and_missing_primitive_cost_are_unsupported(self) -> None:
        algorithm, inputs = self.transcript_case()
        unknown = model.content_id(
            "foundation.evaluation-contract",
            model.encode_datum(model.Symbol("unknown-contract")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        unknown_result = model.Evaluator().evaluate(
            algorithm,
            inputs,
            modules=model.FIXTURE_MODULE_PREIMAGES,
            evaluation_contract=unknown,
        )
        self.assertEqual(unknown_result.outcome, model.Outcome.UNSUPPORTED)
        self.assertEqual(unknown_result.code, "K1-UNSUPPORTED-EVALUATION-CONTRACT")

        projection_id = model.PRIMITIVE_IDS_BY_KEY[("fixture.bytes.prefix-27", 1)]
        no_projection_cost = replace(
            model.DEFAULT_EVALUATION_CONTRACT,
            primitive_cost_rules=tuple(
                rule
                for rule in model.DEFAULT_EVALUATION_CONTRACT.primitive_cost_rules
                if rule.primitive != projection_id
            ),
        )
        evaluator = model.Evaluator(supported_contracts=(no_projection_cost,))
        projection = model.build_lossy_projection_algorithm()
        result = evaluator.evaluate(
            projection,
            (value(model.BYTES_32, model.BytesValue(b"p" * 32)),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
            evaluation_contract=no_projection_cost,
            limits=replace(model.DEFAULT_LIMITS, maximum_result_bytes=0),
        )
        self.assertEqual(result.outcome, model.Outcome.UNSUPPORTED)
        self.assertEqual(result.code, "K1-UNSUPPORTED-PRIMITIVE-COST")
        self.assertEqual(result.charge, model.AbstractCharge())

        registry_subject = model.CanonicalAlgorithm(
            model.Symbol("CorruptContractRegistryFixture"),
            (),
            model.Literal(value(model.UNIT_VALUE, model.UNIT)),
        )
        corrupt_values = (
            object(),
            None,
            replace(model.DEFAULT_EVALUATION_CONTRACT, term_step_units=2),
        )
        for corrupt_value in corrupt_values:
            with self.subTest(registry_value=type(corrupt_value).__name__):
                corrupt_registry = model.Evaluator()
                object.__setattr__(
                    corrupt_registry,
                    "_supported_contracts",
                    {model.DEFAULT_EVALUATION_CONTRACT.identity: corrupt_value},
                )
                checker_failure = corrupt_registry.evaluate(
                    registry_subject,
                    (),
                )
                self.assertEqual(
                    checker_failure.outcome,
                    model.Outcome.CHECKER_FAILURE,
                )
                self.assertEqual(
                    checker_failure.code,
                    "K1-CHECKER-EVALUATION-CONTRACT-REGISTRY",
                )
                self.assertEqual(checker_failure.charge, model.AbstractCharge())
                self.assertIsNone(checker_failure.completion)

    def test_cost_formula_must_match_exact_call_abi_before_preflight(self) -> None:
        projection_id = model.PRIMITIVE_IDS_BY_KEY[("fixture.bytes.prefix-27", 1)]
        incompatible_rule = model.PrimitiveWorkFormulaV0(
            model.Symbol("sum-byte-lengths"),
            (1,),
        )
        with self.assertRaisesRegex(model.ModelError, "u64 naturals"):
            model.PrimitiveWorkFormulaV0(
                model.Symbol("sum-byte-lengths"),
                (1 << 64,),
            )

        unknown_formula = object.__new__(model.PrimitiveWorkFormulaV0)
        object.__setattr__(unknown_formula, "kind", model.Symbol("unknown-v0-rule"))
        object.__setattr__(unknown_formula, "argument_indices", ())
        object.__setattr__(unknown_formula, "constant", 0)
        unknown_rule = object.__new__(model.PrimitiveCostRuleV0)
        object.__setattr__(unknown_rule, "primitive", projection_id)
        object.__setattr__(unknown_rule, "formula", unknown_formula)
        unknown_contract = object.__new__(model.EvaluationContractV0)
        for field in (
            "term_step_units",
            "iteration_item_units",
            "validation_precedence",
            "completion_measure",
            "static_bound_rule",
            "semantic_regime",
        ):
            object.__setattr__(
                unknown_contract,
                field,
                getattr(model.DEFAULT_EVALUATION_CONTRACT, field),
            )
        object.__setattr__(unknown_contract, "primitive_cost_rules", (unknown_rule,))
        unknown_result = model.Evaluator().evaluate(
            model.CanonicalAlgorithm(
                model.Symbol("UnknownWorkFormulaFixture"),
                (),
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
            ),
            (),
            evaluation_contract=unknown_contract,
        )
        self.assertEqual(unknown_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            unknown_result.code,
            "K1-MALFORMED-EVALUATION-CONTRACT",
        )
        self.assertEqual(unknown_result.charge, model.AbstractCharge())
        self.assertIsNone(unknown_result.completion)

        wrong_kind_key = model.content_id(
            "foundation.not-a-semantic-primitive",
            model.encode_datum(model.Symbol("wrong-kind-unknown-formula")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        combined_rule = object.__new__(model.PrimitiveCostRuleV0)
        object.__setattr__(combined_rule, "primitive", wrong_kind_key)
        object.__setattr__(combined_rule, "formula", unknown_formula)
        combined_contract = object.__new__(model.EvaluationContractV0)
        for field in (
            "term_step_units",
            "iteration_item_units",
            "validation_precedence",
            "completion_measure",
            "static_bound_rule",
            "semantic_regime",
        ):
            object.__setattr__(
                combined_contract,
                field,
                getattr(model.DEFAULT_EVALUATION_CONTRACT, field),
            )
        object.__setattr__(combined_contract, "primitive_cost_rules", (combined_rule,))
        combined_result = model.Evaluator().evaluate(
            model.CanonicalAlgorithm(
                model.Symbol("UnknownFormulaBeforeWrongCoordinate"),
                (),
                model.Literal(value(model.UNIT_VALUE, model.UNIT)),
            ),
            (),
            evaluation_contract=combined_contract,
        )
        self.assertEqual(combined_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            combined_result.code,
            "K1-MALFORMED-EVALUATION-CONTRACT",
        )
        self.assertEqual(combined_result.charge, model.AbstractCharge())
        self.assertIsNone(combined_result.completion)

        for incompatible_regime in (
            model.IDENTITY_PROFILE_ID,
            model.PriorMetaId(
                model.FOUNDATION_PROFILE,
                model.SEMANTIC_REGIME_KIND,
                b"\x6f" * 32,
            ),
        ):
            with self.subTest(
                malformed_formula_before_contract_regime=(
                    incompatible_regime.subject_kind
                )
            ):
                malformed_before_regime = object.__new__(model.EvaluationContractV0)
                for field in (
                    "term_step_units",
                    "iteration_item_units",
                    "validation_precedence",
                    "completion_measure",
                    "static_bound_rule",
                    "primitive_cost_rules",
                ):
                    object.__setattr__(
                        malformed_before_regime,
                        field,
                        getattr(unknown_contract, field),
                    )
                object.__setattr__(
                    malformed_before_regime,
                    "semantic_regime",
                    incompatible_regime,
                )
                malformed_before_regime_result = model.Evaluator().evaluate(
                    model.CanonicalAlgorithm(
                        model.Symbol("MalformedFormulaBeforeContractRegime"),
                        (),
                        model.Literal(value(model.UNIT_VALUE, model.UNIT)),
                    ),
                    (),
                    evaluation_contract=malformed_before_regime,
                )
                self.assertEqual(
                    malformed_before_regime_result.outcome,
                    model.Outcome.MALFORMED,
                )
                self.assertEqual(
                    malformed_before_regime_result.code,
                    "K1-MALFORMED-EVALUATION-CONTRACT",
                )

        incompatible_contract = replace(
            model.DEFAULT_EVALUATION_CONTRACT,
            primitive_cost_rules=tuple(
                replace(rule, formula=incompatible_rule)
                if rule.primitive == projection_id
                else rule
                for rule in model.DEFAULT_EVALUATION_CONTRACT.primitive_cost_rules
            ),
        )
        evaluator = model.Evaluator(supported_contracts=(incompatible_contract,))
        result = evaluator.evaluate(
            model.build_lossy_projection_algorithm(),
            (value(model.BYTES_32, model.BytesValue(b"c" * 32)),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
            evaluation_contract=incompatible_contract,
            limits=replace(model.DEFAULT_LIMITS, maximum_result_bytes=0),
        )
        self.assertEqual(result.outcome, model.Outcome.REFUSED)
        self.assertEqual(result.code, "K1-REFUSED-PRIMITIVE-COST-ABI")
        self.assertEqual(result.charge, model.AbstractCharge())

        unused_id = model.PRIMITIVE_IDS_BY_KEY[("fixture.bytes.reverse", 1)]
        syntax_only_unused = replace(
            model.DEFAULT_EVALUATION_CONTRACT,
            primitive_cost_rules=tuple(
                replace(
                    rule,
                    formula=model.PrimitiveWorkFormulaV0(
                        model.Symbol("sum-byte-lengths"),
                        (999,),
                    ),
                )
                if rule.primitive == unused_id
                else rule
                for rule in model.DEFAULT_EVALUATION_CONTRACT.primitive_cost_rules
            ),
        )
        unused_evaluator = model.Evaluator(supported_contracts=(syntax_only_unused,))
        unused_result = unused_evaluator.evaluate(
            model.build_lossy_projection_algorithm(),
            (value(model.BYTES_32, model.BytesValue(b"u" * 32)),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
            evaluation_contract=syntax_only_unused,
        )
        self.assertEqual(unused_result.outcome, model.Outcome.COMPLETED)

        class ExplosiveTag(str):
            comparisons = 0

            def __eq__(self, _other: object) -> bool:
                ExplosiveTag.comparisons += 1
                raise AssertionError("host comparison must not execute")

            def __ne__(self, _other: object) -> bool:
                ExplosiveTag.comparisons += 1
                raise AssertionError("host comparison must not execute")

        with self.assertRaises(model.CanonicalError):
            replace(
                model.DEFAULT_EVALUATION_CONTRACT,
                validation_precedence=model.Symbol(
                    ExplosiveTag("portable-evaluation-precedence-v0")
                ),
            )
        self.assertEqual(ExplosiveTag.comparisons, 0)


class FailClosedOutcomeMatrixTest(unittest.TestCase):
    def test_malformed_typed_carriers_fail_closed(self) -> None:
        baseline = model.CanonicalAlgorithm(
            model.Symbol("CarrierShape"),
            (),
            model.Literal(value(model.UNIT_VALUE, model.UNIT)),
        )
        evaluator = model.Evaluator()
        missing_module_child = model.PrimitiveCall(
            model.PRIMITIVE_REFS_BY_KEY[("sha2-256", 1)],
            (),
        )

        malformed_algorithms = (
            replace(baseline, inputs=None),
            replace(
                baseline,
                term=model.Literal(
                    model.CanonicalValue(object(), model.UNIT)  # type: ignore[arg-type]
                ),
            ),
            replace(baseline, term=model.RecordConstruct(None)),
            replace(
                baseline,
                term=model.RecordConstruct((("not-an-ordinal", baseline.term),)),
            ),
            replace(
                baseline,
                term=model.RecordConstruct(
                    ((0, missing_module_child), (0, baseline.term))
                ),
            ),
            replace(baseline, term=model.Case(baseline.term, None)),
            replace(
                baseline,
                term=model.Case(
                    baseline.term,
                    ((1, missing_module_child), (0, baseline.term)),
                ),
            ),
            replace(
                baseline,
                term=model.SequenceConstruct(model.UNIT_VALUE, None, 0),
            ),
            replace(
                baseline,
                term=model.PrimitiveCall(
                    model.PRIMITIVE_REFS_BY_KEY[("sha2-256", 1)],
                    None,
                ),
            ),
            replace(
                baseline,
                term=model.Fail(object(), baseline.term, model.UNIT_VALUE),
            ),
            replace(
                baseline,
                term=model.Fail(
                    model.ZERO_DIVISOR_FAILURE,
                    baseline.term,
                    object(),
                ),
            ),
            replace(
                baseline,
                term=model.StrictIndex(
                    baseline.term,
                    baseline.term,
                    object(),
                ),
            ),
            replace(
                baseline,
                term=model.BoundedAppend(
                    baseline.term,
                    baseline.term,
                    object(),
                ),
            ),
        )
        for algorithm in malformed_algorithms:
            with self.subTest(term=type(algorithm.term).__name__):
                result = evaluator.evaluate(algorithm, ())
                self.assertEqual(result.outcome, model.Outcome.MALFORMED)
                self.assertEqual(result.code, "K1-MALFORMED-MODEL")

        incomplete_algorithm = object.__new__(model.CanonicalAlgorithm)
        incomplete_algorithm_result = evaluator.evaluate(
            incomplete_algorithm,
            (),
        )
        self.assertEqual(
            incomplete_algorithm_result.outcome,
            model.Outcome.MALFORMED,
        )
        self.assertEqual(
            incomplete_algorithm_result.code,
            "K1-MALFORMED-ALGORITHM-CARRIER",
        )

        with self.assertRaisesRegex(
            model.CanonicalError,
            "declaration kind must be an exact symbol",
        ):
            model.ValueDomain(
                model.SEMANTIC_REGIME_ID,
                model.Nat(0),  # type: ignore[arg-type]
                0,
            )

        malformed_domain = object.__new__(model.ValueDomain)
        object.__setattr__(malformed_domain, "owner", model.SEMANTIC_REGIME_ID)
        object.__setattr__(malformed_domain, "declaration_kind", model.Nat(0))
        object.__setattr__(malformed_domain, "local_ordinal", 0)
        malformed_value_type = object.__new__(model.ValueType)
        object.__setattr__(malformed_value_type, "domain", malformed_domain)
        object.__setattr__(malformed_value_type, "schema", model.UnitSchema())
        malformed_domain_algorithm = replace(
            baseline,
            inputs=(malformed_value_type,),
        )
        malformed_domain_result = evaluator.evaluate(
            malformed_domain_algorithm,
            (),
        )
        self.assertEqual(
            malformed_domain_result.outcome,
            model.Outcome.MALFORMED,
        )
        self.assertEqual(
            malformed_domain_result.code,
            "K1-MALFORMED-MODEL",
        )

        malformed_owner_domain = object.__new__(model.ValueDomain)
        object.__setattr__(
            malformed_owner_domain,
            "owner",
            malformed_content_id(model.FIXTURE_EXTENSION_MODULE_ID),
        )
        object.__setattr__(
            malformed_owner_domain,
            "declaration_kind",
            model.MODULE_VALUE_DOMAIN_KIND,
        )
        object.__setattr__(malformed_owner_domain, "local_ordinal", 0)
        malformed_owner_type = object.__new__(model.ValueType)
        object.__setattr__(malformed_owner_type, "domain", malformed_owner_domain)
        object.__setattr__(malformed_owner_type, "schema", model.UnitSchema())
        malformed_owner_result = evaluator.evaluate(
            replace(baseline, inputs=(malformed_owner_type,)),
            (),
        )
        self.assertEqual(malformed_owner_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(malformed_owner_result.code, "K1-MALFORMED-MODEL")

        malformed_root_domain = object.__new__(model.ValueDomain)
        object.__setattr__(
            malformed_root_domain,
            "owner",
            malformed_prior_meta_id(model.SEMANTIC_REGIME_ID),
        )
        object.__setattr__(
            malformed_root_domain,
            "declaration_kind",
            model.ROOT_VALUE_DOMAIN_KIND,
        )
        object.__setattr__(malformed_root_domain, "local_ordinal", 0)
        malformed_root_type = object.__new__(model.ValueType)
        object.__setattr__(malformed_root_type, "domain", malformed_root_domain)
        object.__setattr__(malformed_root_type, "schema", model.UnitSchema())
        malformed_root_result = evaluator.evaluate(
            replace(baseline, inputs=(malformed_root_type,)),
            (),
        )
        self.assertEqual(malformed_root_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(malformed_root_result.code, "K1-MALFORMED-MODEL")

        wrong_owner = model.content_id(
            "foundation.portable-algorithm",
            model.encode_datum(model.Symbol("wrong-value-domain-owner")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        wrong_owner_type = model.ValueType(
            model.ValueDomain(
                wrong_owner,
                model.MODULE_VALUE_DOMAIN_KIND,
                0,
            ),
            model.UnitSchema(),
        )
        wrong_owner_result = evaluator.evaluate(
            replace(baseline, inputs=(wrong_owner_type,)),
            (),
        )
        self.assertEqual(wrong_owner_result.outcome, model.Outcome.KIND_MISMATCH)
        self.assertEqual(wrong_owner_result.code, "K1-KIND-DECLARATION")

        wrong_owner_with_malformed_bundle = evaluator.evaluate(
            replace(baseline, inputs=(wrong_owner_type,)),
            (),
            modules={object(): object()},  # type: ignore[dict-item]
        )
        self.assertEqual(
            wrong_owner_with_malformed_bundle.outcome,
            model.Outcome.KIND_MISMATCH,
        )
        self.assertEqual(
            wrong_owner_with_malformed_bundle.code,
            "K1-KIND-DECLARATION",
        )

        malformed_inputs = evaluator.evaluate(baseline, None)  # type: ignore[arg-type]
        self.assertEqual(malformed_inputs.outcome, model.Outcome.MALFORMED)
        self.assertEqual(malformed_inputs.code, "K1-MALFORMED-INPUT-BUNDLE")

        input_algorithm = model.CanonicalAlgorithm(
            model.Symbol("IncompleteInputCarrier"),
            (model.UNIT_VALUE,),
            model.Variable(0, model.UNIT_VALUE),
        )
        missing_header = object.__new__(model.CanonicalValue)
        missing_header_result = evaluator.evaluate(
            input_algorithm,
            (missing_header,),
        )
        self.assertEqual(missing_header_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            missing_header_result.code,
            "K1-MALFORMED-INPUT-CARRIER",
        )

        missing_datum = object.__new__(model.CanonicalValue)
        object.__setattr__(missing_datum, "value_type", model.UNIT_VALUE)
        missing_datum_result = evaluator.evaluate(
            input_algorithm,
            (missing_datum,),
        )
        self.assertEqual(missing_datum_result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            missing_datum_result.code,
            "K1-MALFORMED-INPUT-CARRIER",
        )

        for supplied_modules in ([], object()):
            with self.subTest(modules=type(supplied_modules).__name__):
                malformed_modules = evaluator.evaluate(
                    baseline,
                    (),
                    modules=supplied_modules,  # type: ignore[arg-type]
                )
                self.assertEqual(malformed_modules.outcome, model.Outcome.MALFORMED)
                self.assertEqual(
                    malformed_modules.code,
                    "K1-MALFORMED-MODULE-BUNDLE",
                )

        required_module_value = evaluator.evaluate(
            model.build_lossy_projection_algorithm(),
            (value(model.BYTES_32, model.BytesValue(b"m" * 32)),),
            modules={model.FIXTURE_EXTENSION_MODULE_ID: object()},
        )
        self.assertEqual(required_module_value.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            required_module_value.code,
            "K1-MALFORMED-MODULE-PREIMAGE",
        )
        with self.assertRaises(model.ModelError):
            model.authenticate_primitive_declaration(object())  # type: ignore[arg-type]
        with self.assertRaises(model.ModelError):
            model.authenticate_semantic_failure_type(object())  # type: ignore[arg-type]
        with self.assertRaises(model.ModelError):
            model.module_declaration_catalogs(object())  # type: ignore[arg-type]
        with self.assertRaises(model.CanonicalError):
            model.authenticate_content_id(
                model.FIXTURE_EXTENSION_MODULE_ID,
                model.FIXTURE_EXTENSION_MODULE_CANDIDATE.body(),
                object(),  # type: ignore[arg-type]
            )

        class ChameleonInputs(tuple):
            reads = 0

            def __iter__(self):  # type: ignore[override]
                type(self).reads += 1
                return super().__iter__()

        unstable_inputs = ChameleonInputs(())
        rejected_inputs = evaluator.evaluate(baseline, unstable_inputs)
        self.assertEqual(rejected_inputs.outcome, model.Outcome.MALFORMED)
        self.assertEqual(rejected_inputs.code, "K1-MALFORMED-INPUT-BUNDLE")
        self.assertEqual(ChameleonInputs.reads, 0)

        class ChameleonModules(dict):
            reads = 0

            def get(self, key, default=None):  # type: ignore[override]
                type(self).reads += 1
                return super().get(key, default)

        unstable_modules = ChameleonModules(model.FIXTURE_MODULE_PREIMAGES)
        rejected_modules = evaluator.evaluate(
            model.build_lossy_projection_algorithm(),
            (value(model.BYTES_32, model.BytesValue(b"s" * 32)),),
            modules=unstable_modules,
        )
        self.assertEqual(rejected_modules.outcome, model.Outcome.MALFORMED)
        self.assertEqual(rejected_modules.code, "K1-MALFORMED-MODULE-BUNDLE")
        self.assertEqual(ChameleonModules.reads, 0)

        class DelegatingModules(dict):
            iterations = 0

            def __iter__(self):  # type: ignore[override]
                type(self).iterations += 1
                raise AssertionError("host iteration must not execute")

        delegated_proxy = MappingProxyType(
            DelegatingModules(dict(model.FIXTURE_MODULE_PREIMAGES))
        )
        rejected_proxy = evaluator.evaluate(
            model.build_lossy_projection_algorithm(),
            (value(model.BYTES_32, model.BytesValue(b"s" * 32)),),
            modules=delegated_proxy,
        )
        self.assertEqual(rejected_proxy.outcome, model.Outcome.MALFORMED)
        self.assertEqual(rejected_proxy.code, "K1-MALFORMED-MODULE-BUNDLE")
        self.assertEqual(DelegatingModules.iterations, 0)

        with (
            patch.object(model, "MAX_MODULE_BUNDLE_ENTRIES", 0),
            patch.object(
                model.SemanticModuleCandidate,
                "body",
                side_effect=AssertionError("oversized bundle was inspected"),
            ) as body,
        ):
            oversized_modules = evaluator.evaluate(
                model.build_lossy_projection_algorithm(),
                (value(model.BYTES_32, model.BytesValue(b"s" * 32)),),
                modules=dict(model.FIXTURE_MODULE_PREIMAGES),
            )
        self.assertEqual(
            oversized_modules.outcome,
            model.Outcome.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(
            oversized_modules.code,
            "K1-LIMIT-MODULE-BUNDLE-ENTRIES",
        )
        body.assert_not_called()

    def test_authenticated_host_subclasses_cannot_override_semantics(self) -> None:
        baseline = model.CanonicalAlgorithm(
            model.Symbol("ExactHostAlgorithm"),
            (),
            model.Literal(value(model.UNIT_VALUE, model.UNIT)),
        )

        class AlgorithmSubclass(model.CanonicalAlgorithm):
            function_type_reads = 0

            @property
            def function_type(self) -> model.SemanticFunctionType:
                type(self).function_type_reads += 1
                return model.SemanticFunctionType((), model.UNIT_VALUE, ())

        algorithm_subclass = AlgorithmSubclass(
            baseline.algorithm_kind,
            baseline.inputs,
            baseline.term,
            baseline.semantic_regime,
            baseline.diagnostic_label,
        )
        rejected_algorithm = model.Evaluator().evaluate(algorithm_subclass, ())
        self.assertEqual(rejected_algorithm.outcome, model.Outcome.MALFORMED)
        self.assertEqual(
            rejected_algorithm.code,
            "K1-MALFORMED-SUBJECT-CARRIER",
        )
        self.assertEqual(AlgorithmSubclass.function_type_reads, 0)

        class LiteralSubclass(model.Literal):
            pass

        rejected_term = model.Evaluator().evaluate(
            replace(
                baseline,
                term=LiteralSubclass(value(model.UNIT_VALUE, model.UNIT)),
            ),
            (),
        )
        self.assertEqual(rejected_term.outcome, model.Outcome.MALFORMED)
        self.assertEqual(rejected_term.code, "K1-MALFORMED-MODEL")

        projection = model.build_lossy_projection_algorithm()
        authentic_module = model.FIXTURE_EXTENSION_MODULE_CANDIDATE

        class ModuleSubclass(model.SemanticModuleCandidate):
            body_reads = 0

            def body(self) -> bytes:
                type(self).body_reads += 1
                return authentic_module.body()

        module_subclass = ModuleSubclass(
            authentic_module.diagnostic_label,
            authentic_module.imports,
            model.DatumSeq(()),
            authentic_module.domain_payload,
        )
        rejected_module = model.Evaluator().evaluate(
            projection,
            (value(model.BYTES_32, model.BytesValue(b"m" * 32)),),
            modules={model.FIXTURE_EXTENSION_MODULE_ID: module_subclass},
        )
        self.assertEqual(rejected_module.outcome, model.Outcome.MALFORMED)
        self.assertEqual(rejected_module.code, "K1-MALFORMED-MODULE-PREIMAGE")
        self.assertEqual(ModuleSubclass.body_reads, 0)

        class ContractSubclass(model.EvaluationContractV0):
            cost_reads = 0

            def cost_rule(
                self, primitive: model.TypedContentId
            ) -> model.PrimitiveWorkFormulaV0 | None:
                type(self).cost_reads += 1
                return model.PrimitiveWorkFormulaV0(model.Symbol("fixed"), (), 0)

        contract_subclass = ContractSubclass(
            model.DEFAULT_EVALUATION_CONTRACT.term_step_units,
            model.DEFAULT_EVALUATION_CONTRACT.iteration_item_units,
            model.DEFAULT_EVALUATION_CONTRACT.validation_precedence,
            model.DEFAULT_EVALUATION_CONTRACT.completion_measure,
            model.DEFAULT_EVALUATION_CONTRACT.static_bound_rule,
            model.DEFAULT_EVALUATION_CONTRACT.primitive_cost_rules,
            model.DEFAULT_EVALUATION_CONTRACT.semantic_regime,
        )
        with self.assertRaisesRegex(model.ModelError, "exact typed shape"):
            model.Evaluator(supported_contracts=(contract_subclass,))
        rejected_contract_request = model.Evaluator().evaluate(
            baseline,
            (),
            evaluation_contract=contract_subclass,
        )
        self.assertEqual(
            rejected_contract_request.outcome,
            model.Outcome.MALFORMED,
        )
        self.assertEqual(
            rejected_contract_request.code,
            "K1-MALFORMED-EVALUATION-CONTRACT",
        )
        self.assertEqual(
            rejected_contract_request.charge,
            model.AbstractCharge(),
        )
        self.assertIsNone(rejected_contract_request.completion)
        self.assertEqual(ContractSubclass.cost_reads, 0)

        class RegistryTupleSubclass(tuple):
            iterations = 0

            def __iter__(self):  # type: ignore[override]
                type(self).iterations += 1
                raise AssertionError("registry subclass must not be iterated")

        with self.assertRaisesRegex(model.ModelError, "exact tuple"):
            model.Evaluator(
                supported_primitives=RegistryTupleSubclass(
                    model.DEFAULT_SUPPORTED_PRIMITIVES
                )
            )
        with self.assertRaisesRegex(model.ModelError, "exact tuple"):
            model.Evaluator(
                supported_contracts=RegistryTupleSubclass(
                    (model.DEFAULT_EVALUATION_CONTRACT,)
                )
            )
        self.assertEqual(RegistryTupleSubclass.iterations, 0)

        with self.assertRaises(model.CanonicalError):
            model.Evaluator(
                supported_primitives=(
                    malformed_content_id(model.DEFAULT_SUPPORTED_PRIMITIVES[0]),
                ),
                supported_contracts=(),
            )
        wrong_registry_kind = model.content_id(
            "foundation.portable-algorithm",
            model.encode_datum(model.Symbol("wrong-registry-primitive-kind")),
            semantic_regime=model.SEMANTIC_REGIME_ID,
        )
        with self.assertRaisesRegex(model.ModelError, "wrong subject kind"):
            model.Evaluator(
                supported_primitives=(wrong_registry_kind,),
                supported_contracts=(),
            )

        with (
            patch.object(model, "MAX_EVALUATOR_REGISTRY_ENTRIES", 0),
            patch.object(
                model.TypedContentId,
                "internal_reference",
                side_effect=AssertionError("over-limit primitive was inspected"),
            ),
        ):
            with self.assertRaisesRegex(model.ModelError, "registry exceeds"):
                model.Evaluator(
                    supported_primitives=(model.DEFAULT_SUPPORTED_PRIMITIVES[0],),
                    supported_contracts=(),
                )
        with (
            patch.object(model, "MAX_EVALUATOR_REGISTRY_ENTRIES", 0),
            patch.object(
                model.EvaluationContractV0,
                "__post_init__",
                side_effect=AssertionError("over-limit contract was inspected"),
            ),
        ):
            with self.assertRaisesRegex(model.ModelError, "registry exceeds"):
                model.Evaluator(
                    supported_primitives=(),
                    supported_contracts=(model.DEFAULT_EVALUATION_CONTRACT,),
                )

        class FormulaSubclass(model.PrimitiveWorkFormulaV0):
            def measure(self, values: tuple[model.CanonicalValue, ...]) -> int:
                return 0

        formula_subclass = FormulaSubclass(model.Symbol("fixed"), (), 0)
        with self.assertRaisesRegex(model.ModelError, "formula.*exact shape"):
            replace(
                model.DEFAULT_EVALUATION_CONTRACT,
                primitive_cost_rules=(
                    model.PrimitiveCostRuleV0(
                        model.PRIMITIVE_IDS_BY_KEY[("sha2-256", 1)],
                        formula_subclass,
                    ),
                ),
            )

        primitive_key = ("fixture.bytes.prefix-27", 1)
        primitive_id = model.PRIMITIVE_IDS_BY_KEY[primitive_key]
        declaration = model.PRIMITIVE_DECLARATIONS[primitive_id]
        with self.assertRaises(TypeError):
            replace(
                declaration,
                derive_output=lambda _: model.BYTES_0_32,
            )

        frozen_tables = (
            (model.PRIMITIVE_CATALOG_BY_KEY, primitive_key),
            (model.PRIMITIVE_IDS_BY_KEY, primitive_key),
            (model.PRIMITIVE_REFS_BY_KEY, primitive_key),
            (model.PRIMITIVE_DECLARATIONS, primitive_id),
            (model.PRIMITIVE_DECLARATIONS_BY_KEY, primitive_key),
            (model._PRIMITIVE_TYPE_RULE_SUPPORT, primitive_id),
            (model.FIXTURE_FAILURE_TYPES_BY_ORDINAL, 0),
            (model.ROOT_VALUE_SCHEMA_CLASSES, 4),
            (model.FIXTURE_MODULE_PREIMAGES, model.FIXTURE_EXTENSION_MODULE_ID),
        )
        for table, key in frozen_tables:
            with self.subTest(frozen_table=table):
                with self.assertRaises(TypeError):
                    table[key] = table[key]  # type: ignore[index]

        projection_type = projection.function_type
        self.assertEqual(projection_type.output, model.BYTES_27)

        class CallbackRegistry:
            reads = 0

            def get(self, _key: object) -> object:
                CallbackRegistry.reads += 1
                raise AssertionError("host registry lookup must not execute")

            def __contains__(self, _key: object) -> bool:
                CallbackRegistry.reads += 1
                raise AssertionError("host support lookup must not execute")

        guarded_evaluator = model.Evaluator()
        contract_id = model.DEFAULT_EVALUATION_CONTRACT.identity
        with self.assertRaises(TypeError):
            guarded_evaluator.supported_contracts[contract_id] = object()  # type: ignore[index]
        with self.assertRaises(AttributeError):
            guarded_evaluator.supported_contracts = CallbackRegistry()  # type: ignore[assignment]
        with self.assertRaises(AttributeError):
            guarded_evaluator.supported_primitives = CallbackRegistry()  # type: ignore[assignment]
        self.assertEqual(CallbackRegistry.reads, 0)

    def test_encoded_input_admission_precedes_body_decode(self) -> None:
        malformed_body = b"\x03" + (2).to_bytes(8, "big") + b"\x00\x00"
        canonical_bytes = model.encode_datum(model.BytesValue(b"x" * 32))
        evaluator = model.Evaluator()

        malformed_algorithm = replace(
            model.build_lossy_projection_algorithm(),
            term=model.Variable(0, model.NAT_U64),
        )
        algorithm_first = evaluator.evaluate_encoded(
            malformed_algorithm,
            (model.EncodedValue(model.BYTES_32, malformed_body),),
        )
        self.assertEqual(algorithm_first.code, "K1-REFUSED-ALGORITHM-TYPING")

        projection = model.build_lossy_projection_algorithm()
        arity_first = evaluator.evaluate_encoded(
            projection,
            (
                model.EncodedValue(model.BYTES_32, canonical_bytes),
                model.EncodedValue(model.BYTES_32, malformed_body),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(arity_first.code, "K1-KIND-ARITY")

        type_first = evaluator.evaluate_encoded(
            projection,
            (model.EncodedValue(model.BYTES_0_32, malformed_body),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(type_first.code, "K1-KIND-INPUT")

        body_last = evaluator.evaluate_encoded(
            projection,
            (model.EncodedValue(model.BYTES_32, malformed_body),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(body_last.code, "K1-MALFORMED-CANONICAL-INPUT")

    def test_module_closure_precedes_encoded_body_after_structural_identity(
        self,
    ) -> None:
        projection = model.build_lossy_projection_algorithm()
        malformed_body = b"\x03" + (2).to_bytes(8, "big") + b"\x00\x00"
        malformed = model.Evaluator().evaluate_encoded(
            projection,
            (model.EncodedValue(model.BYTES_32, malformed_body),),
        )
        self.assertEqual(malformed.code, "K1-MISSING-MODULE")

        valid = model.Evaluator().evaluate_encoded(
            projection,
            (
                model.EncodedValue(
                    model.BYTES_32,
                    model.encode_datum(model.BytesValue(b"x" * 32)),
                ),
            ),
        )
        self.assertEqual(valid.code, "K1-MISSING-MODULE")

        authenticated_module = model.Evaluator().evaluate_encoded(
            projection,
            (model.EncodedValue(model.BYTES_32, malformed_body),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(authenticated_module.code, "K1-MALFORMED-CANONICAL-INPUT")

    def test_noncanonical_encoded_input_is_malformed(self) -> None:
        malformed_zero = b"\x03" + (2).to_bytes(8, "big") + b"\x00\x00"
        algorithm = model.build_mod_algorithm()
        result = model.Evaluator().evaluate_encoded(
            algorithm,
            (
                model.EncodedValue(model.NAT_U64, malformed_zero),
                model.EncodedValue(model.NAT_U64, model.encode_datum(model.Nat(1))),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(result.outcome, model.Outcome.MALFORMED)
        self.assertEqual(result.charge, model.AbstractCharge())

        outside_owner_schema = model.Nat(1 << 64)
        refused_encoded = model.Evaluator().evaluate_encoded(
            algorithm,
            (
                model.EncodedValue(
                    model.NAT_U64,
                    model.encode_datum(outside_owner_schema),
                ),
                model.EncodedValue(
                    model.NAT_U64,
                    model.encode_datum(model.Nat(1)),
                ),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(refused_encoded.outcome, model.Outcome.REFUSED)
        self.assertEqual(refused_encoded.code, "K1-REFUSED-INPUT-ADMISSION")
        self.assertEqual(refused_encoded.charge, model.AbstractCharge())

        refused_typed = model.Evaluator().evaluate(
            algorithm,
            (
                model.CanonicalValue(model.NAT_U64, outside_owner_schema),
                value(model.NAT_U64, model.Nat(1)),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(refused_typed.outcome, model.Outcome.REFUSED)
        self.assertEqual(refused_typed.code, "K1-REFUSED-INPUT-ADMISSION")
        self.assertEqual(refused_typed.charge, model.AbstractCharge())

    def test_canonical_input_precedes_support_and_support_precedes_preflight(
        self,
    ) -> None:
        algorithm = model.build_unsupported_algorithm()
        malformed_zero = b"\x03" + (2).to_bytes(8, "big") + b"\x00\x00"
        malformed = model.Evaluator().evaluate_encoded(
            algorithm,
            (model.EncodedValue(model.BYTES_0_32, malformed_zero),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
            limits=replace(model.DEFAULT_LIMITS, maximum_result_bytes=0),
        )
        self.assertEqual(malformed.code, "K1-MALFORMED-CANONICAL-INPUT")
        self.assertEqual(malformed.charge, model.AbstractCharge())

        supported_shape = model.Evaluator().evaluate_encoded(
            algorithm,
            (
                model.EncodedValue(
                    model.BYTES_0_32,
                    model.encode_datum(model.BytesValue(b"abc")),
                ),
            ),
            modules=model.FIXTURE_MODULE_PREIMAGES,
            limits=replace(model.DEFAULT_LIMITS, maximum_result_bytes=0),
        )
        self.assertEqual(supported_shape.outcome, model.Outcome.UNSUPPORTED)
        self.assertEqual(supported_shape.code, "K1-UNSUPPORTED-PRIMITIVE")
        self.assertEqual(supported_shape.charge, model.AbstractCharge())

    def test_wrong_input_domain_or_schema_is_kind_mismatch(self) -> None:
        algorithm = model.build_lossy_projection_algorithm()
        evaluator = model.Evaluator()
        result = evaluator.evaluate(
            algorithm,
            (value(model.BYTES_0_32, model.BytesValue(b"x" * 32)),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(result.outcome, model.Outcome.KIND_MISMATCH)

        class EqualityAlias:
            comparisons = 0

            def __eq__(self, _other: object) -> bool:
                EqualityAlias.comparisons += 1
                return True

            def __ne__(self, _other: object) -> bool:
                EqualityAlias.comparisons += 1
                return False

        class ExplosiveAlias:
            comparisons = 0

            def __eq__(self, _other: object) -> bool:
                ExplosiveAlias.comparisons += 1
                raise AssertionError("host comparison must not execute")

            def __ne__(self, _other: object) -> bool:
                ExplosiveAlias.comparisons += 1
                raise AssertionError("host comparison must not execute")

        canonical_body = model.BytesValue(b"x" * 32)
        encoded_body = model.encode_datum(canonical_body)
        for alias_type in (EqualityAlias, ExplosiveAlias):
            with self.subTest(alias=alias_type.__name__, carrier="canonical"):
                forged = evaluator.evaluate(
                    algorithm,
                    (
                        model.CanonicalValue(
                            alias_type(),  # type: ignore[arg-type]
                            canonical_body,
                        ),
                    ),
                    modules=model.FIXTURE_MODULE_PREIMAGES,
                )
                self.assertEqual(forged.outcome, model.Outcome.MALFORMED)
                self.assertEqual(forged.code, "K1-MALFORMED-INPUT-CARRIER")
            with self.subTest(alias=alias_type.__name__, carrier="encoded"):
                forged = evaluator.evaluate_encoded(
                    algorithm,
                    (
                        model.EncodedValue(
                            alias_type(),  # type: ignore[arg-type]
                            encoded_body,
                        ),
                    ),
                    modules=model.FIXTURE_MODULE_PREIMAGES,
                )
                self.assertEqual(forged.outcome, model.Outcome.MALFORMED)
                self.assertEqual(forged.code, "K1-MALFORMED-INPUT-CARRIER")
            self.assertEqual(alias_type.comparisons, 0)

        forged_value_type = object.__new__(model.ValueType)
        object.__setattr__(forged_value_type, "domain", ExplosiveAlias())
        object.__setattr__(
            forged_value_type,
            "schema",
            model.BytesSchema(32, 32),
        )
        for encoded in (False, True):
            with self.subTest(exact_value_type_with_bad_domain=encoded):
                if encoded:
                    forged = evaluator.evaluate_encoded(
                        algorithm,
                        (model.EncodedValue(forged_value_type, encoded_body),),
                        modules=model.FIXTURE_MODULE_PREIMAGES,
                    )
                else:
                    forged = evaluator.evaluate(
                        algorithm,
                        (model.CanonicalValue(forged_value_type, canonical_body),),
                        modules=model.FIXTURE_MODULE_PREIMAGES,
                    )
                self.assertEqual(forged.outcome, model.Outcome.MALFORMED)
                self.assertEqual(forged.code, "K1-MALFORMED-INPUT-CARRIER")
        self.assertEqual(ExplosiveAlias.comparisons, 0)

    def test_module_dependency_is_authenticated_before_execution(self) -> None:
        dependency = module("fixture.required")
        algorithm = model.build_module_dependent_algorithm(dependency.identity)
        missing = model.Evaluator().evaluate(algorithm, ())
        self.assertEqual(missing.outcome, model.Outcome.MISSING_DEPENDENCY)

        unsupported = model.Evaluator().evaluate(
            algorithm, (), modules={dependency.identity: dependency}
        )
        self.assertEqual(unsupported.outcome, model.Outcome.UNSUPPORTED)
        self.assertEqual(unsupported.code, "K1-UNSUPPORTED-VALUE-DOMAIN")
        self.assertEqual(unsupported.charge, model.AbstractCharge())

    def test_advertised_but_missing_implementation_is_checker_failure(self) -> None:
        evaluator = model.Evaluator(tuple(model.PRIMITIVE_DECLARATIONS))
        result = evaluator.evaluate(
            model.build_unsupported_algorithm(),
            (value(model.BYTES_0_32, model.BytesValue(b"abc")),),
            modules=model.FIXTURE_MODULE_PREIMAGES,
        )
        self.assertEqual(result.outcome, model.Outcome.CHECKER_FAILURE)

        foreign_owner = module("fixture.derived-abi-foreign")
        foreign_type = model.ValueType(
            model.ValueDomain(
                foreign_owner.identity,
                model.MODULE_VALUE_DOMAIN_KIND,
                0,
            ),
            model.BytesSchema(27, 27),
        )
        projection = model.build_lossy_projection_algorithm()
        with patch.object(
            model,
            "resolve_primitive_type_rule",
            return_value=lambda _arguments: foreign_type,
        ):
            derived_escape = model.Evaluator().evaluate(
                projection,
                (value(model.BYTES_32, model.BytesValue(b"d" * 32)),),
                modules=model.FIXTURE_MODULE_PREIMAGES,
            )
        self.assertEqual(
            derived_escape.outcome,
            model.Outcome.CHECKER_FAILURE,
        )
        self.assertEqual(derived_escape.code, "K1-CHECKER-DERIVED-ABI")
        self.assertEqual(derived_escape.charge, model.AbstractCharge())


if __name__ == "__main__":
    unittest.main()
