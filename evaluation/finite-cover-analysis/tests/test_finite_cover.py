from __future__ import annotations

from dataclasses import replace
from functools import lru_cache
import importlib.util
from pathlib import Path
import sys
import unittest
from unittest.mock import patch


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
EVALUATION_ROOT = PACKAGE_ROOT.parent
sys.path.insert(0, str(PACKAGE_ROOT))

import independent_oracle as oracle  # noqa: E402
import portable_arithmetic as portable  # noqa: E402


def _load(name: str, path: Path) -> object:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


k1 = _load(
    "_finite_cover_test_foundation",
    EVALUATION_ROOT / "k1-executable-foundations" / "reference_model.py",
)


def _transcript_datum(values: tuple[int, int, int, int]) -> object:
    return k1.DatumRecord(
        tuple((ordinal, k1.Nat(value)) for ordinal, value in enumerate(values))
    )


def _raw_pair_value(
    bundle: portable.PortableArithmeticBundle,
    first: tuple[int, int, int, int],
    second: tuple[int, int, int, int],
) -> object:
    return k1.admit_value(
        bundle.raw_pair_type,
        k1.DatumRecord(
            ((0, _transcript_datum(first)), (1, _transcript_datum(second)))
        ),
    )


class PortableArithmeticTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.bundle = portable.build_bundle(k1)
        cls.evaluator = portable.CheckedPortableEvaluator(k1, cls.bundle)

    def test_independent_oracle_matches_stream_and_candidate(self) -> None:
        count, digest, outputs = oracle.expected_result()
        self.assertEqual(count, 308)
        self.assertEqual(
            digest.hex(),
            "1d9472a4470c26748e864ea0b4b7383ee17ee4e83210a70a90fb03081532a3dd",
        )
        self.assertEqual(digest, self.bundle.representative_stream_digest)
        self.assertEqual(set(outputs), {3})

        emitted = []
        for state in range(309):
            state_value = k1.admit_value(
                self.bundle.stream_state_type, k1.Nat(state)
            )
            outcome = self.evaluator.evaluate(
                self.bundle.representative_stream_algorithm,
                (state_value,),
            )
            self.assertEqual(outcome.kind, "success")
            if state < 308:
                self.assertEqual(outcome.value.datum.case, 0)
                fields = dict(outcome.value.datum.payload.fields)
                emitted.append(fields[0])
                self.assertEqual(fields[1], k1.Nat(state + 1))
            else:
                self.assertEqual(outcome.value.datum.case, 1)
                fields = dict(outcome.value.datum.payload.fields)
                self.assertEqual(fields[0], k1.Nat(308))
                self.assertEqual(fields[1], k1.BytesValue(digest))
        self.assertEqual(tuple(emitted), self.bundle.representative_datums)

        for datum in emitted:
            representative = k1.admit_value(
                self.bundle.representative_pair_type, datum
            )
            embedded = self.evaluator.evaluate(
                self.bundle.embedding_algorithm, (representative,)
            )
            self.assertEqual(embedded.kind, "success")
            candidate = self.evaluator.evaluate(
                self.bundle.candidate_algorithm, (embedded.value,)
            )
            self.assertEqual(candidate.kind, "success")
            self.assertEqual(candidate.value.datum, k1.Nat(3))

    def test_noncanonical_members_factor_through_normalization(self) -> None:
        canonical = oracle.representative_stream()[0]
        first, second = canonical
        raw = _raw_pair_value(
            self.bundle,
            (
                first[0],
                first[1] + 23 * 257,
                first[2],
                first[3] + 11 * 257,
            ),
            (
                second[0],
                second[1] + 23 * 257,
                second[2],
                second[3] + 11 * 509,
            ),
        )
        normalized = self.evaluator.evaluate(
            self.bundle.normalization_algorithm, (raw,)
        )
        self.assertEqual(normalized.kind, "success")
        self.assertEqual(
            normalized.value.datum,
            self.bundle.representative_datums[0],
        )
        candidate = self.evaluator.evaluate(self.bundle.candidate_algorithm, (raw,))
        self.assertEqual(candidate.kind, "success")
        self.assertEqual(candidate.value.datum, k1.Nat(3))

    def test_evaluator_failure_partition_is_closed_and_distinct(self) -> None:
        with self.assertRaises(TypeError):
            self.bundle.module_preimages[self.bundle.module_id] = object()
        with self.assertRaises(TypeError):
            self.bundle.primitive_refs["natural.equal"] = object()

        representative = k1.admit_value(
            self.bundle.representative_pair_type,
            self.bundle.representative_datums[0],
        )
        embedded = self.evaluator.evaluate(
            self.bundle.embedding_algorithm, (representative,)
        ).value
        first = oracle.representative_stream()[0][0]
        zero_denominator = _raw_pair_value(self.bundle, first, first)

        self.assertEqual(
            self.evaluator.evaluate(
                self.bundle.candidate_algorithm, (zero_denominator,)
            ).kind,
            "domain-failure",
        )
        self.assertEqual(
            self.evaluator.evaluate(self.bundle.candidate_algorithm, ()).kind,
            "kind-mismatch",
        )
        self.assertEqual(
            self.evaluator.evaluate(
                self.bundle.candidate_algorithm, (object(),)
            ).kind,
            "malformed",
        )
        self.assertEqual(
            self.evaluator.evaluate(
                self.bundle.candidate_algorithm,
                (embedded,),
                module_preimages={},
            ).kind,
            "missing-dependency",
        )
        self.assertEqual(
            self.evaluator.evaluate(
                self.bundle.candidate_algorithm,
                (embedded,),
                limits=portable.PortableEvaluationLimits(
                    maximum_steps=0,
                    maximum_primitive_work=0,
                    maximum_result_bytes=0,
                ),
            ).kind,
            "deterministic-limit-exceeded",
        )

        literal = k1.Literal(k1.admit_value(k1.NAT_U64, k1.Nat(1)))
        widened = k1.PrimitiveCall(
            self.bundle.primitive_refs["natural.widen-u64"],
            (literal,),
        )
        unsupported = k1.CanonicalAlgorithm(
            k1.Symbol("test.unsupported-sequence"),
            (),
            k1.SequenceConstruct(k1.NAT_U64, (widened,), 1),
        )
        self.assertEqual(
            self.evaluator.evaluate(unsupported, ()).kind,
            "unsupported",
        )

        with patch.object(
            self.evaluator,
            "_evaluate_primitive",
            return_value=k1.admit_value(k1.NAT_U64, k1.Nat(3)),
        ):
            self.assertEqual(
                self.evaluator.evaluate(
                    self.bundle.candidate_algorithm, (embedded,)
                ).kind,
                "checker-failure",
            )


@lru_cache(maxsize=1)
def _analysis_context() -> tuple[object, object]:
    model = _load(
        "_finite_cover_test_analysis",
        EVALUATION_ROOT / "k3-analysis-closure" / "reference_model.py",
    )
    return model, model.establish_checked_fixed_extractor()


class AnalysisActivationTest(unittest.TestCase):
    def test_exact_hypothesis_free_judgment_and_certificate_boundary(self) -> None:
        model, checked = _analysis_context()
        proposition = model._formed_analysis_body(
            checked.proposition_id, "analysis.proposition"
        )
        hypothesis_context = model._formed_analysis_body(
            proposition.hypothesis_context_id,
            "analysis.hypothesis-context",
        )
        self.assertEqual(hypothesis_context.nodes, ())
        self.assertEqual(len(checked.certificate_judgment_ids), 3)
        self.assertEqual(len(set(checked.certificate_judgment_ids)), 3)
        self.assertEqual(checked.stream_receipt.exact_representative_count, 308)
        self.assertEqual(
            checked.stream_receipt.ordered_representative_stream_digest.hex(),
            "1d9472a4470c26748e864ea0b4b7383ee17ee4e83210a70a90fb03081532a3dd",
        )

        support = model._formed_analysis_body(
            checked.support_id, "analysis.support-instantiation"
        )
        entries = support.non_hypothesis_premise_bindings.values
        missing = replace(
            support,
            non_hypothesis_premise_bindings=model.k1.DatumSeq(entries[:2]),
        )
        with self.assertRaisesRegex(model.AuthorityError, "three exact certificates"):
            model._validate_finite_cover_certificate_bindings(missing)
        reordered = replace(
            support,
            non_hypothesis_premise_bindings=model.k1.DatumSeq(
                (entries[1], entries[0], entries[2])
            ),
        )
        with self.assertRaisesRegex(model.AuthorityError, "ordinal changed"):
            model._validate_finite_cover_certificate_bindings(reordered)

        judgment = model._formed_analysis_body(
            checked.judgment_id, "analysis.judgment-record"
        )
        validation = model._formed_analysis_body(
            checked.validation_basis_id, "analysis.validation-basis"
        )
        checker_entries = validation.admitted_checker_contract_ids_and_abis
        wrong_validation_id = model._analysis_id(
            "analysis.validation-basis",
            replace(
                validation,
                admitted_checker_contract_ids_and_abis=model.k1.DatumSeq(
                    checker_entries.values[:-1]
                ),
            ),
        )
        wrong_context = model._derive_qualification_subject_context(
            semantic_profile=model.ANALYSIS_PROPERTY_PROFILE,
            proposition_id=checked.proposition_id,
            semantic_basis_id=checked.semantic_basis_id,
            support_id=checked.support_id,
            validation_basis_id=wrong_validation_id,
            judgment_record=replace(
                judgment,
                validation_basis_id=model._id_datum(
                    wrong_validation_id, "analysis.validation-basis"
                ),
            ),
        )
        law = model._qualification_law(
            "finite-fixed-extractor-universal-result"
        )
        expectation = model._QualificationExpectation(
            checked.semantic_basis_id,
            checked.support_id,
            None,
            None,
            None,
            model.k1.DatumSeq(()),
        )
        with self.assertRaisesRegex(
            model.AuthorityError, "validation basis is not its exact constructor"
        ):
            model._require_exact_support_and_validation(
                law, wrong_context, expectation
            )

        conclusion = model._formed_analysis_body(
            checked.judgment_id, "analysis.judgment-record"
        ).exact_family_conclusion
        encoded = model.k1.encode_datum(conclusion)
        for forbidden in (
            b"efficiency",
            b"asymptotic",
            b"knowledge-soundness",
            b"fiat-shamir",
            b"rom-security",
            b"qrom",
        ):
            self.assertNotIn(forbidden, encoded)

    def test_stream_and_candidate_mutations_fail_closed(self) -> None:
        model, _ = _analysis_context()
        delegate = model.FINITE_COVER_PORTABLE_EVALUATOR

        class MutatingEvaluator:
            def __init__(self, mode: str) -> None:
                self.mode = mode

            def evaluate(self, algorithm: object, inputs: tuple[object, ...]) -> object:
                if algorithm is model.FINITE_COVER_ARITHMETIC.candidate_algorithm:
                    if self.mode == "false-candidate":
                        return model.finite_cover.PortableEvaluationResult(
                            "success",
                            model.k1.admit_value(
                                model.FINITE_COVER_ARITHMETIC.witness_type,
                                model.k1.Nat(4),
                            ),
                        )
                if algorithm is model.FINITE_COVER_ARITHMETIC.representative_stream_algorithm:
                    state = inputs[0].datum.value
                    if self.mode == "duplicate" and state == 1:
                        return delegate.evaluate(
                            algorithm,
                            (
                                model.k1.admit_value(
                                    model.FINITE_COVER_ARITHMETIC.stream_state_type,
                                    model.k1.Nat(0),
                                ),
                            ),
                        )
                    if self.mode == "premature-terminal" and state == 20:
                        return delegate.evaluate(
                            algorithm,
                            (
                                model.k1.admit_value(
                                    model.FINITE_COVER_ARITHMETIC.stream_state_type,
                                    model.k1.Nat(308),
                                ),
                            ),
                        )
                return delegate.evaluate(algorithm, inputs)

        cases = (
            ("duplicate", "duplicate, reordered, or has another successor"),
            ("premature-terminal", "terminal receipt disagrees"),
            ("false-candidate", "candidate failed its relation"),
        )
        for mode, message in cases:
            with self.subTest(mode=mode), patch.object(
                model,
                "FINITE_COVER_PORTABLE_EVALUATOR",
                MutatingEvaluator(mode),
            ):
                with self.assertRaisesRegex(model.AuthorityError, message):
                    model._run_finite_cover_stream()

        with self.assertRaises(model.k1.ValueAdmissionRefusedError):
            model.k1.admit_value(
                model.FINITE_COVER_ARITHMETIC.stream_state_type,
                model.k1.Nat(309),
            )


if __name__ == "__main__":
    unittest.main()
