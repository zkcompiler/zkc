from __future__ import annotations

from dataclasses import replace
import hashlib
from pathlib import Path
import sys
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(MODEL_ROOT))

from p01model.semantic import (  # noqa: E402
    COMMITMENT,
    STATEMENT,
    AlgebraProfile,
    TranscriptConstruction,
    _Shake128Duplex,
    _derive_cfrg_session_id,
    admit_algebra,
    admit_core,
    admit_fresh_realization,
    admit_protocol,
    admit_transcript_construction,
    canonical_core,
    canonical_transcript_construction,
    checked_fs_factorization,
    derive_fs_challenge,
    make_fresh_protocol,
    make_fs_protocol,
)
from p01model.terms import Outcome, Result, semantic_id  # noqa: E402


PROFILE = AlgebraProfile(p=23, q=11, generator=2, challenge_size=8)
APPLICATION_CONTEXT = "zkc/p01/test-session/alpha"
STATEMENT_VALUE = 13
COMMITMENT_VALUE = 16
RESPONSE_VALUE = 2


class SemanticResultAssertions(unittest.TestCase):
    def assert_result(
        self,
        checked: object,
        outcome: Outcome,
        boundary: str,
        code: str,
    ) -> Result:
        self.assertIsInstance(checked, Result)
        assert isinstance(checked, Result)
        self.assertEqual(checked.outcome, outcome)
        self.assertEqual(checked.boundary, boundary)
        self.assertEqual(checked.code, code)
        return checked


class CanonicalAdmissionAndVectorTest(SemanticResultAssertions):
    def setUp(self) -> None:
        self.profile = PROFILE
        self.core = canonical_core(self.profile)
        self.construction = canonical_transcript_construction(
            self.core, self.profile
        )
        self.fresh_protocol, self.fresh = make_fresh_protocol(
            self.core, self.profile
        )
        self.fs_protocol = make_fs_protocol(
            self.core, self.construction, self.profile
        )

    def test_canonical_fresh_fs_admission_and_factorization(self) -> None:
        checks = (
            (
                admit_algebra(self.profile),
                "algebra-profile",
                "P01-ALG-OK",
            ),
            (
                admit_core(self.core, self.profile),
                "core-admission",
                "P01-CORE-OK",
            ),
            (
                admit_fresh_realization(
                    self.fresh, self.core, self.profile
                ),
                "fresh-realization",
                "P01-FRESH-OK",
            ),
            (
                admit_transcript_construction(
                    self.construction,
                    self.core,
                    self.profile,
                    source_fresh=self.fresh,
                ),
                "transcript-construction",
                "P01-FS-OK",
            ),
            (
                admit_protocol(
                    self.fresh_protocol,
                    self.core,
                    self.profile,
                    fresh=self.fresh,
                ),
                "protocol-admission",
                "P01-PROTO-OK",
            ),
            (
                admit_protocol(
                    self.fs_protocol,
                    self.core,
                    self.profile,
                    construction=self.construction,
                ),
                "protocol-admission",
                "P01-PROTO-OK",
            ),
            (
                checked_fs_factorization(
                    self.fresh_protocol,
                    self.fs_protocol,
                    self.construction,
                    self.core,
                    self.profile,
                    self.fresh,
                ),
                "relations:fresh-fs-factorization",
                "P01-FACT-OK",
            ),
        )
        for checked, boundary, code in checks:
            with self.subTest(code=code):
                self.assert_result(
                    checked, Outcome.AFFIRMATIVE, boundary, code
                )

        self.assertEqual(
            self.fresh_protocol.core_id,
            self.fs_protocol.core_id,
        )
        self.assertEqual(
            self.fresh_protocol.honest_prover_contract_id,
            self.fs_protocol.honest_prover_contract_id,
        )
        self.assertNotEqual(
            self.fresh_protocol.identity,
            self.fs_protocol.identity,
        )
        self.assertEqual(
            self.construction.source_fresh_protocol_id,
            self.fresh_protocol.identity,
        )
        self.assertEqual(
            self.construction.source_fresh_realization_id,
            self.fresh.identity,
        )

    def test_frozen_p01_v3_transcript_and_proof_bytes(self) -> None:
        challenge, query, receipts = derive_fs_challenge(
            self.construction,
            self.profile,
            APPLICATION_CONTEXT,
            STATEMENT_VALUE,
            COMMITMENT_VALUE,
        )
        proof = self.profile.encode_group(
            COMMITMENT_VALUE
        ) + self.profile.encode_scalar(RESPONSE_VALUE)

        self.assertEqual(tuple(r["occurrence"] for r in receipts), (
            STATEMENT,
            COMMITMENT,
        ))
        self.assertEqual(len(query), 448)
        self.assertEqual(
            hashlib.sha256(query).hexdigest(),
            "ccb57bf733f23917e32f91edfefc8ff8"
            "2332bb30e36118f411f21caf874e4218",
        )
        self.assertEqual(challenge, 6)
        self.assertEqual(proof.hex(), "1002")

    def test_canonical_builder_rejects_non_mod_8_profile(self) -> None:
        unsupported = replace(self.profile, challenge_size=4)
        unsupported_core = canonical_core(unsupported)

        with self.assertRaisesRegex(ValueError, "exact mod-8 profile"):
            canonical_transcript_construction(
                unsupported_core,
                unsupported,
            )


class StrongFiatShamirNegativeMatrixTest(SemanticResultAssertions):
    def setUp(self) -> None:
        self.profile = PROFILE
        self.core = canonical_core(self.profile)
        self.construction = canonical_transcript_construction(
            self.core, self.profile
        )
        _, self.fresh = make_fresh_protocol(self.core, self.profile)

    def _admit(
        self,
        construction: TranscriptConstruction,
        *,
        source_fresh: object | None = None,
    ) -> Result:
        kwargs = (
            {}
            if source_fresh is None
            else {"source_fresh": source_fresh}
        )
        return admit_transcript_construction(
            construction,
            self.core,
            self.profile,
            **kwargs,
        )

    def test_required_source_and_transcript_contract_mutations_fail_closed(
        self,
    ) -> None:
        atoms = self.construction.atoms
        foreign_semantic_id = semantic_id(
            "p01.test.foreign-source-fresh-protocol.v1",
            {"case": "source-fresh-mutation"},
        )
        cases = (
            (
                "statement-omission",
                replace(self.construction, atoms=atoms[1:]),
                None,
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-prefix:challenge:c",
                "P01-FS-005",
                STATEMENT,
            ),
            (
                "commitment-omission",
                replace(self.construction, atoms=atoms[:1]),
                None,
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-prefix:challenge:c",
                "P01-FS-005",
                COMMITMENT,
            ),
            (
                "source-order",
                replace(self.construction, atoms=tuple(reversed(atoms))),
                None,
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-prefix:ordered-exactness:c",
                "P01-FS-006",
                None,
            ),
            (
                "source-kind",
                replace(
                    self.construction,
                    atoms=(
                        replace(atoms[0], source_kind="PriorProofMessage"),
                        atoms[1],
                    ),
                ),
                None,
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-atom:typed-occurrence-source",
                "P01-FS-007",
                None,
            ),
            (
                "source-codec",
                replace(
                    self.construction,
                    atoms=(
                        replace(atoms[0], codec="fixed-width-scalar.v1"),
                        atoms[1],
                    ),
                ),
                None,
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-atom:typed-occurrence-source",
                "P01-FS-007",
                None,
            ),
            (
                "framing",
                replace(self.construction, framing="raw-concatenation.v1"),
                None,
                Outcome.SEMANTIC_NEGATIVE,
                "transcript-framing:injectivity",
                "P01-FS-012",
                None,
            ),
            (
                "challenge-namespace",
                replace(
                    self.construction,
                    challenge_namespace="zkc/p01/schnorr/challenge/wrong",
                ),
                None,
                Outcome.SEMANTIC_NEGATIVE,
                "squeeze-sample:namespace",
                "P01-FS-011",
                None,
            ),
            (
                "decoder",
                replace(
                    self.construction,
                    decoder=replace(
                        self.construction.decoder,
                        squeeze_bytes=2,
                    ),
                ),
                None,
                Outcome.SEMANTIC_NEGATIVE,
                "squeeze-sample:decoder-contract",
                "P01-FS-025",
                None,
            ),
            (
                "source-fresh-protocol",
                replace(
                    self.construction,
                    source_fresh_protocol_id=foreign_semantic_id,
                ),
                self.fresh,
                Outcome.MISMATCH,
                "transcript-construction:source-public-coin-basis",
                "P01-FS-021",
                None,
            ),
            (
                "supplied-source-fresh-realization",
                self.construction,
                replace(
                    self.fresh,
                    conditional_kernel_contract_id=foreign_semantic_id,
                ),
                Outcome.SEMANTIC_NEGATIVE,
                "fresh-realization:public-coin-contract",
                "P01-FRESH-002",
                None,
            ),
        )

        for (
            name,
            construction,
            source_fresh,
            outcome,
            boundary,
            code,
            expected_source,
        ) in cases:
            with self.subTest(case=name):
                checked = self.assert_result(
                    self._admit(
                        construction,
                        source_fresh=source_fresh,
                    ),
                    outcome,
                    boundary,
                    code,
                )
                if expected_source is not None:
                    self.assertEqual(
                        checked.evidence["expected_source"],
                        expected_source,
                    )


class CfrgDraft03ByteExampleTest(unittest.TestCase):
    """Exact draft-03 bytes, not a claim of suite or draft conformance.

    These four regression examples are transcribed from Appendix B.2 of
    draft-irtf-cfrg-fiat-shamir-03.  They exercise only the two local private
    helpers named below; P01 remains an independent finite semantic witness.
    """

    SESSION_ID = bytes(range(32))

    def test_shake128_init_squeeze_example(self) -> None:
        state = _Shake128Duplex(self.SESSION_ID)
        self.assertEqual(
            state.squeeze(32).hex(),
            "63e1b3543377fab6fb8cf0f7698a9980"
            "ca0211d5bc4aba213dd7a6ef7dd63cfa",
        )

    def test_shake128_absorb_squeeze_example(self) -> None:
        state = _Shake128Duplex(self.SESSION_ID)
        state.absorb(b"hello world")
        self.assertEqual(
            state.squeeze(64).hex(),
            "f627ff348dfee50d2aa5918a2621a0c1"
            "daf74c7ef930d49b5ea6eae73455e8c7"
            "56d433cbde0ade711bdd55d7ed5de38b"
            "b9adea8b2eec4402a0df090c16371413",
        )

    def test_shake128_interleave_example(self) -> None:
        state = _Shake128Duplex(self.SESSION_ID)
        state.absorb(bytes(range(10)))
        first = state.squeeze(16)
        state.absorb(b"more data")
        second = state.squeeze(16)
        self.assertEqual(
            (first + second).hex(),
            "2da3c7e3a65c6e92901e8b668c43917e"
            "b9f02e9988e66d5ce2fbd833a0ecb93e",
        )

    def test_shake128_session_derivation_example(self) -> None:
        self.assertEqual(
            _derive_cfrg_session_id(b"interop-test-v00").hex(),
            "b508aca89eecac56cd33e4a28f817f43"
            "f849d035922f354173ae8466628308cf",
        )


if __name__ == "__main__":
    unittest.main()
