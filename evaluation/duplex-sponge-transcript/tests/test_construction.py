from __future__ import annotations

import copy
import json
from pathlib import Path
import sys
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(MODEL_ROOT))

from duplexmodel.construction import (  # noqa: E402
    construction_codec_biases,
    construction_id,
    core_id,
    finite_source_applicability,
    parse_construction,
    protocol_id,
)
from duplexmodel.diagnostics import (  # noqa: E402
    AdmissionRefusal,
    DeterministicLimitExceeded,
    MalformedInput,
    SourceApplicabilityRefusal,
)


CONSTRUCTION_PATH = REPO_ROOT / "evaluation/duplex-sponge-transcript/cases/construction.json"


def fixture() -> dict[str, object]:
    return json.loads(CONSTRUCTION_PATH.read_text(encoding="utf-8"))


class ConstructionTest(unittest.TestCase):
    def test_exact_construction_admits_and_reconstructs(self) -> None:
        construction = parse_construction(fixture())
        self.assertEqual(
            core_id(construction.core),
            "sha256:17ff7dabd605d44e493fa12b6807ac7d2a0489a8ec7b8af7b1fd9241a92c5fb5",
        )
        self.assertEqual(construction.body(), fixture()["construction"])

    def test_all_selected_decoders_are_total_and_unbiased(self) -> None:
        biases = construction_codec_biases(parse_construction(fixture()))
        self.assertEqual(set(biases), {"challenge-1", "challenge-2", "challenge-3"})
        self.assertTrue(all(value["numerator"] == 0 for value in biases.values()))

    def test_fresh_and_duplex_protocols_share_core_but_not_identity(self) -> None:
        construction = parse_construction(fixture())
        fresh = protocol_id(construction, "Fresh")
        duplex = protocol_id(construction, "DuplexSponge")
        self.assertNotEqual(fresh, duplex)
        self.assertIn(core_id(construction.core), construction.body().values())

    def test_noninjective_message_codec_is_structural_but_not_source_applicable(self) -> None:
        value = fixture()
        value["construction"]["message_codecs"][0]["codec"] = "PairFirstDuplicate"
        value["construction"]["message_codecs"][0][
            "algorithm"
        ] = "DuplicateFirstTupleSymbol"
        construction = parse_construction(value)
        with self.assertRaisesRegex(SourceApplicabilityRefusal, "not injective"):
            finite_source_applicability(construction)

    def test_variable_length_message_codec_is_refused(self) -> None:
        value = fixture()
        value["construction"]["message_codecs"][0]["codec"] = "PairDropZero"
        value["construction"]["message_codecs"][0][
            "algorithm"
        ] = "DropLeadingZeroSymbol"
        with self.assertRaisesRegex(AdmissionRefusal, "exact encoded length"):
            parse_construction(value)

    def test_wrong_declared_message_length_is_refused(self) -> None:
        value = fixture()
        value["construction"]["message_codecs"][2]["encoded_length"] = 2
        with self.assertRaisesRegex(AdmissionRefusal, "exact encoded length"):
            parse_construction(value)

    def test_partial_challenge_decoder_fails_source_applicability(self) -> None:
        value = fixture()
        value["construction"]["challenge_decoders"][1]["decoder"] = "PartialScalar"
        value["construction"]["challenge_decoders"][1][
            "algorithm"
        ] = "OnlySymbolExceptLastUndefined"
        construction = parse_construction(value)
        with self.assertRaisesRegex(SourceApplicabilityRefusal, "not total"):
            finite_source_applicability(construction)

    def test_decoder_returning_wrong_type_fails_source_applicability(self) -> None:
        value = fixture()
        value["construction"]["challenge_decoders"][0]["decoder"] = "PairAsScalar"
        value["construction"]["challenge_decoders"][0][
            "algorithm"
        ] = "FirstSymbolOnly"
        construction = parse_construction(value)
        with self.assertRaisesRegex(SourceApplicabilityRefusal, "wrong value type"):
            finite_source_applicability(construction)

    def test_biased_total_decoder_admits_but_rotates_identity(self) -> None:
        baseline = parse_construction(fixture())
        value = fixture()
        value["construction"]["challenge_decoders"][1]["decoder"] = "ConstantScalar"
        value["construction"]["challenge_decoders"][1][
            "algorithm"
        ] = "ConstantZero"
        mutated = parse_construction(value)
        finite_source_applicability(mutated)
        self.assertGreater(
            construction_codec_biases(mutated)["challenge-2"]["numerator"], 0
        )
        self.assertNotEqual(construction_id(baseline), construction_id(mutated))

    def test_missing_duplicate_and_reordered_maps_are_refused(self) -> None:
        for mutation in ("missing", "duplicate", "reordered"):
            with self.subTest(mutation=mutation):
                value = fixture()
                mappings = value["construction"]["message_codecs"]
                if mutation == "missing":
                    del mappings[1]
                elif mutation == "duplicate":
                    mappings[1] = copy.deepcopy(mappings[0])
                else:
                    mappings[0], mappings[1] = mappings[1], mappings[0]
                with self.assertRaisesRegex(AdmissionRefusal, "exact, total"):
                    parse_construction(value)

    def test_missing_duplicate_and_reordered_challenge_maps_are_refused(self) -> None:
        for mutation in ("missing", "duplicate", "reordered"):
            with self.subTest(mutation=mutation):
                value = fixture()
                mappings = value["construction"]["challenge_decoders"]
                if mutation == "missing":
                    del mappings[1]
                elif mutation == "duplicate":
                    mappings[1] = copy.deepcopy(mappings[0])
                else:
                    mappings[0], mappings[1] = mappings[1], mappings[0]
                with self.assertRaisesRegex(AdmissionRefusal, "exact, total"):
                    parse_construction(value)

    def test_nonbijective_provider_is_structural_but_not_source_applicable(self) -> None:
        value = fixture()
        value["construction"]["provider_semantics"]["permutation"]["matrix"][0] = [
            0,
            0,
            0,
            0,
            0,
        ]
        construction = parse_construction(value)
        with self.assertRaisesRegex(SourceApplicabilityRefusal, "not a permutation"):
            finite_source_applicability(construction)

    def test_execution_semantics_rotate_construction_and_duplex_identity(self) -> None:
        baseline = parse_construction(fixture())
        value = fixture()
        value["construction"]["provider_semantics"]["permutation"]["offset"][0] = 2
        changed = parse_construction(value)
        finite_source_applicability(changed)
        self.assertEqual(core_id(baseline.core), core_id(changed.core))
        self.assertEqual(
            protocol_id(baseline, "Fresh"), protocol_id(changed, "Fresh")
        )
        self.assertNotEqual(construction_id(baseline), construction_id(changed))
        self.assertNotEqual(
            protocol_id(baseline, "DuplexSponge"),
            protocol_id(changed, "DuplexSponge"),
        )

    def test_fixed_instance_projection_rejects_a_smaller_bound(self) -> None:
        value = fixture()
        value["construction"]["instance_bit_bound"] = 8
        with self.assertRaisesRegex(AdmissionRefusal, "fixed instance projection"):
            parse_construction(value)

    def test_oversized_decoder_enumeration_fails_fast_outside_admission(self) -> None:
        value = fixture()
        value["construction"]["challenge_decoders"][0]["squeeze_length"] = 16
        construction = parse_construction(value)
        with self.assertRaisesRegex(
            DeterministicLimitExceeded, "enumeration limit"
        ):
            finite_source_applicability(construction)

    def test_xor_mode_and_eager_law_are_refused(self) -> None:
        for key, replacement in (
            ("absorption_mode", "Xor"),
            ("absorb_law", "eager permutation at every filled rate segment"),
        ):
            with self.subTest(key=key):
                value = fixture()
                value["construction"][key] = replacement
                with self.assertRaisesRegex(AdmissionRefusal, key):
                    parse_construction(value)

    def test_inverse_provider_capability_is_not_execution_input(self) -> None:
        value = fixture()
        value["construction"]["provider_interface"].append("InversePermutation")
        with self.assertRaisesRegex(AdmissionRefusal, "wrong exact interface"):
            parse_construction(value)

    def test_caller_authored_skip_flag_is_malformed(self) -> None:
        value = fixture()
        value["construction"]["skip_message"] = "message-2"
        with self.assertRaisesRegex(MalformedInput, "keys differ"):
            parse_construction(value)

    def test_core_identity_mismatch_is_refused(self) -> None:
        value = fixture()
        value["construction"]["core_id"] = "sha256:" + "00" * 32
        with self.assertRaisesRegex(AdmissionRefusal, "Core other"):
            parse_construction(value)
