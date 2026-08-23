from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = MODEL_ROOT.parents[1]
sys.path.insert(0, str(MODEL_ROOT))

from r2model.frigrind import (
    BASE_FIXTURE,
    BASE_HASH,
    BOUND_FIXTURE,
    BOUND_HASH,
    EXTERNAL_FRESH_FILE,
    EXTERNAL_FRESH_HASH,
    INVOCATION_FILE,
    INVOCATION_HASH,
    FreshTapeOrigin,
    _load_json,
    base_scenario,
    load_external_fresh,
    load_fixture,
    load_invocation,
)


EXPECTED_DIGESTS = {
    BASE_FIXTURE: "cf2e4effc006cae253a77a9f8e0a0d0a3fe024bf3d6af99a75801d4b4765426a",
    BOUND_FIXTURE: "317258c54a4b8dad0308f552adc2bf0f8ec4fc72ecc5dc765f4ad206c9503858",
    INVOCATION_FILE: "f61a560d3671b924c76031de2b50b5d1f0a1dc65dfef83d45fc9b4f1a643269a",
    EXTERNAL_FRESH_FILE: "297f5d518d516f12b6994684f66b263a0db5ec5e3d49d9319fc416e2f9de7425",
}


class SourceFidelityV3Test(unittest.TestCase):
    """Frozen-source fidelity and semantic-binding checks for the v3 witness."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = load_fixture(REPO_ROOT)
        cls.companion = load_fixture(REPO_ROOT, companion=True)
        cls.invocation = load_invocation(REPO_ROOT)
        cls.scenario = base_scenario(cls.fixture)
        cls.external_tape, cls.external_nonce = load_external_fresh(
            REPO_ROOT,
            cls.scenario.core,
        )

    def test_frozen_sources_have_exact_content_hashes(self) -> None:
        declared = {
            BASE_FIXTURE: BASE_HASH,
            BOUND_FIXTURE: BOUND_HASH,
            INVOCATION_FILE: INVOCATION_HASH,
            EXTERNAL_FRESH_FILE: EXTERNAL_FRESH_HASH,
        }
        self.assertEqual(declared, EXPECTED_DIGESTS)
        for relative_path, expected_digest in EXPECTED_DIGESTS.items():
            with self.subTest(source=str(relative_path)):
                raw = (REPO_ROOT / relative_path).read_bytes()
                self.assertEqual(hashlib.sha256(raw).hexdigest(), expected_digest)

        self.assertEqual(self.fixture.sha256, EXPECTED_DIGESTS[BASE_FIXTURE])
        self.assertEqual(self.companion.sha256, EXPECTED_DIGESTS[BOUND_FIXTURE])
        self.assertEqual(
            self.invocation.source_document_id,
            f"sha256:{EXPECTED_DIGESTS[INVOCATION_FILE]}",
        )
        self.assertEqual(
            self.external_tape.source_id,
            f"sha256:{EXPECTED_DIGESTS[EXTERNAL_FRESH_FILE]}",
        )

    def test_fixture_names_and_companion_preamble_are_exact(self) -> None:
        self.assertEqual(self.fixture.payload["name"], "frigrind")
        self.assertEqual(self.companion.payload["name"], "frigrind-bound")
        self.assertEqual(
            self.companion.payload["preamble"],
            [{"label": "air_id", "class": "rs", "anchor": "contract"}],
        )

    def test_invocation_schema_binding_and_nonce_interval_are_exact(self) -> None:
        payload = json.loads(
            (REPO_ROOT / INVOCATION_FILE).read_text(encoding="utf-8")
        )
        self.assertEqual(payload["schema"], "zkc.r2.frigrind-invocation.v2")
        self.assertEqual(payload["source_fixture_sha256"], BASE_HASH)
        self.assertEqual(payload["g1_strategy"], "copy_statement")
        self.assertEqual(self.invocation.default_search.term(), {"start": 0, "limit": 1_000_000})
        self.assertEqual(self.invocation.source_fixture_id, f"sha256:{BASE_HASH}")

    def test_external_fresh_support_point_has_no_execution_dependency(self) -> None:
        payload = json.loads(
            (REPO_ROOT / EXTERNAL_FRESH_FILE).read_text(encoding="utf-8")
        )
        self.assertEqual(payload["schema"], "zkc.r2.frigrind-external-fresh.v1")
        self.assertEqual(payload["source_fixture_sha256"], BASE_HASH)
        self.assertIs(self.external_tape.origin, FreshTapeOrigin.EXTERNAL_FIXTURE)
        self.assertIsNone(self.external_tape.dependency_execution_id)
        self.assertEqual(self.external_nonce.term(), {"nonce": payload["fixed_nonce"]})
        self.assertEqual(
            [vector.term() for vector in self.external_tape.vectors],
            [
                {"challenge": occurrence, "values": values}
                for occurrence, values in payload["coin_vectors"].items()
            ],
        )

    def test_json_loader_rejects_duplicate_keys_after_exact_hash_check(self) -> None:
        raw = b'{"schema":"v3","schema":"duplicate"}'
        exact_digest = hashlib.sha256(raw).hexdigest()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "duplicate.json"
            path.write_bytes(raw)
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), exact_digest)
            with self.assertRaisesRegex(ValueError, "duplicate JSON key: schema"):
                _load_json(path, exact_digest)


if __name__ == "__main__":
    unittest.main()
