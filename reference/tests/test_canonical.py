from __future__ import annotations

import unittest

from oracle import canonical, model


class CanonicalBoundaryTest(unittest.TestCase):
    def test_model_facade_preserves_canonical_public_objects(self) -> None:
        self.assertIs(model.Refusal, canonical.Refusal)
        self.assertIs(model.canon_json, canonical.canon_json)
        self.assertIs(model.tagged_digest, canonical.tagged_digest)
        self.assertIs(model.load_json, canonical.load_json)
        self.assertIs(model.check_domain, canonical.check_domain)

    def test_canonical_spelling_and_digest_are_stable(self) -> None:
        value = {"z": [2, 1], "a": "x"}
        self.assertEqual(canonical.canon_json(value), '{"a":"x","z":[2,1]}')
        self.assertEqual(
            canonical.tagged_digest("test/domain\n", value),
            "sha256:464efc3746aee5753271768a5df9c120278e5c4f35fe796d88dee3c4a6699a63",
        )

    def test_loader_refuses_ambiguous_or_noninteger_json(self) -> None:
        for document in ('{"x":1,"x":2}', '{"x":1.5}', '{"x":NaN}'):
            with self.subTest(document=document):
                with self.assertRaises(canonical.Refusal):
                    canonical.load_json(document)

    def test_attribute_domain_keeps_bool_and_integer_distinct(self) -> None:
        canonical.check_domain({"n": 1})
        with self.assertRaisesRegex(ValueError, "booleans"):
            canonical.check_domain({"n": True})


if __name__ == "__main__":
    unittest.main()
