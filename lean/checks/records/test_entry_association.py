"""Source alias scope uses the same checked interface association as binding."""

from copy import deepcopy
import unittest

from . import reports


class EntryAssociationTests(unittest.TestCase):
    def setUp(self):
        self.item = {
            "request": {"subject": {"entry": "admitted_protocol"}},
            "source_entry": "example::Proof",
            "entry_association": {
                "source_entry": "example::Proof",
                "protocol": "admitted_protocol",
                "interface_digest": "sha256:" + "a" * 64,
                "attribution": "trusted-frontend-checked-interface",
            },
        }
        self.source = {"entries": ["example::Proof"], "claims": [self.item]}
        self.scope = {"entries": ["example::Proof"], "selection": "explicit"}

    def test_checked_alias_populates_source_scope(self):
        self.assertEqual(reports.scope_reasons(self.source, self.scope), [])
        self.assertEqual(reports.source_entry(self.item), ("example::Proof", []))

    def test_legacy_exact_entry_needs_no_alias(self):
        item = {"request": {"subject": {"entry": "same_entry"}}}
        self.assertEqual(reports.source_entry(item), ("same_entry", []))

    def test_alias_without_association_refuses(self):
        del self.item["entry_association"]
        self.assertTrue(reports.scope_reasons(self.source, self.scope))

    def test_crossed_protocol_refuses(self):
        self.item["request"]["subject"]["entry"] = "another_protocol"
        self.assertTrue(reports.scope_reasons(self.source, self.scope))

    def test_crossed_source_alias_refuses(self):
        self.item["entry_association"]["source_entry"] = "other::Proof"
        self.assertTrue(reports.scope_reasons(self.source, self.scope))

    def test_malformed_interface_attribution_refuses(self):
        for key, value in [("interface_digest", "not-a-digest"),
                           ("interface_digest", "a" * 64),
                           ("interface_digest", None),
                           ("attribution", "kernel-correspondence")]:
            with self.subTest(key=key, value=value):
                item = deepcopy(self.item)
                item["entry_association"][key] = value
                self.assertTrue(reports.source_entry(item)[1])

    def test_valid_alias_cannot_enter_another_scope(self):
        scope = {"entries": ["admitted_protocol"], "selection": "explicit"}
        source = {**self.source, "entries": ["admitted_protocol"]}
        self.assertTrue(reports.scope_reasons(source, scope))

    def test_selected_alias_still_requires_claims(self):
        self.assertTrue(reports.scope_reasons({**self.source, "claims": []}, self.scope))


if __name__ == "__main__":
    unittest.main()
