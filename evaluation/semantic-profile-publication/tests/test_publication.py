from __future__ import annotations

import copy
import json
from pathlib import Path
import unittest

import independent as cold
import reference_model as ref


ROOT = Path(__file__).resolve().parents[3]


class SemanticProfilePublicationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.reference = ref.compile_repository()
        cls.independent = cold.compile_repository()
        cls.manifests = ref.load_repository_manifests()

    def assert_both_refuse(
        self,
        *,
        manifests: dict[str, dict[str, object]] | None = None,
        pages: dict[str, bytes] | None = None,
    ) -> None:
        with self.assertRaises(ref.PublicationError):
            ref.compile_repository(
                manifest_overrides=manifests,
                page_overrides=pages,
            )
        with self.assertRaises(cold.ColdError):
            cold.compile_repository(
                manifest_overrides=manifests,
                page_overrides=pages,
            )

    def owner_page(self, key: str) -> tuple[str, bytes]:
        path = self.manifests[key]["owner_page"]
        assert type(path) is str
        return path, (ROOT / path).read_bytes()

    def test_cold_foundation_reconstruction_matches_selected_basis(self) -> None:
        self.assertEqual(ref.verify_foundation_source(), cold.foundation_record())
        self.assertEqual(
            cold.foundation_record(),
            {
                "identity_profile_digest": "0764186d53048eb619e79783581331dd7ef7c3939215b8000239c94768237ac1",
                "hash_suite_digest": "c24b580c31bf26bf314e746c87a93cb7ff61d3c33880fbd0ad8e31b307110805",
                "semantic_regime_digest": "0c537a1d1638992bd0c3efd2256ed4c3506ecb96bb6136b6084189de10b86bef",
                "semantic_core_law_length": 45933,
                "semantic_core_law_sha256": "f603cee6ce7acc601ca92a35b3de3787dcd9b9ea47a85486c8f4fb2732212658",
            },
        )

    def test_independent_compilers_agree_on_complete_artifacts(self) -> None:
        self.assertEqual(
            self.reference.topological_order,
            self.independent.topological_order,
        )
        for key in ref.PROFILE_KEYS:
            with self.subTest(profile=key):
                reference = self.reference.profiles[key]
                independent = self.independent.profiles[key]
                self.assertEqual(reference.body_bytes, independent.body_bytes)
                self.assertEqual(
                    reference.profile_id.internal_reference(),
                    independent.identifier.ref(),
                )
                self.assertEqual(
                    reference.direct_import_keys,
                    independent.direct_import_keys,
                )
                self.assertEqual(
                    reference.direct_import_uses,
                    independent.direct_import_uses,
                )
                self.assertEqual(
                    self.reference.exact_closure(key),
                    self.independent.exact_closure(key),
                )
        self.assertEqual(
            ref.identity_table(self.reference),
            cold.identity_table(self.independent),
        )

    def test_published_identity_table_is_reproduced_not_trusted(self) -> None:
        published = json.loads(
            (ROOT / "docs-next/pir/profiles/published-identities.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(published, ref.identity_table(self.reference))
        self.assertEqual(published, cold.identity_table(self.independent))

    def test_source_fragments_are_stored_once_and_not_copied_into_law_source(self) -> None:
        for key, artifact in self.reference.profiles.items():
            with self.subTest(profile=key):
                for fragment in artifact.source_fragments.values():
                    self.assertEqual(artifact.body_bytes.count(fragment), 1)
                    self.assertNotIn(fragment, artifact.profile.semantic_law_source)
                self.assertNotIn(artifact.profile_id.digest, artifact.body_bytes)

    def test_build_coordinates_are_not_identity_bearing(self) -> None:
        manifest = copy.deepcopy(self.manifests["interaction"])
        old_path, page = self.owner_page("interaction")
        moved_path = "docs-next/pir/profiles/moved-interaction-owner.md"
        manifest["owner_page"] = moved_path
        moved = ref.compile_repository(
            manifest_overrides={"interaction": manifest},
            page_overrides={moved_path: page},
        )
        cold_moved = cold.compile_repository(
            manifest_overrides={"interaction": manifest},
            page_overrides={moved_path: page},
        )
        self.assertEqual(
            moved.profiles["interaction"].body_bytes,
            self.reference.profiles["interaction"].body_bytes,
        )
        self.assertEqual(
            cold_moved.profiles["interaction"].body_bytes,
            self.independent.profiles["interaction"].body_bytes,
        )
        self.assertNotIn(old_path.encode("utf-8"), moved.profiles["interaction"].body_bytes)
        for source in manifest["fragments"]:
            self.assertNotIn(
                source["start"].encode("ascii"),
                moved.profiles["interaction"].body_bytes,
            )

    def test_text_outside_selected_fragments_does_not_rotate_identity(self) -> None:
        path, page = self.owner_page("canonical-framed-fiat-shamir")
        changed = b"<!-- nonsemantic relocated-page prefix -->\n" + page
        reference = ref.compile_repository(page_overrides={path: changed})
        independent = cold.compile_repository(page_overrides={path: changed})
        self.assertEqual(
            ref.identity_table(reference), ref.identity_table(self.reference)
        )
        self.assertEqual(
            cold.identity_table(independent), cold.identity_table(self.independent)
        )

    def test_interaction_change_rotates_every_dependent_profile(self) -> None:
        path, page = self.owner_page("interaction")
        old = b"Old bytes are never reinterpreted."
        new = b"Old bytes are never reinterpreted under this source edition."
        self.assertIn(old, page)
        changed_page = page.replace(old, new, 1)
        changed = ref.compile_repository(page_overrides={path: changed_page})
        cold_changed = cold.compile_repository(page_overrides={path: changed_page})
        for key in ref.PROFILE_KEYS:
            with self.subTest(profile=key):
                self.assertNotEqual(
                    changed.profiles[key].profile_id,
                    self.reference.profiles[key].profile_id,
                )
                self.assertNotEqual(
                    cold_changed.profiles[key].identifier,
                    self.independent.profiles[key].identifier,
                )

    def test_sibling_change_is_local(self) -> None:
        path, page = self.owner_page("canonical-framed-fiat-shamir")
        old = b"The construction body does not repeat a `core_id` outside field 0"
        new = b"The construction body never repeats a `core_id` outside field 0"
        self.assertIn(old, page)
        changed_page = page.replace(old, new, 1)
        changed = ref.compile_repository(page_overrides={path: changed_page})
        cold_changed = cold.compile_repository(page_overrides={path: changed_page})
        for key in ref.PROFILE_KEYS:
            should_rotate = key == "canonical-framed-fiat-shamir"
            with self.subTest(profile=key):
                self.assertEqual(
                    changed.profiles[key].body_bytes
                    != self.reference.profiles[key].body_bytes,
                    should_rotate,
                )
                self.assertEqual(
                    cold_changed.profiles[key].body_bytes
                    != self.independent.profiles[key].body_bytes,
                    should_rotate,
                )

    def test_public_setup_change_rotates_only_its_descendants(self) -> None:
        path, page = self.owner_page("public-setup")
        old = b"The entries are every and only"
        new = b"The entries are exactly every and only"
        self.assertIn(old, page)
        changed_page = page.replace(old, new, 1)
        changed = ref.compile_repository(page_overrides={path: changed_page})
        cold_changed = cold.compile_repository(page_overrides={path: changed_page})
        rotated = {"public-setup", "commitment-opening", "oracle-commitment"}
        for key in ref.PROFILE_KEYS:
            with self.subTest(profile=key):
                self.assertEqual(
                    changed.profiles[key].body_bytes
                    != self.reference.profiles[key].body_bytes,
                    key in rotated,
                )
                self.assertEqual(
                    cold_changed.profiles[key].body_bytes
                    != self.independent.profiles[key].body_bytes,
                    key in rotated,
                )

    def test_missing_and_surplus_direct_imports_refuse(self) -> None:
        missing = copy.deepcopy(self.manifests["commitment-opening"])
        missing["expected_imports"] = ["interaction"]
        self.assert_both_refuse(manifests={"commitment-opening": missing})

        surplus = copy.deepcopy(self.manifests["public-setup"])
        surplus["expected_imports"] = [
            "canonical-framed-fiat-shamir",
            "interaction",
        ]
        self.assert_both_refuse(manifests={"public-setup": surplus})

    def test_profile_import_cycle_refuses_before_hashing(self) -> None:
        cyclic = copy.deepcopy(self.manifests["interaction"])
        cyclic["expected_imports"] = ["canonical-framed-fiat-shamir"]
        self.assert_both_refuse(manifests={"interaction": cyclic})

    def test_unresolved_imported_declaration_refuses(self) -> None:
        changed = copy.deepcopy(self.manifests["commitment-opening"])
        dependency = changed["definitions"][0]["dependencies"][0]
        dependency["name"] = "unknown-public-setup-compiler"
        self.assert_both_refuse(manifests={"commitment-opening": changed})

    def test_public_setup_consumer_cannot_omit_its_direct_use(self) -> None:
        changed = copy.deepcopy(self.manifests["commitment-opening"])
        for definition in changed["definitions"]:
            definition["dependencies"] = [
                dependency
                for dependency in definition["dependencies"]
                if dependency["profile"] != "public-setup"
            ]
        self.assert_both_refuse(manifests={"commitment-opening": changed})

    def test_absent_selector_and_unreachable_definition_refuse(self) -> None:
        absent = copy.deepcopy(self.manifests["duplex-sponge-fiat-shamir"])
        absent["definitions"][0]["selector"] = "NoSuchDuplexBodyCompiler"
        self.assert_both_refuse(
            manifests={"duplex-sponge-fiat-shamir": absent}
        )

        unreachable = copy.deepcopy(self.manifests["interaction"])
        unreachable["definitions"].append(
            {
                "kind": "pir.semantic-law",
                "name": "unused-law-v0",
                "revision": 0,
                "fragment": "interaction-kernel",
                "selector": "## 4. Parties, inputs, values, and scopes",
                "dependencies": [],
            }
        )
        self.assert_both_refuse(manifests={"interaction": unreachable})

    def test_subject_rows_must_equal_supported_kinds(self) -> None:
        changed = copy.deepcopy(self.manifests["interaction"])
        changed["subjects"] = changed["subjects"][:-1]
        self.assert_both_refuse(manifests={"interaction": changed})

    def test_source_fragments_cannot_overlap_across_manifests(self) -> None:
        changed = copy.deepcopy(self.manifests["public-setup"])
        interaction_fragment = self.manifests["interaction"]["fragments"][2]
        changed["fragments"][0]["start"] = interaction_fragment["start"]
        changed["fragments"][0]["end"] = interaction_fragment["end"]
        self.assert_both_refuse(manifests={"public-setup": changed})

    def test_expected_identity_or_copied_law_field_cannot_enter_source(self) -> None:
        for field in ("expected_profile_id", "semantic_law_source"):
            with self.subTest(field=field):
                changed = copy.deepcopy(self.manifests["interaction"])
                changed[field] = "forbidden"
                self.assert_both_refuse(manifests={"interaction": changed})

    def test_marker_and_text_normalization_fail_closed(self) -> None:
        path, page = self.owner_page("canonical-framed-fiat-shamir")
        marker = b"<!-- zkc-profile-source:canonical-framed-fs-semantics:start -->\n"
        self.assertEqual(page.count(marker), 1)

        missing = page.replace(marker, b"<!-- missing-source-marker -->\n", 1)
        self.assert_both_refuse(pages={path: missing})

        repeated = page + marker
        self.assert_both_refuse(pages={path: repeated})

        trailing = page.replace(
            b"The construction body does not repeat a `core_id` outside field 0 or store\n",
            b"The construction body does not repeat a `core_id` outside field 0 or store \n",
            1,
        )
        self.assertNotEqual(trailing, page)
        self.assert_both_refuse(pages={path: trailing})

        decomposed = page.replace(
            b"The construction body does not repeat",
            "The construction e\u0301 body does not repeat".encode("utf-8"),
            1,
        )
        self.assert_both_refuse(pages={path: decomposed})

        cr_bearing = page.replace(
            b"## Appendix A. Canonical bodies\n",
            b"## Appendix A. Canonical bodies\r\n",
            1,
        )
        self.assert_both_refuse(pages={path: cr_bearing})

        no_blank_before_end = page.replace(
            b"\n\n<!-- zkc-profile-source:canonical-framed-fs-semantics:end -->\n",
            b"\n<!-- zkc-profile-source:canonical-framed-fs-semantics:end -->\n",
            1,
        )
        self.assertNotEqual(no_blank_before_end, page)
        self.assert_both_refuse(pages={path: no_blank_before_end})

    def test_missing_family_parameter_in_fs_receipt_refuses(self) -> None:
        path, page = self.owner_page("canonical-framed-fiat-shamir")
        changed = page.replace(
            b"CanonicalValue<declared challenge type>",
            b"CanonicalValue<ConcreteChallengeType>",
            1,
        )
        self.assertNotEqual(changed, page)
        self.assert_both_refuse(pages={path: changed})

    def test_concrete_core_coordinate_in_fs_receipt_refuses(self) -> None:
        path, page = self.owner_page("canonical-framed-fiat-shamir")
        changed = page.replace(
            b"FSChallengeReceipt = {\n",
            b"FSChallengeReceipt = {\n  forbidden_core_id: CoreId,\n",
            1,
        )
        self.assertNotEqual(changed, page)
        self.assert_both_refuse(pages={path: changed})

    def test_concrete_core_coordinate_in_duplex_auxiliary_receipt_refuses(self) -> None:
        path, page = self.owner_page("duplex-sponge-fiat-shamir")
        changed = page.replace(
            b"DuplexInitializationReceipt = {\n",
            b"DuplexInitializationReceipt = {\n  forbidden_core_id: CoreId,\n",
            1,
        )
        self.assertNotEqual(changed, page)
        self.assert_both_refuse(pages={path: changed})

    def test_complete_bodies_stay_within_constitutional_limit(self) -> None:
        for key, artifact in self.reference.profiles.items():
            with self.subTest(profile=key):
                self.assertLessEqual(len(artifact.body_bytes), ref.k1.MAX_CANONICAL_BYTES)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
