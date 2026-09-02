from __future__ import annotations

from itertools import product
import json
import unittest

from oracle import canonical


ATOMS = (None, -1, 0, 1, "", "a", "~")


def _finite_values() -> tuple[object, ...]:
    """Enumerate the complete depth-one grammar used by these tests."""

    values: list[object] = list(ATOMS)
    values.extend([value] for value in ATOMS)
    values.extend([left, right] for left, right in product(ATOMS, repeat=2))
    values.extend({"a": value} for value in ATOMS)
    values.extend(
        {"a": left, "b": right} for left, right in product(ATOMS, repeat=2)
    )
    return tuple(values)


def _independent_spelling(value: object) -> str:
    if value is None:
        return "null"
    if type(value) is int:
        return str(value)
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=True)
    if isinstance(value, list):
        return "[" + ",".join(_independent_spelling(item) for item in value) + "]"
    if isinstance(value, dict):
        members = (
            _independent_spelling(key) + ":" + _independent_spelling(value[key])
            for key in sorted(value)
        )
        return "{" + ",".join(members) + "}"
    raise AssertionError(f"finite grammar produced unsupported value {value!r}")


class CanonicalPropertyTest(unittest.TestCase):
    def test_finite_grammar_roundtrips_and_matches_independent_spelling(self) -> None:
        values = _finite_values()
        self.assertEqual(119, len(values))
        for value in values:
            with self.subTest(value=value):
                encoded = canonical.canon_json(value)
                self.assertEqual(_independent_spelling(value), encoded)
                self.assertEqual(value, canonical.load_json(encoded))
                canonical.check_domain(value)

    def test_object_insertion_order_is_metamorphically_irrelevant(self) -> None:
        forward = {"a": [1, 0], "b": "x"}
        reverse = {"b": "x", "a": [1, 0]}
        self.assertEqual(canonical.canon_json(forward), canonical.canon_json(reverse))
        self.assertEqual(
            canonical.tagged_digest("test/order\n", forward),
            canonical.tagged_digest("test/order\n", reverse),
        )

    def test_domain_tag_mutation_changes_every_finite_observation(self) -> None:
        for value in _finite_values():
            with self.subTest(value=value):
                self.assertNotEqual(
                    canonical.tagged_digest("test/left\n", value),
                    canonical.tagged_digest("test/right\n", value),
                )

    def test_nesting_limit_accepts_boundary_and_refuses_next_level(self) -> None:
        boundary: object = None
        for _ in range(canonical.MAX_ATTR_DEPTH):
            boundary = [boundary]
        canonical.check_domain(boundary)
        with self.assertRaisesRegex(ValueError, "nesting exceeds"):
            canonical.check_domain([boundary])


if __name__ == "__main__":
    unittest.main()
