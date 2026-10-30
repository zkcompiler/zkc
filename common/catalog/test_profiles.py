"""Build-free controls for owner-fixed consumer profile formation."""

import copy
import json
from pathlib import Path
import unittest

from generate import unique, validate
from tablegen import project


def source():
    return json.loads(Path(__file__).with_name("declarations.json").read_text(), object_pairs_hook=unique)


def enroll(value, operation):
    value["operations"].append(operation)
    value["consumerProfiles"][0]["operations"].append({
        "operation": operation["name"],
        **{key: copy.deepcopy(operation[key]) for key in (
            "scope", "stage", "parameters", "signature", "requirements")},
    })


class Profiles(unittest.TestCase):
    def test_exact_primitive_abi(self):
        value = source()
        validate(value)
        profile = value["consumerProfiles"][0]
        self.assertEqual([m["operation"] for m in profile["operations"]], [
            "index.constant", "index.add", "index.sub", "index.mul", "index.div", "index.mod",
            "index.equal", "index.less", "vector.empty", "vector.length", "vector.sum",
            "vector.split", "vector.append", "vector.equal", "field.equal", "field.embed"])
        self.assertEqual(profile["implementation"], "unselected")
        for member in profile["operations"]:
            roots = [t["parameter"] for t in member["scope"] if t["kind"] == "root"]
            self.assertEqual(roots, [] if member["operation"].startswith("index.") else [
                {"kind": "Domain", "sort": "Field"}])
        self.assertEqual(project(value), project(value))

    def test_profile_refusals(self):
        cases = [
            ("old root schema", lambda v: v.pop("consumerProfiles")),
            ("unknown profile field", lambda v: v["consumerProfiles"][0].update(unexpected=True)),
            ("unknown member field", lambda v: v["consumerProfiles"][0]["operations"][0].update(unexpected=True)),
            ("unknown nested field", lambda v: v["consumerProfiles"][0]["operations"][0]["parameters"].update(unexpected=True)),
            ("empty identity", lambda v: v["consumerProfiles"][0].update(name="")),
            ("unknown operation", lambda v: v["consumerProfiles"][0]["operations"][0].update(operation="missing")),
            ("unknown constructor", lambda v: v["consumerProfiles"][0]["typeConstructors"].append("missing")),
            ("duplicate constructor", lambda v: v["consumerProfiles"][0]["typeConstructors"].append("field")),
            ("duplicate validator", lambda v: v["consumerProfiles"][0]["parameterValidators"].append("None")),
            ("unknown validator", lambda v: v["consumerProfiles"][0]["parameterValidators"].append("Unknown")),
            ("unsupported validator", lambda v: v["consumerProfiles"][0].update(parameterValidators=["None"])),
            ("unsupported type", lambda v: v["consumerProfiles"][0]["typeConstructors"].remove("field")),
            ("selected implementation", lambda v: v["consumerProfiles"][0].update(implementation="selected")),
            ("duplicate membership", lambda v: v["consumerProfiles"][0]["operations"].append(copy.deepcopy(v["consumerProfiles"][0]["operations"][0]))),
            ("duplicate profile", lambda v: v["consumerProfiles"].append(copy.deepcopy(v["consumerProfiles"][0]))),
        ]
        for label, mutate in cases:
            with self.subTest(label):
                value = source()
                mutate(value)
                with self.assertRaises(ValueError):
                    validate(value)

    def test_independently_well_formed_declaration_drift(self):
        for field, changed in [
            ("scope", [{"kind": "root", "name": "Other", "parameter": {"kind": "Domain", "sort": "Field"}}]),
            ("stage", "Construction"),
            ("parameters", {"validator": "Natural", "minimum": 1, "maximum": 1}),
            ("requirements", []),
            ("signature", {"kind": "fixed", "inputs": [], "outputs": [{"constructor": "bool", "arguments": []}]}),
        ]:
            for side in ("declaration", "consumer"):
                with self.subTest(field=field, side=side):
                    value = source()
                    op = next(o for o in value["operations"] if o["name"] == "field.equal")
                    member = next(m for m in value["consumerProfiles"][0]["operations"] if m["operation"] == "field.equal")
                    (op if side == "declaration" else member)[field] = changed
                    with self.assertRaisesRegex(ValueError, "consumer operation " + field + " mismatch"):
                        validate(value)

    def test_declaration_presence_does_not_enroll(self):
        value = source()
        profile = copy.deepcopy(value["consumerProfiles"])
        operation = copy.deepcopy(next(o for o in value["operations"] if o["name"] == "field.equal"))
        operation["name"] = "example.equal"
        value["operations"].append(operation)
        validate(value)
        self.assertEqual(value["consumerProfiles"], profile)

    def test_separate_owner_profile_is_explicit(self):
        value = source()
        original = copy.deepcopy(value["consumerProfiles"][0])
        other = copy.deepcopy(original)
        other["name"] = "example-primitives"
        other["operations"] = []
        operation = next(o for o in value["operations"] if o["name"] == "field.add")
        other["operations"].append({
            "operation": operation["name"],
            **{key: copy.deepcopy(operation[key]) for key in (
                "scope", "stage", "parameters", "signature", "requirements")},
        })
        value["consumerProfiles"].append(other)
        validate(value)
        project(value)
        self.assertEqual(value["consumerProfiles"][0], original)

    def test_closed_nested_type_dependencies(self):
        value = source()
        enroll(value, {
            "name": "example.nested", "scope": [
                {"kind": "root", "name": "F", "parameter": {"kind": "Domain", "sort": "Field"}},
                {"kind": "apply", "constructor": "field", "arguments": [0]},
                {"kind": "apply", "constructor": "sequence", "arguments": [1]},
            ], "stage": "Source", "parameters": {"validator": "None", "minimum": 0, "maximum": 0},
            "signature": {"kind": "fixed", "inputs": [{"term": 2}], "outputs": [{"term": 2}]},
            "requirements": [], "facets": [],
        })
        value["consumerProfiles"][0]["typeConstructors"].append("sequence")
        validate(value)
        # Keep only the nested operation to isolate its inner field dependency.
        value["consumerProfiles"][0]["operations"] = value["consumerProfiles"][0]["operations"][-1:]
        value["consumerProfiles"][0]["typeConstructors"].remove("field")
        with self.assertRaisesRegex(ValueError, "unsupported profile type constructor"):
            validate(value)

    def test_open_type_and_numerical_families_refuse(self):
        value = source()
        enroll(value, {
            "name": "example.open", "scope": [
                {"kind": "root", "name": "T", "parameter": {"kind": "Type", "sort": ""}}],
            "stage": "Source", "parameters": {"validator": "None", "minimum": 0, "maximum": 0},
            "signature": {"kind": "fixed", "inputs": [{"term": 0}], "outputs": [{"term": 0}]},
            "requirements": [], "facets": [],
        })
        with self.assertRaisesRegex(ValueError, "unsupported profile Type term"):
            validate(value)
        value = source()
        operation = next(o for o in value["operations"] if o["name"] == "numerical.map")
        value["consumerProfiles"][0]["operations"].append({
            "operation": operation["name"],
            **{key: copy.deepcopy(operation[key]) for key in (
                "scope", "stage", "parameters", "signature", "requirements")},
        })
        with self.assertRaisesRegex(ValueError, "unsupported profile signature family"):
            validate(value)


if __name__ == "__main__":
    unittest.main()
