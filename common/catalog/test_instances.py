"""Build-free controls for the installed-instance tables and native installation.

The catalog generator validates the authored documents and runs the shared
validation cases. The data is then compared with independently authored Python
oracles, which are read here and never changed.
"""

import ast
import json
from pathlib import Path
import sys
import unittest

from generate import unique, validate, validate_installation
from tablegen import project
import validation_cases

ROOT = Path(__file__).resolve().parents[2]
SUPPORT = ROOT / "common/tests/support"
EVM = ROOT / "common/tests/evm"
sys.path.insert(0, str(SUPPORT))
import binomial_reference  # noqa: E402
import hash_chain_reference  # noqa: E402


def documents():
    here = Path(__file__).parent
    return tuple(
        json.loads((here / name).read_text(), object_pairs_hook=unique)
        for name in ("declarations.json", "installation.json")
    )


def find(rows, **fields):
    return next(r for r in rows if all(r[k] == v for k, v in fields.items()))


def domain(catalog, identity):
    return find(catalog["domains"], identity=identity)


def codec(catalog, kind, identity=""):
    return find(catalog["codecs"], kind=kind, domain=identity)


def member(row, name):
    return dict(row["members"]).get(name)


def refuses(test, mutate, expected):
    catalog, installation = documents()
    mutate(catalog, installation)
    with test.assertRaises(ValueError) as refusal:
        validate(catalog)
        validate_installation(installation, catalog)
    test.assertIn(expected, str(refusal.exception))


class Documents(unittest.TestCase):
    def test_authored_documents_validate_and_project(self):
        catalog, installation = documents()
        validate(catalog)
        validate_installation(installation, catalog)
        declarations, _, native = project(catalog, installation)
        self.assertNotIn("ZKC_NativeRepresentation", declarations)
        self.assertNotIn("ZKC_InstalledDomain", native)
        self.assertEqual(project(catalog, installation), project(catalog, installation))

    def test_unknown_and_missing_document_fields_refuse(self):
        # Document shapes the shared case edits cannot express; the shared case
        # list owns every rule of the two chapters.
        for label, mutate, expected in [
            ("unknown root table", lambda c, i: c.update(extra=[]), "unknown fields"),
            ("missing type column", lambda c, i: c["types"][0].pop("sourceData"), "missing fields"),
            ("unknown installation table", lambda c, i: i.update(extra=[]), "unknown fields"),
        ]:
            with self.subTest(label):
                refuses(self, mutate, expected)

    def test_shared_cases(self):
        # The same cases run against zkc-tblgen (compiler/test/catalog_source.py)
        # and the Rust build (crates/zkc-catalog/tests/validation_cases.rs).
        catalog, installation = documents()
        cases = validation_cases.load()
        for case in cases["accepted"]:
            with self.subTest(case["name"]):
                declarations, physical = validation_cases.apply(case["edits"], catalog, installation)
                validate(declarations)
                validate_installation(physical, declarations)
        for case in cases["refused"]:
            with self.subTest(case["name"]):
                declarations, physical = validation_cases.apply(case["edits"], catalog, installation)
                with self.assertRaises(ValueError) as refusal:
                    validate(declarations)
                    validate_installation(physical, declarations)
                self.assertIn(case["diagnostics"]["generator"], str(refusal.exception))


def literal(tree, name):
    """The literal value assigned to `name` anywhere in a module."""
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id == name for t in node.targets):
            return ast.literal_eval(node.value)
    raise AssertionError(f"oracle has no literal {name}")


def frame_calls(node, helper):
    """Literal tags passed to the oracle's frame-header helper under `node`."""
    return [call.args[0].value for call in ast.walk(node)
            if isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
            and call.func.id == helper and call.args
            and isinstance(call.args[0], ast.Constant)]


def function(tree, name):
    return next(node for node in ast.walk(tree)
                if isinstance(node, ast.FunctionDef) and node.name == name)


def labelled(tree, helper, label):
    """Tags in tuples whose first element is the literal `label`."""
    found = set()
    for node in ast.walk(tree):
        if (isinstance(node, ast.Tuple) and node.elts
                and isinstance(node.elts[0], ast.Constant) and node.elts[0].value == label):
            found.update(frame_calls(node, helper))
    return found


def evaluate(node, names):
    """Integer arithmetic over literals and named oracle constants."""
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.Name):
        return names[node.id]
    if isinstance(node, ast.BinOp):
        left, right = evaluate(node.left, names), evaluate(node.right, names)
        operators = {ast.Add: lambda a, b: a + b, ast.Pow: lambda a, b: a ** b,
                     ast.Sub: lambda a, b: a - b, ast.Mult: lambda a, b: a * b}
        return operators[type(node.op)](left, right)
    raise AssertionError("unsupported oracle expression")


class Oracles(unittest.TestCase):
    def setUp(self):
        self.catalog, self.installation = documents()
        self.tags = {row["tag"]: row for row in self.catalog["frameTags"]}

    def frame(self, kind, identity=""):
        return codec(self.catalog, kind, identity)["frame"]

    def aggregate(self, constructor, identity=""):
        return find(self.catalog["aggregateFrames"], constructor=constructor, domain=identity)["tag"]

    def structure(self, identity):
        return domain(self.catalog, identity)["field"]["structure"]

    def degree(self, identity):
        structure = self.structure(identity)
        return 1 if structure["kind"] == "prime" else structure["degree"]

    def prime_base(self, identity):
        while self.structure(identity)["kind"] == "extension":
            identity = member(domain(self.catalog, identity), "BaseField")
        return identity

    def test_wire_controls_fields(self):
        tree = ast.parse((EVM / "wire_controls.py").read_text())
        for identity, scalar, vector, width, degree, prime in literal(tree, "FIELDS"):
            with self.subTest(identity):
                self.assertEqual(self.frame("field", identity), {"tag": scalar, "elementBytes": width * degree})
                self.assertEqual(self.frame("vector", identity), {"tag": vector, "elementBytes": width * degree})
                self.assertEqual(self.degree(identity), degree)
                self.assertEqual(int(domain(self.catalog, identity)["field"]["characteristic"]), prime)
                base = self.frame("field", self.prime_base(identity))
                self.assertEqual(base["elementBytes"], width)

    def test_wire_controls_envelopes(self):
        tree = ast.parse((EVM / "wire_controls.py").read_text())
        for scheme, root, path, width, prime in literal(tree, "envelopes"):
            with self.subTest(scheme):
                self.assertEqual(self.frame("commitment", scheme)["tag"], root)
                self.assertEqual(self.frame("proof", scheme)["tag"], path)
                facts = domain(self.catalog, scheme)["commitment"]
                self.assertEqual(facts.get("digestWordBytes", 0), width)
                self.assertEqual(facts["digestBytes"], 32)
                if width:
                    self.assertEqual(self.tags[root]["layout"], "DigestRoot")
                    self.assertEqual(self.tags[path]["layout"], "DigestProof")
                    field = {"koala-bear.poseidon2-16": "koala-bear", "baby-bear.poseidon2-16": "baby-bear",
                             "goldilocks.poseidon2-8": "goldilocks"}[facts["permutation"]]
                    self.assertEqual(int(domain(self.catalog, field)["field"]["characteristic"]), prime)
                else:
                    self.assertEqual(facts["scheme"], "keccak256Rows")

    def test_wire_controls_structural_tags(self):
        tree = ast.parse((EVM / "wire_controls.py").read_text())
        self.assertEqual(frame_calls(function(tree, "sequence"), "head"), [self.aggregate("sequence")])
        self.assertEqual(frame_calls(function(tree, "variant"), "head"), [self.aggregate("variant")])
        self.assertEqual(frame_calls(function(tree, "indices"), "head"), [self.frame("indices")["tag"]])
        self.assertEqual(frame_calls(function(tree, "raw_bytes"), "head"), [self.frame("bytes")["tag"]])
        self.assertEqual(labelled(tree, "head", "index"), {self.frame("index")["tag"]})
        self.assertEqual(labelled(tree, "head", "bool"), {self.frame("bool")["tag"]})
        self.assertIn(self.aggregate("field_array", "bls12-381.fr"), frame_calls(tree, "head"))
        for tag in frame_calls(tree, "head"):
            self.assertIn(tag, self.tags)

    def test_foundation_controls(self):
        tree = ast.parse((EVM / "foundation_controls.py").read_text())
        for identity, (scalar, vector) in literal(tree, "TAGS").items():
            with self.subTest(identity):
                self.assertEqual(self.frame("field", identity)["tag"], scalar)
                self.assertEqual(self.frame("vector", identity)["tag"], vector)
        assignment = next(node for node in ast.walk(tree) if isinstance(node, ast.Assign)
                          and any(isinstance(t, ast.Name) and t.id == "FIELDS" for t in node.targets))
        names = {"BLS12_381_R": hash_chain_reference.BLS12_381_R}
        for key, call in zip(assignment.value.right.keys, assignment.value.right.values):
            identity = key.value
            with self.subTest(identity):
                keywords = {k.arg: evaluate(k.value, names) for k in call.keywords}
                self.assertEqual(evaluate(call.args[0], names), self.degree(identity))
                self.assertEqual(keywords["modulus"],
                                 int(domain(self.catalog, identity)["field"]["characteristic"]))
                self.assertEqual(keywords["coordinate_bytes"], self.frame("field", identity)["elementBytes"])
        self.assertEqual(frame_calls(function(tree, "sequence"), "frame"), [self.aggregate("sequence")])
        self.assertEqual(frame_calls(function(tree, "variant"), "frame"), [self.aggregate("variant")])
        self.assertEqual(frame_calls(function(tree, "raw_bytes"), "frame"), [self.frame("bytes")["tag"]])
        self.assertEqual(frame_calls(function(tree, "index_wire"), "frame"), [self.frame("index")["tag"]])

    def test_binomial_reference(self):
        for identity, field in binomial_reference.PLONKY3_FIELDS.items():
            with self.subTest(identity):
                row = domain(self.catalog, identity)
                structure = row["field"]["structure"]
                self.assertEqual(int(row["field"]["characteristic"]), field.modulus)
                self.assertEqual(self.degree(identity), field.degree)
                if field.degree > 1:
                    self.assertEqual(structure["over"], "BaseField")
                    self.assertEqual(structure["reduction"], [[0, str(field.nonresidue)]])
                base = self.frame("field", self.prime_base(identity))
                self.assertEqual(base["elementBytes"], field.coordinate_bytes)
                self.assertEqual(self.frame("field", identity)["elementBytes"],
                                 field.degree * field.coordinate_bytes)

    def test_hash_chain_reference(self):
        self.assertEqual(int(domain(self.catalog, "bls12-381.fr")["field"]["characteristic"]),
                         hash_chain_reference.BLS12_381_R)
        self.assertEqual(int(domain(self.catalog, "koala-bear")["field"]["characteristic"]),
                         hash_chain_reference.KOALA_BEAR_P)
        tree = ast.parse((SUPPORT / "hash_chain_reference.py").read_text())
        assignment = next(node for node in ast.walk(function(tree, "vectors"))
                          if isinstance(node, ast.Assign) and any(
                              isinstance(t, ast.Name) and t.id == "instances" for t in node.targets))
        services = {row["contract"]: row["field"] for row in self.catalog["randomServices"]}
        decoders = {"fr64be": hash_chain_reference.BLS_SUITE}
        for element in assignment.value.elts:
            suite = getattr(hash_chain_reference, element.elts[0].id)
            contract, degree = element.elts[1].value, element.elts[3].value
            with self.subTest(suite):
                row = domain(self.catalog, suite)
                self.assertEqual(row["transcript"]["family"], "hash-chain")
                self.assertEqual(row["transcript"]["hash"], "keccak256")
                self.assertTrue(row["transcript"]["bindsSuite"])
                self.assertIs(hash_chain_reference.suite_hash(suite), hash_chain_reference.keccak256)
                challenge = member(row, "ChallengeField")
                self.assertEqual(services[contract], challenge)
                self.assertEqual(self.degree(challenge), degree)
                if suite in decoders.values():
                    self.assertEqual(row["transcript"]["decoder"], "fr64be")
        for name in ("BLS_SUITE", "OCTIC_SUITE", "QUARTIC_SUITE"):
            suite = getattr(hash_chain_reference, name)
            row = domain(self.catalog, suite)
            self.assertEqual(row["transcript"]["family"], "hash-chain")
            challenge = member(row, "ChallengeField")
            prime = self.structure(challenge)["kind"] == "prime"
            self.assertEqual(row["transcript"]["decoder"], "fr64be" if prime else "rejection31le")


if __name__ == "__main__":
    unittest.main()
