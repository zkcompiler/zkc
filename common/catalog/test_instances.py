"""Build-free controls for the installed-instance tables and native installation.

The catalog generator validates the authored documents and refuses forged rows.
The data is then compared with independently authored Python oracles, which are
read here and never changed.
"""

import ast
import copy
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


# Each forged document breaks one rule of the declaration or installation
# chapters; the generator must refuse it with the named diagnostic.
DECLARATION_MUTATIONS = [
    ("unknown root table", lambda c, i: c.update(extra=[]), "unknown fields"),
    ("missing type column", lambda c, i: c["types"][0].pop("sourceData"), "missing fields"),
    ("collection rank", lambda c, i: find(c["types"], name="matrix")["collection"].update(rank=3),
     "collection rank"),
    ("parameter element without a parameter",
     lambda c, i: find(c["types"], name="bytes")["collection"].update(element="parameter"),
     "parameter collection element"),
    ("unknown setup role", lambda c, i: find(c["types"], name="prover_key").update(setup="both"),
     "unknown declaration alternative"),
    ("duplicate domain identity", lambda c, i: c["domains"].append(copy.deepcopy(c["domains"][0])),
     "duplicate domain identity"),
    ("identity shared by a domain and a codec",
     lambda c, i: codec(c, "bool").update(identity="koala-bear"),
     "duplicate identity across domains and codecs"),
    ("invalid identity", lambda c, i: domain(c, "edwards25519.prime").update(identity="1edwards"),
     "invalid catalog identity"),
    ("Slot domain", lambda c, i: domain(c, "edwards25519.prime").update(sort="Slot"),
     "invalid domain sort"),
    ("member sort mismatch",
     lambda c, i: domain(c, "edwards25519.prime")["members"].__setitem__(0, ["Scalar", "ristretto255.group"]),
     "domain member sort mismatch"),
    ("member of another sort",
     lambda c, i: domain(c, "ristretto255.group")["members"].append(["BaseField", "koala-bear"]),
     "is not a member of sort Group"),
    ("duplicate member",
     lambda c, i: domain(c, "koala-bear.ext4-binomial3")["members"].append(["BaseField", "koala-bear"]),
     "duplicate domain member"),
    ("capability over another sort",
     lambda c, i: domain(c, "bn254.g1")["capabilities"].append("Field"),
     "is not a unary predicate over Group"),
    ("capabilities not closed under rules",
     lambda c, i: domain(c, "koala-bear")["capabilities"].remove("Field"),
     "not closed under rules"),
    ("pairing groups not distinct",
     lambda c, i: domain(c, "bls12-381.fr")["members"].__setitem__(1, ["PairingG2", "bls12-381.g1"]),
     "distinct pairing groups"),
    ("pairing group with another scalar",
     lambda c, i: domain(c, "bn254.g2")["members"].__setitem__(0, ["Scalar", "bls12-381.fr"]),
     "pairing group must act"),
    ("evaluation field on a row commitment",
     lambda c, i: domain(c, "rows.merkle-keccak256.koala-bear/0")["members"].append(["PointField", "koala-bear"]),
     "PointField and EvaluationField"),
    ("characteristic one", lambda c, i: domain(c, "gf2-64.pentanomial-4-3-1")["field"].update(characteristic="1"),
     "invalid characteristic"),
    ("CharacteristicNotTwo in characteristic two",
     lambda c, i: domain(c, "gf2-64.pentanomial-4-3-1")["capabilities"].append("CharacteristicNotTwo"),
     "CharacteristicNotTwo disagrees"),
    ("prime structure without PrimeField",
     lambda c, i: domain(c, "ristretto255.scalar")["capabilities"].remove("PrimeField"),
     "PrimeField disagrees"),
    ("prime structure holding ExtensionField",
     lambda c, i: domain(c, "koala-bear")["capabilities"].append("ExtensionField"),
     "ExtensionField disagrees"),
    ("extension structure without ExtensionField",
     lambda c, i: domain(c, "koala-bear.ext4-binomial3")["capabilities"].remove("ExtensionField"),
     "ExtensionField disagrees"),
    ("reduction exponents out of order",
     lambda c, i: domain(c, "gf2-64.pentanomial-4-3-1")["field"]["structure"]["reduction"].reverse(),
     "strictly decrease"),
    ("reduction exponent at the degree",
     lambda c, i: domain(c, "koala-bear.ext4-binomial3")["field"]["structure"].update(reduction=[[4, "3"]]),
     "reaches the degree"),
    ("empty reduction",
     lambda c, i: domain(c, "koala-bear.ext4-binomial3")["field"]["structure"].update(reduction=[]),
     "reduction is a nonempty list"),
    ("zero reduction coefficient",
     lambda c, i: domain(c, "koala-bear.ext4-binomial3")["field"]["structure"].update(reduction=[[0, "0"]]),
     "nonzero prime-subfield"),
    ("BaseField member over the prime subfield",
     lambda c, i: domain(c, "gf2-64.pentanomial-4-3-1")["members"].append(["BaseField", "koala-bear"]),
     "exactly the rows over BaseField have a BaseField member"),
    ("base field of another characteristic",
     lambda c, i: domain(c, "goldilocks.ext2-binomial7")["members"].__setitem__(0, ["BaseField", "baby-bear"]),
     "BaseField has another characteristic"),
    ("convention on an extension",
     lambda c, i: domain(c, "koala-bear.ext4-binomial3")["field"].update(
         twoAdic=copy.deepcopy(domain(c, "koala-bear")["field"]["twoAdic"])),
     "belongs to a prime row"),
    ("two-adicity beyond 64",
     lambda c, i: domain(c, "koala-bear")["field"]["twoAdic"].update(twoAdicity=65),
     "between 1 and 64"),
    ("maximal root outside the field",
     lambda c, i: domain(c, "koala-bear")["field"]["twoAdic"].update(maximalRoot="2130706433"),
     "not a field element"),
    ("duplicate convention",
     lambda c, i: domain(c, "baby-bear")["field"]["twoAdic"].update(
         convention=domain(c, "koala-bear")["field"]["twoAdic"]["convention"]),
     "duplicate coset convention"),
    ("TwoAdicField without a convention",
     lambda c, i: domain(c, "bls12-381.fr")["capabilities"].append("TwoAdicField"),
     "TwoAdicField disagrees"),
    ("hash on a Merlin suite",
     lambda c, i: domain(c, "merlin3.bls12-381.fr64be/0")["transcript"].update(hash="keccak256"),
     "keccak256 hash exactly for hash-chain"),
    ("transcript without FieldTranscript",
     lambda c, i: domain(c, "merlin3.bls12-381.fr64be/0")["capabilities"].remove("FieldTranscript"),
     "requires Transcript and FieldTranscript"),
    ("wide decoder over an extension challenge",
     lambda c, i: domain(c, "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0")["transcript"].update(
         decoder="fr64be"),
     "requires a prime challenge field"),
    ("31-bit rejection over Goldilocks",
     lambda c, i: domain(c, "merlin3.goldilocks.ext2-binomial7.rejection64le/0")["transcript"].update(
         decoder="rejection31le"),
     "characteristic is too large"),
    ("commitment without ValueField",
     lambda c, i: domain(c, "rows.merkle-keccak256.koala-bear/0").update(members=[]),
     "requires ValueField"),
    ("short row digest",
     lambda c, i: domain(c, "rows.merkle-keccak256.koala-bear/0")["commitment"].update(digestBytes=16),
     "32-byte digests"),
    ("permutation over another field",
     lambda c, i: domain(c, "rows.merkle-poseidon2-16.koala-bear/0")["commitment"].update(
         permutation="baby-bear.poseidon2-16"),
     "permutation field"),
    ("digest word width",
     lambda c, i: domain(c, "rows.merkle-poseidon2-16.koala-bear/0")["commitment"].update(digestWordBytes=8),
     "digest word width"),
    ("logical type over another sort",
     lambda c, i: c["logicalTypes"].append({"kind": "field", "domain": "bn254.g1"}),
     "invalid logical type instance"),
    ("duplicate logical type",
     lambda c, i: c["logicalTypes"].append(copy.deepcopy(c["logicalTypes"][0])),
     "duplicate logical type instance"),
    ("resource unit logical type",
     lambda c, i: c["logicalTypes"].append({"kind": "resource_unit", "domain": ""}),
     "invalid logical type constructor"),
    ("setup key over a row commitment",
     lambda c, i: c["logicalTypes"].append({"kind": "prover_key", "domain": "rows.merkle-keccak256.koala-bear/0"}),
     "setup keys exist only"),
    ("tag zero", lambda c, i: c["frameTags"][0].update(tag=0), "invalid or duplicate frame tag"),
    ("codec over an unadmitted type",
     lambda c, i: c["codecs"].append(
         {"identity": "zkcv.point.koala-bear/0", "kind": "point", "domain": "koala-bear", "frame": None}),
     "codec payload is not an admitted logical type"),
    ("second codec for one type",
     lambda c, i: c["codecs"].append(dict(copy.deepcopy(codec(c, "bool")), identity="zkcv.bool/1")),
     "second codec for one logical type"),
    ("codec kind without its predicate",
     lambda c, i: c["codecs"].append({"identity": "zkcv.opening_state.multilinear-kzg/0",
                                      "kind": "opening_state", "domain": "multilinear.kzg.bls12-381/0",
                                      "frame": None}),
     "lacks its Encodes predicate"),
    ("message codec without a frame", lambda c, i: codec(c, "bool").update(frame=None),
     "a message codec requires a frame"),
    ("frame on a non-message codec",
     lambda c, i: (c["frameTags"].append({"tag": 3, "layout": "Scalar", "shared": None}),
                   codec(c, "polynomial", "koala-bear").update(frame={"tag": 3, "elementBytes": 4})),
     "only the input-only table frame"),
    ("frame fields disagree with the layout",
     lambda c, i: codec(c, "field", "koala-bear").update(frame={"tag": 19}),
     "frame fields disagree"),
    ("element width disagrees with the structure",
     lambda c, i: codec(c, "field", "koala-bear")["frame"].update(elementBytes=8),
     "element width disagrees"),
    ("codec frame with an aggregate layout",
     lambda c, i: codec(c, "bool").update(frame={"tag": 69}),
     "carries no codec frame"),
    ("unshared duplicate tag",
     lambda c, i: codec(c, "field", "baby-bear")["frame"].update(tag=19),
     "frame tag 19 needs exactly one user"),
    ("shared tag used by an unlisted kind",
     lambda c, i: find(c["frameTags"], tag=71)["shared"].update(kind="proof"),
     "shared frame tag 71 users disagree"),
    ("field codec with a vector layout",
     lambda c, i: codec(c, "field", "koala-bear")["frame"].update(tag=20),
     "codec kind field fixes its frame layout"),
    ("proof codec with the root layout",
     lambda c, i: codec(c, "proof", "rows.merkle-poseidon2-16.koala-bear/0")["frame"].update(tag=71),
     "codec kind proof fixes its frame layout"),
    ("group widths differ",
     lambda c, i: codec(c, "groups", "bn254.g1")["frame"].update(elementBytes=64),
     "group and groups codecs disagree"),
    ("commitment frame of another scheme",
     lambda c, i: codec(c, "commitment", "multilinear.kzg.bls12-381/0").update(frame={"tag": 33}),
     "codec kind commitment fixes its frame layout"),
    ("aggregate frame layout", lambda c, i: find(c["aggregateFrames"], constructor="sequence").update(tag=65),
     "aggregate frame tag layout mismatch"),
    ("sequence frame with a domain",
     lambda c, i: find(c["aggregateFrames"], constructor="sequence").update(domain="koala-bear"),
     "frame has the empty domain"),
    ("rng type without a service",
     lambda c, i: c["randomServices"].pop(0), "random services and rng logical types disagree"),
    ("duplicate service field",
     lambda c, i: c["randomServices"][1].update(field=c["randomServices"][0]["field"]),
     "duplicate random service field"),
    ("duplicate limit", lambda c, i: c["limits"].append(copy.deepcopy(c["limits"][0])), "duplicate limit"),
    ("negative limit", lambda c, i: c["limits"][0].update(value=-1), "invalid limit value"),
    ("fold with a collection",
     lambda c, i: find(c["finiteDefinitions"], identity="math.fold").update(collection="vector"),
     "only collect names a collection"),
    ("filtered field array",
     lambda c, i: find(c["finiteDefinitions"], identity="math.collect.field_array").update(filtered=True),
     "cannot be filtered"),
    ("duplicate finite definition",
     lambda c, i: c["finiteDefinitions"].append(copy.deepcopy(c["finiteDefinitions"][0])),
     "duplicate finite definition"),
    ("domain constructor axis", lambda c, i: c["domainConstructors"][0].update(axis=2), "axis is 0 or 1"),
    ("succession port outside the signature",
     lambda c, i: find(c["operations"], name="resource_unit.pass")["facets"][0].update(stateInput=1),
     "succession port outside signature"),
    ("succession over ordinary values",
     lambda c, i: find(c["operations"], name="index.add")["facets"].append(
         {"kind": "Succession", "stateInput": 0, "stateOutput": 0}),
     "succession ports must be resource units"),
]

INSTALLATION_MUTATIONS = [
    ("unknown installation table", lambda c, i: i.update(extra=[]), "unknown fields"),
    ("representation of an undeclared instance",
     lambda c, i: i["representations"].append(
         dict(copy.deepcopy(i["representations"][0]), kind="field", domain="bn254.g1")),
     "undeclared logical type instance"),
    ("second default representation",
     lambda c, i: find(i["representations"], identity="blst/fr", kind="field").update(default=True),
     "second default representation"),
    ("duplicate representation",
     lambda c, i: i["representations"].append(copy.deepcopy(i["representations"][0])),
     "duplicate representation"),
    ("instance without a default",
     lambda c, i: i["representations"].remove(find(i["representations"], identity="native.bool/0")),
     "has no default representation"),
    ("local default of a framed instance",
     lambda c, i: find(i["representations"], identity="native.bool/0").update(frame="local"),
     "the default of a framed instance is canonical"),
    ("canonical representation without a framed codec",
     lambda c, i: find(i["representations"], identity="arkworks.polynomial/0").update(frame="canonical"),
     "requires a framed codec for its instance"),
    ("canonical applied representation without an aggregate frame",
     lambda c, i: find(i["appliedRepresentations"], identity="blst/fixed-vector").update(frame="canonical"),
     "requires its aggregate frame"),
    ("canonical field array over a field without a frame",
     lambda c, i: find(i["appliedRepresentations"], identity="arkworks.field-array/0").update(
         arguments=[["domain", "Field", "koala-bear"], ["natRange", "0", "1048576"]],
         child={"kind": "field", "domain": "koala-bear", "representation": "plonky3.koala-bear/0"}),
     "requires its aggregate frame"),
    ("canonical field array over any field",
     lambda c, i: find(i["appliedRepresentations"], identity="blst/field-array").update(
         arguments=[["any"], ["natRange", "0", "1048576"]], child=None),
     "requires its aggregate frame"),
    ("default storage unit", lambda c, i: find(i["representations"], identity="arkworks.fr/0").update(unit="blst"),
     "default storage unit"),
    ("duplicate layout",
     lambda c, i: i["representations"].append(
         dict(copy.deepcopy(find(i["representations"], identity="arkworks.fr-diagonal/0")), identity="other/0")),
     "duplicate representation layout"),
    ("applied representation of a nullary type",
     lambda c, i: i["appliedRepresentations"][0].update(constructor="bool", arguments=[]),
     "parameterized constructor"),
    ("pattern of another kind",
     lambda c, i: i["appliedRepresentations"][0]["arguments"].__setitem__(0, ["natRange", "0", "1"]),
     "natural argument disagrees"),
    ("natural beyond the static bound",
     lambda c, i: i["appliedRepresentations"][0]["arguments"].__setitem__(1, ["natRange", "0", "1048577"]),
     "natural exceeds the static bound"),
    ("child of another element",
     lambda c, i: i["appliedRepresentations"][0]["child"].update(domain="koala-bear",
                                                                representation="plonky3.koala-bear/0"),
     "child is not the logical element"),
    ("child without a representation row",
     lambda c, i: i["appliedRepresentations"][0]["child"].update(representation="missing/0"),
     "child names no representation row"),
    ("overlapping defaults",
     lambda c, i: find(i["appliedRepresentations"], identity="blst/field-array").update(default=True),
     "both defaults"),
    ("overlapping identities",
     lambda c, i: find(i["appliedRepresentations"], identity="blst/field-array").update(
         identity="arkworks.field-array/0"),
     "share an identity"),
    ("type pattern over a group",
     lambda c, i: find(i["appliedRepresentations"], identity="blst/fixed-vector")["arguments"].__setitem__(
         0, ["type", ["apply", "field", [["domain", "Field", "bn254.g1"]]]]),
     "domain argument disagrees"),
    ("type pattern that is no logical type instance",
     lambda c, i: find(i["appliedRepresentations"], identity="blst/fixed-vector")["arguments"].__setitem__(
         0, ["type", ["apply", "sequence", [["type", ["apply", "bool", []]]]]]),
     "type pattern is not a logical type instance"),
    ("slot pattern without a declared domain",
     lambda c, i: find(i["appliedRepresentations"], identity="logical.resource_unit/0").update(
         arguments=[["domain", "Slot", "Slot.A"]]),
     "domain argument disagrees"),
    ("domain without a provider row", lambda c, i: i["providers"].pop(0), "exactly one provider row"),
    ("provider twice in a row",
     lambda c, i: find(i["providers"], domain="bn254.fr")["alternatives"].append("arkworks"),
     "appears twice"),
    ("unknown provider", lambda c, i: i["providers"][0].update(default="native"),
     "unknown declaration alternative"),
    ("stated provider unit",
     lambda c, i: find(i["providerUnits"], provider="spongefish").update(unit="plonky3"),
     "spongefish is installed by arkworks"),
    ("arithmetic of another representation",
     lambda c, i: find(i["fieldForms"], field="koala-bear")["arithmetic"].update(
         representation="plonky3.koala-bear-vector/0"),
     "residue arithmetic names"),
    ("Montgomery words without arithmetic",
     lambda c, i: find(i["fieldForms"], field="gf2-64.pentanomial-4-3-1").update(
         montgomery={"wordBytes": 4, "radixBits": 32}),
     "require residue arithmetic"),
    ("Montgomery radix below the characteristic",
     lambda c, i: find(i["fieldForms"], field="goldilocks").update(montgomery={"wordBytes": 4, "radixBits": 32}),
     "exceeds the Montgomery radix"),
    ("Montgomery radix and word width",
     lambda c, i: find(i["fieldForms"], field="koala-bear")["montgomery"].update(radixBits=31),
     "radix is the word width"),
    ("byte encoding of another field",
     lambda c, i: find(i["fieldForms"], field="koala-bear")["byteEncoding"].update(codec="zkcv.field.baby-bear/0"),
     "byte encoding names"),
    ("second field form for one field",
     lambda c, i: i["fieldForms"].append(copy.deepcopy(i["fieldForms"][0])), "duplicate field form"),
    ("field form over a group",
     lambda c, i: i["fieldForms"][0].update(field="bn254.g1"), "is not a Field domain"),
    ("undeclared physical argument operation",
     lambda c, i: i["physicalArguments"].append({"operation": "example.missing"}), "undeclared operation"),
    ("duplicate physical argument row",
     lambda c, i: i["physicalArguments"].append(copy.deepcopy(i["physicalArguments"][0])),
     "duplicate physical argument row"),
]


class Documents(unittest.TestCase):
    def test_authored_documents_validate_and_project(self):
        catalog, installation = documents()
        validate(catalog)
        validate_installation(installation, catalog)
        declarations, _, native = project(catalog, installation)
        self.assertNotIn("ZKC_NativeRepresentation", declarations)
        self.assertNotIn("ZKC_InstalledDomain", native)
        self.assertEqual(project(catalog, installation), project(catalog, installation))

    def test_declaration_mutations_refuse(self):
        for label, mutate, expected in DECLARATION_MUTATIONS:
            with self.subTest(label):
                refuses(self, mutate, expected)

    def test_installation_mutations_refuse(self):
        for label, mutate, expected in INSTALLATION_MUTATIONS:
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

    def test_limits_match_the_specified_table(self):
        catalog, _ = documents()
        self.assertEqual(find(catalog["limits"], name="protocol.roles"), {
            "name": "protocol.roles", "value": 1024, "unit": "roles", "owner": "IR / Protocol",
            "scope": "Ordered role roster of one protocol, participant or Entry",
            "phase": "admission"})


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
