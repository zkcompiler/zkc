"""Check shared-source projection against independent native declaration admission."""
import copy
import json
from pathlib import Path
import subprocess
import sys

from cases import case, counted
from tools import records, tool

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "common/catalog"))
from generate import unique, validate, validate_installation  # noqa: E402
from tablegen import project  # noqa: E402
from test_deterministic_data import COVERAGE  # noqa: E402


def main():
    source = json.loads((ROOT / "common/catalog/declarations.json").read_text(), object_pairs_hook=unique)
    installation = json.loads((ROOT / "common/catalog/installation.json").read_text(),
                              object_pairs_hook=unique)
    directory = Path(records()) / "include/zkc/Contracts"
    directory.mkdir(parents=True)
    generator = tool("tablegen")

    def native(value, expected=None, check_source=True, composed=False, extra="", physical=None):
        """Dump the declarations, or with `physical` the native installation
        checked together with them."""
        if check_source:
            validate(value)
            if physical is not None:
                validate_installation(physical, value)
        declarations, mathematical, installed = project(
            value, installation if physical is None else physical)
        (directory / "Catalog.td").write_text(declarations + extra)
        (directory / "Mathematical.td").write_text(mathematical)
        (directory / "NativeInstallation.td").write_text(installed)
        input_path = directory / "Catalog.td"
        action = "--dump-contract-declarations"
        if physical is not None:
            input_path = directory / "Complete.td"
            input_path.write_text('include "zkc/Contracts/Catalog.td"\n'
                                  'include "zkc/Contracts/NativeInstallation.td"\n')
            action = "--dump-native-installation"
        if composed:
            input_path = directory / "Installation.td"
            input_path.write_text('''include "zkc/Contracts/Declarations/Schema.td"
defset list<ZKC_Declaration> BaseRecords = {
include "zkc/Contracts/Catalog.td"
}
def Base : ZKC_Contribution<"base", [], BaseRecords>;
def Extra : ZKC_Operation<"example.unenrolled", [], [], []>;
def Extension : ZKC_Contribution<"example", ["base"], [Extra]>;
''')
        result = subprocess.run([generator, action,
                                 "-I", directory.parents[1], "-I", ROOT / "compiler/include",
                                 input_path], text=True, capture_output=True)
        if expected:
            assert result.returncode > 0 and expected in result.stderr, result.stderr
            return None
        assert result.returncode == 0, result.stderr
        return json.loads(result.stdout)

    with case("every section survives independent native projection"):
        assert native(source) == source
        assert native(source, physical=installation) == installation
        assert project(source, installation) == project(source, installation)

    def find(rows, **fields):
        return next(r for r in rows if all(r[k] == v for k, v in fields.items()))

    # Each forged row breaks one installed-instance, Succession or installation
    # rule; the generator and zkc-tblgen must each refuse it on their own.
    for label, mutate, generator_diagnostic, native_diagnostic, physical in [
        ("duplicate identity",
         lambda c, i: c["domains"].append(copy.deepcopy(c["domains"][0])),
         "duplicate domain identity", "duplicate domain identity", False),
        ("member sort mismatch",
         lambda c, i: find(c["domains"], identity="edwards25519.prime")["members"].__setitem__(
             0, ["Scalar", "ristretto255.group"]),
         "domain member sort mismatch", "domain member sort mismatch", False),
        ("codec over an unadmitted type",
         lambda c, i: c["codecs"].append({"identity": "zkcv.point.koala-bear/0", "kind": "point",
                                          "domain": "koala-bear", "frame": None}),
         "codec payload is not an admitted logical type",
         "codec payload is not an admitted logical type", False),
        ("unshared duplicate tag",
         lambda c, i: find(c["codecs"], kind="field", domain="baby-bear")["frame"].update(tag=19),
         "frame tag 19 needs exactly one user", "frame tag 19 needs exactly one user", False),
        ("shared tag used by an unlisted kind",
         lambda c, i: find(c["frameTags"], tag=71)["shared"].update(kind="proof"),
         "shared frame tag 71 users disagree", "shared frame tag 71 users disagree", False),
        ("codec frame of another layout",
         lambda c, i: find(c["codecs"], kind="field", domain="koala-bear")["frame"].update(tag=20),
         "codec kind field fixes its frame layout", "codec kind field fixes its frame layout", False),
        ("empty extension reduction",
         lambda c, i: find(c["domains"], identity="koala-bear.ext4-binomial3")["field"]["structure"].update(
             reduction=[]),
         "extension reduction is a nonempty list", "extension reduction is a nonempty list", False),
        ("structure without ExtensionField",
         lambda c, i: find(c["domains"], identity="koala-bear.ext4-binomial3")["capabilities"].remove(
             "ExtensionField"),
         "ExtensionField disagrees with the structure",
         "ExtensionField disagrees with the structure", False),
        ("prime structure holding ExtensionField",
         lambda c, i: find(c["domains"], identity="koala-bear")["capabilities"].append("ExtensionField"),
         "ExtensionField disagrees with the structure",
         "ExtensionField disagrees with the structure", False),
        ("BaseField member over the prime subfield",
         lambda c, i: find(c["domains"], identity="gf2-64.pentanomial-4-3-1")["members"].append(
             ["BaseField", "koala-bear"]),
         "exactly the rows over BaseField have a BaseField member",
         "exactly the rows over BaseField have a BaseField member", False),
        ("Succession port outside the signature",
         lambda c, i: find(c["operations"], name="resource_unit.pass")["facets"][0].update(stateInput=1),
         "succession port outside signature", "facet port outside signature", False),
        ("Succession over ordinary values",
         lambda c, i: find(c["operations"], name="index.add")["facets"].append(
             {"kind": "Succession", "stateInput": 0, "stateOutput": 0}),
         "succession ports must be resource units", "facet port constructor mismatch", False),
        ("canonical representation without a framed codec",
         lambda c, i: find(i["representations"], identity="arkworks.polynomial/0").update(frame="canonical"),
         "requires a framed codec for its instance", "requires a framed codec for its instance", True),
        ("local default of a framed instance",
         lambda c, i: find(i["representations"], identity="native.bool/0").update(frame="local"),
         "the default of a framed instance is canonical",
         "the default of a framed instance is canonical", True),
        ("canonical applied representation without an aggregate frame",
         lambda c, i: find(i["appliedRepresentations"], identity="blst/fixed-vector").update(frame="canonical"),
         "requires its aggregate frame", "requires its aggregate frame", True),
        ("canonical field array over a field without a frame",
         lambda c, i: find(i["appliedRepresentations"], identity="arkworks.field-array/0").update(
             arguments=[["domain", "Field", "koala-bear"], ["natRange", "0", "1048576"]],
             child={"kind": "field", "domain": "koala-bear", "representation": "plonky3.koala-bear/0"}),
         "requires its aggregate frame", "requires its aggregate frame", True),
        ("type pattern that is no logical type instance",
         lambda c, i: find(i["appliedRepresentations"], identity="blst/fixed-vector")["arguments"].__setitem__(
             0, ["type", ["apply", "sequence", [["type", ["apply", "bool", []]]]]]),
         "type pattern is not a logical type instance", "type pattern is not a logical type instance", True),
        ("slot pattern without a declared domain",
         lambda c, i: find(i["appliedRepresentations"], identity="logical.resource_unit/0").update(
             arguments=[["domain", "Slot", "Slot.A"]]),
         "domain argument disagrees with its parameter",
         "domain argument disagrees with its parameter", True),
        ("second field form for one field",
         lambda c, i: i["fieldForms"].append(copy.deepcopy(i["fieldForms"][0])),
         "duplicate field form", "duplicate field form", True),
        ("second default representation",
         lambda c, i: find(i["representations"], identity="blst/fr", kind="field").update(default=True),
         "second default representation", "second default representation", True),
        ("installation row naming an undeclared instance",
         lambda c, i: i["representations"].append(
             dict(copy.deepcopy(i["representations"][0]), kind="field", domain="bn254.g1")),
         "representation names an undeclared logical type instance",
         "representation names an undeclared logical type instance", True),
    ]:
        with case("both native validators refuse " + label):
            value, other = copy.deepcopy(source), copy.deepcopy(installation)
            mutate(value, other)
            try:
                validate(value)
                validate_installation(other, value)
            except ValueError as error:
                assert generator_diagnostic in str(error), error
            else:
                raise AssertionError("generator accepted " + label)
            native(value, native_diagnostic, check_source=False, physical=other if physical else None)

    for section, field, replacement, diagnostic in [
        ("frontendAssociations", "signature", "RandomConstructor", "frontend signature identity mismatch"),
        ("frontendAssociations", "identity", "record.unknown", "frontend signature identity mismatch"),
        ("frontendHomes", "constructor", "Vector", "invalid frontend home"),
        ("frontendHomes", "module", "foreign", "invalid frontend home"),
        ("serviceMethods", "signature", "Unknown", "service method capability mismatch"),
        ("serviceMethods", "capability", "IndexRandomness", "service method capability mismatch"),
    ]:
        with case(f"independent frontend refusal {section}.{field}"):
            value = copy.deepcopy(source)
            value[section][0][field] = replacement
            try:
                validate(value)
            except ValueError:
                pass
            else:
                raise AssertionError("source accepted invalid frontend association")
            native(value, diagnostic, check_source=False)
    for section, diagnostic in [("frontendAssociations", "duplicate source export ownership"),
                                ("frontendHomes", "duplicate frontend home"),
                                ("serviceMethods", "invalid or duplicate service method")]:
        with case("independent duplicate " + section):
            value = copy.deepcopy(source)
            value[section].append(copy.deepcopy(value[section][0]))
            native(value, diagnostic, check_source=False)
    with case("source spelling is separate from installed identity"):
        value = copy.deepcopy(source)
        value["frontendAssociations"][0]["name"] = "open_payload"
        assert native(value)["frontendAssociations"] == value["frontendAssociations"]
    with case("unknown frontend authority fields refuse"):
        value = copy.deepcopy(source)
        value["frontendAssociations"][0]["authority"] = "all-records"
        try:
            validate(value)
        except ValueError as error:
            assert "unknown fields" in str(error)
        else:
            raise AssertionError("source accepted unknown association authority")

    with case("installed contribution cannot enroll itself into the selected consumer"):
        inventory = native(source, composed=True)
        assert inventory["operations"][-1]["name"] == "example.unenrolled"
        assert inventory["consumerProfiles"] == source["consumerProfiles"]

    with case("deterministic data is an exact nullary exported facet"):
        inventory = native(source)
        selected = [op for op in inventory["operations"]
                    if {"kind": "DeterministicData"} in op["facets"]]
        assert {op["name"] for op in selected} == {
            name for rows in COVERAGE.values() for name in rows.split()}
        assert all(f == {"kind": "DeterministicData"} for op in selected
                   for f in op["facets"] if f["kind"] == "DeterministicData")

    with case("new declarations do not inherit deterministic data by prefix"):
        inventory = native(source, extra='\ndef FutureIndex : ZKC_Operation<"index.future", [], [], []>;\n')
        assert next(op for op in inventory["operations"]
                    if op["name"] == "index.future")["facets"] == []

    with case("duplicate deterministic data is independently refused"):
        value = copy.deepcopy(source)
        value["operations"][0]["facets"] = [{"kind": "DeterministicData"}] * 2
        native(value, "duplicate semantic facet", check_source=False)

    with case("unknown facets are independently refused"):
        native(source, "unsupported semantic facet", extra='''
def UnknownData : ZKC_Facet;
def UnknownOperation : ZKC_Operation<"example.unknown", [], [], []> {
  let facets = [UnknownData];
}
''')

    with case("separate consumer profiles require explicit declaration expectations"):
        value = copy.deepcopy(source)
        profile = copy.deepcopy(value["consumerProfiles"][0])
        profile["name"] = "example-primitives"
        profile["operations"] = []
        op = next(o for o in value["operations"] if o["name"] == "field.add")
        profile["operations"].append({"operation": op["name"], **{
            key: copy.deepcopy(op[key]) for key in ("scope", "stage", "parameters", "signature", "requirements")}})
        value["consumerProfiles"].append(profile)
        assert native(value) == value

    for field, mutate in [
        ("scope", lambda m: m["scope"][0].update(name="Other")),
        ("stage", lambda m: m.update(stage="Construction")),
        ("signature", lambda m: m["signature"].update(inputs=[])),
        ("requirements", lambda m: m.update(requirements=[])),
        ("parameters", lambda m: m.update(parameters={"validator": "Natural", "minimum": 1, "maximum": 1})),
    ]:
        for side in ("declaration", "consumer"):
            with case("native consumer refuses " + side + " " + field + " drift"):
                value = copy.deepcopy(source)
                target = (next(o for o in value["operations"] if o["name"] == "field.equal")
                          if side == "declaration" else
                          next(m for m in value["consumerProfiles"][0]["operations"] if m["operation"] == "field.equal"))
                mutate(target)
                native(value, "consumer operation " + field + " mismatch", check_source=False)

    for label, mutate, expected in [
        ("duplicate membership", lambda p: p["operations"].append(copy.deepcopy(p["operations"][0])), "duplicate profile membership"),
        ("unsupported constructor", lambda p: p["typeConstructors"].remove("field"), "unsupported profile type constructor"),
        ("unsupported validator", lambda p: p.update(parameterValidators=["None"]), "unsupported profile validator"),
        ("unknown parameter family", lambda p: p["parameterValidators"].append("Unknown"), "unsupported profile parameter family"),
        ("selected implementation", lambda p: p.update(implementation="selected"), "unsupported profile implementation policy"),
        ("numerical signature family", lambda p: p["operations"][0].update(operation="numerical.map"), "unsupported profile signature family"),
    ]:
        with case("native consumer refuses " + label):
            value = copy.deepcopy(source)
            mutate(value["consumerProfiles"][0])
            native(value, expected, check_source=False)

    with case("nominal identities preserve Unicode and literal bytes"):
        value = copy.deepcopy(source)
        value["sorts"].extend(["Δοκιμή_한국어", 'quoted"slash\\',
                               "controls" + "".join(chr(n) for n in range(32))])
        assert native(value) == value

    with case("members retain Type and Nat ownership independently"):
        value = copy.deepcopy(source)
        for owner in ("Type", "Nat"):
            value["members"].append({"name": "Element", "owner": {"kind": owner, "sort": ""},
                                     "result": {"kind": "Type", "sort": ""}})
        value["operations"].append({
            "name": "example.identity", "scope": [
                {"kind": "root", "name": "N", "parameter": {"kind": "Nat", "sort": ""}},
                {"kind": "project", "parent": 0, "member": "Element"},
                {"kind": "project", "parent": 1, "member": "Element"}],
            "stage": "Source", "parameters": {"validator": "None", "minimum": 0, "maximum": 0},
            "signature": {"kind": "fixed", "inputs": [{"term": 2}], "outputs": [{"term": 2}]},
            "requirements": [], "facets": [],
        })
        assert native(value) == value

    for name, mutate, expected in [
        ("nominal port mismatch", lambda v: v["operations"][0]["signature"]["inputs"][0].update(arguments=[1, 0]),
         "parameter kind or sort mismatch"),
        ("unscoped direct port", lambda v: v["operations"][0]["signature"]["inputs"].__setitem__(0, {"term": 0}),
         "direct ports require a scoped Type term"),
    ]:
        with case(name):
            value = copy.deepcopy(source)
            mutate(value)
            native(value, expected)

    for name, mutate in [
        ("unknown root field", lambda v: v.update(unexpected=True)),
        ("unknown nested field", lambda v: v["operations"][0]["scope"][0].update(unexpected=0)),
        ("old envelope without profiles", lambda v: v.pop("consumerProfiles")),
        ("unknown profile field", lambda v: v["consumerProfiles"][0].update(unexpected=True)),
        ("unknown consumer operation field", lambda v: v["consumerProfiles"][0]["operations"][0].update(unexpected=True)),
        ("unknown consumer signature field", lambda v: v["consumerProfiles"][0]["operations"][0]["signature"].update(unexpected=True)),
        ("unknown consumer parameter field", lambda v: v["consumerProfiles"][0]["operations"][0]["parameters"].update(unexpected=True)),
        ("duplicate operation", lambda v: v["operations"].append(copy.deepcopy(v["operations"][0]))),
        ("Boolean count", lambda v: v["operations"][0]["parameters"].update(minimum=True)),
    ]:
        with case(name):
            value = copy.deepcopy(source)
            mutate(value)
            try:
                validate(value)
            except ValueError:
                pass
            else:
                raise AssertionError("malformed source was accepted")
    with case("duplicate object key"):
        try:
            json.loads('{"name":"a","name":"b"}', object_pairs_hook=unique)
        except ValueError:
            pass
        else:
            raise AssertionError("duplicate key accepted")
    print(f"{counted()} catalog source cases exercised")


if __name__ == "__main__":
    main()
