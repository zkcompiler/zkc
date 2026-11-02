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
import validation_cases  # noqa: E402


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

    # The shared validation cases: the generator and zkc-tblgen each accept the
    # accepted edits and refuse every refused edit on their own, with their own
    # diagnostics. The Rust build runs the same cases.
    def run_native(value, physical, expected=None):
        """zkc-tblgen over the declarations alone, then with the installation."""
        if expected is None:
            assert native(value, check_source=False) == value
            assert native(value, check_source=False, physical=physical) == physical
            return
        try:
            native(value, check_source=False)
        except AssertionError:
            native(value, expected, check_source=False)
            return
        native(value, expected, check_source=False, physical=physical)

    cases = validation_cases.load()
    for shared in cases["accepted"]:
        with case("both native validators accept " + shared["name"]):
            value, other = validation_cases.apply(shared["edits"], source, installation)
            validate(value)
            validate_installation(other, value)
            run_native(value, other)
    for shared in cases["refused"]:
        with case("both native validators refuse " + shared["name"]):
            value, other = validation_cases.apply(shared["edits"], source, installation)
            try:
                validate(value)
                validate_installation(other, value)
            except ValueError as error:
                assert shared["diagnostics"]["generator"] in str(error), error
            else:
                raise AssertionError("generator accepted " + shared["name"])
            run_native(value, other, shared["diagnostics"]["native"])

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
