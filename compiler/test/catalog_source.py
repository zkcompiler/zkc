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
from generate import unique, validate  # noqa: E402
from tablegen import project  # noqa: E402


def main():
    source = json.loads((ROOT / "common/catalog/declarations.json").read_text(), object_pairs_hook=unique)
    directory = Path(records()) / "include/zkc/Contracts"
    directory.mkdir(parents=True)
    generator = tool("tablegen")

    def native(value, expected=None, check_source=True, composed=False):
        if check_source:
            validate(value)
        declarations, mathematical = project(value)
        (directory / "Catalog.td").write_text(declarations)
        (directory / "Mathematical.td").write_text(mathematical)
        input_path = directory / "Catalog.td"
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
        result = subprocess.run([generator, "--dump-contract-declarations",
                                 "-I", directory.parents[1], "-I", ROOT / "compiler/include",
                                 input_path], text=True, capture_output=True)
        if expected:
            assert result.returncode and expected in result.stderr, result.stderr
            return None
        assert result.returncode == 0, result.stderr
        return json.loads(result.stdout)

    with case("every section survives independent native projection"):
        assert native(source) == source
        assert project(source) == project(source)

    with case("installed contribution cannot enroll itself into the selected consumer"):
        inventory = native(source, composed=True)
        assert inventory["operations"][-1]["name"] == "example.unenrolled"
        assert inventory["consumerProfiles"] == source["consumerProfiles"]

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
