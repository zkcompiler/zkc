"""Check the neutral catalog's exact schema and independent ABI witnesses."""
import json
from pathlib import Path
import subprocess

from cases import case, counted
from tools import tool


def main():
    generator = tool("tablegen")
    root = Path(__file__).resolve().parents[1] / "include"
    result = subprocess.run([generator, "--dump-contract-declarations", "-I", root,
                             "-I", generator.parent / "include",
                             root / "zkc/Contracts/Declarations.td"],
                            text=True, capture_output=True, check=True)
    catalog = json.loads(result.stdout)
    with case("exact current envelope at development version zero"):
        assert catalog.keys() == {"format", "sorts", "types", "operations", "members", "rules",
                                  "capabilities", "exports", "families", "associatedTypes",
                                  "mathematicalIdentities", "mathematicalIntrinsics", "consumerProfiles"}
        assert catalog["format"] == "zkc.contract-declarations/0"
        assert '"commonGeneric"' not in result.stdout
    types = {t["name"]: t for t in catalog["types"]}
    operations = {o["name"]: o for o in catalog["operations"]}
    with case("structured primitive profile preserves its independent consumer ABI"):
        assert len(catalog["consumerProfiles"]) == 1
        profile = catalog["consumerProfiles"][0]
        assert profile.keys() == {"name", "implementation", "typeConstructors", "parameterValidators", "operations"}
        assert profile["name"] == "structured-source-primitives"
        assert profile["implementation"] == "unselected"
        assert profile["typeConstructors"] == ["index", "bool", "field", "vector"]
        assert profile["parameterValidators"] == ["None", "Natural"]
        assert [m["operation"] for m in profile["operations"]] == [
            "index.constant", "index.add", "index.sub", "index.mul", "index.div", "index.mod",
            "index.equal", "index.less", "vector.empty", "vector.length", "vector.sum",
            "vector.split", "vector.append", "vector.equal", "field.equal", "field.embed"]
        for member in profile["operations"]:
            assert member.keys() == {"operation", "scope", "stage", "parameters", "signature", "requirements"}
            assert all(member[k] == operations[member["operation"]][k] for k in member if k != "operation")
            roots = [t["parameter"] for t in member["scope"] if t["kind"] == "root"]
            assert roots == ([] if member["operation"].startswith("index.") else [{"kind": "Domain", "sort": "Field"}])
        assert operations["field.embed"]["scope"][1] == {"kind": "project", "parent": 0, "member": "BaseField"}
        assert operations["vector.equal"]["requirements"] == [{"capability": "CommRing", "arguments": [0]}]
    meanings = {m["name"]: m for m in catalog["mathematicalIdentities"]}
    with case("logical constructors exclude native containers"):
        assert not {"scalar", "capability"} & types.keys()
        assert types["resource_unit"]["parameters"] == [{"kind": "Domain", "sort": "Slot"}]
    for operation in catalog["operations"]:
        with case(operation["name"] + " complete tagged signature"):
            fields = {"name", "scope", "stage", "parameters", "signature", "requirements", "facets"}
            assert fields <= operation.keys() <= fields | {"derivedCounterpart"}
            for i, term in enumerate(operation["scope"]):
                keys = {"root": {"kind", "name", "parameter"},
                        "project": {"kind", "member", "parent"},
                        "apply": {"kind", "constructor", "arguments"},
                        "natural": {"kind", "value"}}
                assert term.keys() == keys[term["kind"]]
                if term["kind"] == "project":
                    assert 0 <= term["parent"] < i
                if term["kind"] == "apply":
                    assert term["constructor"] in types
                    assert all(0 <= index < i for index in term["arguments"])
            schema = operation["parameters"]
            assert schema["maximum"] is None or schema["maximum"] >= schema["minimum"] >= 0
            signature = operation["signature"]
            if signature["kind"] == "numerical":
                assert signature.keys() == {"kind", "fieldTerm", "result"}
                assert signature["fieldTerm"] == 0 and signature["result"] in {"map", "sum", "product"}
            else:
                assert signature.keys() == {"kind", "inputs", "outputs"}
                assert signature["kind"] == "fixed"
            for facet in operation["facets"]:
                if facet["kind"] == "Mathematical":
                    assert facet["identity"] in meanings
                for port in ("boundInput", "vectorOutput"):
                    if port in facet:
                        assert facet[port] is None or facet[port] >= 0
                if facet["kind"] == "DomainValue":
                    fields = {"kind", "rule", "output"}
                    fields |= {"parameter"} if facet["rule"] == "Constant" else {"input"}
                    if facet["rule"] in {"Multiply", "Divide"}:
                        fields.add("otherInput")
                    assert facet.keys() == fields
    with case("resource signatures preserve the declared nominal slot"):
        for mode, ins, outs in [("create", 0, 1), ("pass", 1, 1), ("consume", 1, 0)]:
            op = operations["resource_unit." + mode]
            assert op["scope"] == [{"kind": "root", "name": "S",
                                    "parameter": {"kind": "Domain", "sort": "Slot"}}]
            port = {"constructor": "resource_unit", "arguments": [0]}
            assert op["signature"] == {"kind": "fixed", "inputs": [port] * ins, "outputs": [port] * outs}
    with case("mathematical data retains meanings and independent law obligations"):
        assert meanings["FieldAdd"]["laws"]["associative"] is True
        assert all(intrinsic["identity"] in meanings for intrinsic in catalog["mathematicalIntrinsics"])
    with case("constant value facet indexes parameters of a nullary operation"):
        op = operations["index.constant"]
        assert op["signature"]["inputs"] == []
        assert {"kind": "DomainValue", "rule": "Constant", "output": 0, "parameter": 0} in op["facets"]
    print(f"{counted()} catalog inventory cases exercised")


if __name__ == "__main__":
    main()
