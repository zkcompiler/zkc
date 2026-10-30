"""Validate the authored catalog's exact shape and project TableGen inputs.

zkc-tblgen separately checks kinds, scopes, requirements, permissions and facets.
The Rust build performs its own formation checks without running this tool.
"""

import argparse
import json
from pathlib import Path
import sys

from tablegen import project


def require(condition, message):
    if not condition:
        raise ValueError(message)


def text(value):
    require(isinstance(value, str), "expected string")
    value.encode("utf-8", errors="strict")


def count(value):
    require(type(value) is int and 0 <= value <= 1048576, "invalid declaration count")


def flag(value):
    require(type(value) is bool, "expected Boolean")


def one_of(*values):
    def check(value):
        text(value)
        require(value in values, f"unknown declaration alternative {value}")

    return check


def sequence(check):
    def validate(value):
        require(
            isinstance(value, list) and len(value) <= 100000, "invalid declaration list"
        )
        for item in value:
            check(item)

    return validate


def nullable(check):
    def validate(value):
        if value is not None:
            check(value)

    return validate


def record(value, required, optional=None):
    optional = optional or {}
    require(isinstance(value, dict), "expected declaration object")
    require(
        set(required) <= value.keys(), f"missing fields: {set(required) - value.keys()}"
    )
    require(
        value.keys() <= required.keys() | optional.keys(),
        f"unknown fields: {value.keys() - required.keys() - optional.keys()}",
    )
    fields = required | optional
    for key, item in value.items():
        fields[key](item)


def kind(value):
    record(value, {"kind": one_of("Domain", "Type", "Nat"), "sort": text})
    require(
        value["kind"] == "Domain" or value["sort"] == "", "non-domain kind has a sort"
    )


def application(value, extra=None):
    record(value, {"constructor": text, "arguments": sequence(count)} | (extra or {}))


def term(value):
    require(isinstance(value, dict), "expected scope term")
    tag = value.get("kind")
    common = {"kind": one_of("root", "project", "apply", "natural")}
    if tag == "root":
        record(value, common | {"name": text, "parameter": kind})
    elif tag == "project":
        record(value, common | {"member": text, "parent": count})
    elif tag == "apply":
        application(value, common)
    elif tag == "natural":
        record(value, common | {"value": text})
        number = int(value["value"])
        count(number)
        require(str(number) == value["value"], "noncanonical natural")
    else:
        raise ValueError("unknown scope term")


def port(value):
    require(isinstance(value, dict), "expected port")
    if "term" in value:
        record(value, {"term": count})
    else:
        application(value)


def signature(value):
    require(isinstance(value, dict), "expected signature")
    if value.get("kind") == "fixed":
        record(
            value,
            {
                "kind": one_of("fixed"),
                "inputs": sequence(port),
                "outputs": sequence(port),
            },
        )
    else:
        record(
            value,
            {
                "kind": one_of("numerical"),
                "fieldTerm": count,
                "result": one_of("map", "sum", "product"),
            },
        )


def parameters(value):
    record(
        value,
        {
            "validator": one_of(
                "None",
                "Natural",
                "Extent",
                "FieldLiteral",
                "FieldLiterals",
                "MatrixShape",
                "MatrixIdentity",
                "AssetIdentity",
                "MatrixVector",
                "GatherIndices",
                "ScatterIndices",
                "NumericalExpression",
                "NativeOrigin",
            ),
            "minimum": count,
            "maximum": nullable(count),
        },
        {"fieldTerm": count, "assetFormat": text},
    )


def requirement(value):
    record(value, {"capability": text, "arguments": sequence(count)})


def facet(value):
    require(isinstance(value, dict), "expected facet")
    tag = value.get("kind")
    fields = {
        "PublicReplay": {},
        "AcceptanceGuard": {},
        "Conjunction": {},
        "SourceHistory": {},
        "ManagedHistory": {},
        "Mathematical": {"identity": text},
        "History": {"stateInput": count, "stateOutput": count},
        "Observation": {
            "stateInput": count,
            "payloadInput": count,
            "stateOutput": count,
        },
        "Sampling": {
            "provider": one_of("Entropy", "Transcript"),
            "domain": one_of("Field", "FieldVector", "BoundedIndex"),
            "stateInput": count,
            "valueOutput": count,
            "stateOutput": count,
            "boundInput": nullable(count),
        },
        "Diagonal": {
            "factorsInput": count,
            "valuesInput": count,
            "resultOutput": count,
        },
        "Contraction": {"coefficientsInput": count, "valuesInput": count},
        "Coset": {
            "shiftInput": count,
            "sizeInput": count,
            "sizeIsLength": flag,
            "foldedOutput": flag,
            "vectorOutput": nullable(count),
        },
    }
    if tag == "DomainValue":
        rule = value.get("rule")
        extra = (
            {"parameter": count}
            if rule == "Constant"
            else {"input": count}
            if rule == "Length"
            else {"input": count, "otherInput": count}
        )
        record(
            value,
            {
                "kind": one_of(tag),
                "rule": one_of("Constant", "Length", "Multiply", "Divide"),
                "output": count,
            }
            | extra,
        )
    else:
        require(isinstance(tag, str) and tag in fields, "unknown facet")
        record(value, {"kind": one_of(tag)} | fields[tag])


def operation(value):
    record(
        value,
        {
            "name": text,
            "scope": sequence(term),
            "stage": one_of("Source", "Construction", "CompilerGenerated", "Physical"),
            "parameters": parameters,
            "signature": signature,
            "requirements": sequence(requirement),
            "facets": sequence(facet),
        },
        {"derivedCounterpart": text},
    )


def laws(value):
    record(
        value,
        {
            "algebra": one_of("FieldRing", "GroupModule", "Access"),
            "signature": one_of(
                "FieldConstant",
                "FieldBinary",
                "GroupBinary",
                "GroupAction",
                "ElementAccess",
                "MatrixAccess",
            ),
            "associative": flag,
            "commutative": flag,
            "total": flag,
            "scalarAction": flag,
            **{
                key: one_of("None", "Zero", "One", "GroupIdentity")
                for key in ("leftIdentity", "rightIdentity", "annihilator")
            },
            "access": one_of("None", "Element", "MatrixCell"),
        },
    )


def export(value):
    require(isinstance(value, dict), "expected export")
    key = "constructor" if "constructor" in value else "predicate"
    record(value, {"module": text, "name": text, key: text})


def rule(value):
    sequence(text)(value)
    require(len(value) == 2, "implication needs two predicates")


def validate(catalog):
    def row(fields):
        return lambda value: record(value, fields)

    record(
        catalog,
        {
            "format": one_of("zkc.contract-declarations/0"),
            "sorts": sequence(text),
            "types": sequence(
                row(
                    {
                        "name": text,
                        "parameters": sequence(kind),
                        "custody": one_of("PublicValue", "PrivateImmutable", "Affine"),
                        **{
                            key: flag
                            for key in (
                                "copy",
                                "drop",
                                "nativeLocal",
                                "mathematical",
                                "participants",
                                "constructible",
                                "message",
                            )
                        },
                    }
                )
            ),
            "operations": sequence(operation),
            "members": sequence(row({"name": text, "owner": kind, "result": kind})),
            "rules": sequence(rule),
            "capabilities": sequence(row({"name": text, "parameters": sequence(kind)})),
            "exports": sequence(export),
            "families": sequence(
                row(
                    {
                        "family": text,
                        "elementConstructor": text,
                        "resultConstructor": text,
                    }
                )
            ),
            "associatedTypes": sequence(
                row({"sort": text, "member": text, "constructor": text})
            ),
            "mathematicalIdentities": sequence(
                row({"name": text, "laws": nullable(laws)})
            ),
            "mathematicalIntrinsics": sequence(
                row(
                    {
                        "name": text,
                        "identity": text,
                        "domainKind": one_of(
                            "Boolean",
                            "Index",
                            "Collection",
                            "Field",
                            "Group",
                            "Quotient",
                        ),
                        "naturals": count,
                        "domainPoints": flag,
                        "scalar": flag,
                    }
                )
            ),
        },
    )

    # Reject duplicates before dictionary-backed projection can hide them.
    for category in (
        "types",
        "operations",
        "capabilities",
        "mathematicalIdentities",
        "mathematicalIntrinsics",
    ):
        names = [row["name"] for row in catalog[category]]
        require(len(names) == len(set(names)), f"duplicate {category} identity")
    require(len(catalog["sorts"]) == len(set(catalog["sorts"])), "duplicate sort")
    for row in catalog["operations"]:
        for key in ("scope", "requirements", "facets"):
            require(len(row[key]) <= 1024, "operation declaration limit")


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate key {key}")
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    data = args.source.read_bytes()
    require(len(data) <= 64 * 1024 * 1024, "declaration byte limit")
    catalog = json.loads(data, object_pairs_hook=unique)
    validate(catalog)
    declarations, mathematical = project(catalog)
    args.output.mkdir(parents=True, exist_ok=True)
    for name, content in (
        ("Catalog.td", declarations),
        ("Mathematical.td", mathematical),
    ):
        target = args.output / name
        # Do not invalidate every dependent target for an unchanged projection.
        if not target.exists() or target.read_text() != content:
            target.write_text(content)


if __name__ == "__main__":
    try:
        main()
    except (
        ValueError,
        KeyError,
        IndexError,
        TypeError,
        RecursionError,
        OSError,
    ) as error:
        sys.exit(f"invalid declaration source: {error}")
