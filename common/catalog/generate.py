"""Validate exact catalog shapes and consumer expectations; project TableGen.

The declaration document and its native installation document are checked
together: installed-instance tables, the Succession law and every
native-installation rule are validated here, independently of zkc-tblgen.
zkc-tblgen separately checks kinds, scopes, requirements, permissions and facets
and again validates every installed-instance and installation rule over the
projected records. The Rust build performs its own formation checks without
running this tool.
"""

import argparse
import json
from pathlib import Path
import re
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
                "NativeIndexBlock",
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
        "DeterministicData": {},
        "AcceptanceGuard": {},
        "Conjunction": {},
        "SourceHistory": {},
        "ManagedHistory": {},
        "Mathematical": {"identity": text},
        "History": {"stateInput": count, "stateOutput": count},
        "Succession": {"stateInput": count, "stateOutput": count},
        "Observation": {
            "stateInput": count,
            "payloadInput": count,
            "stateOutput": count,
        },
        "Sampling": {
            "provider": one_of("Entropy", "Transcript"),
            "domain": one_of("Field", "FieldVector", "BoundedIndex", "IndexBlock"),
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


def consumer_operation(value):
    record(
        value,
        {
            "operation": text,
            "scope": sequence(term),
            "stage": one_of("Source", "Construction", "CompilerGenerated", "Physical"),
            "parameters": parameters,
            "signature": signature,
            "requirements": sequence(requirement),
        },
    )


def consumer_profile(value):
    record(
        value,
        {
            "name": text,
            "implementation": one_of("unselected"),
            "typeConstructors": sequence(text),
            "parameterValidators": sequence(text),
            "operations": sequence(consumer_operation),
        },
    )


def validate_profiles(catalog):
    operations = {row["name"]: row for row in catalog["operations"]}
    types = {row["name"] for row in catalog["types"]}
    validators = {
        "None", "Natural", "Extent", "FieldLiteral", "FieldLiterals",
        "MatrixShape", "MatrixIdentity", "AssetIdentity", "MatrixVector",
        "GatherIndices", "ScatterIndices", "NativeOrigin",
                "NativeIndexBlock",
    }
    for profile in catalog["consumerProfiles"]:
        require(bool(profile["name"]), "empty consumer profile identity")
        constructors = profile["typeConstructors"]
        require(len(constructors) == len(set(constructors)), "duplicate profile constructor")
        require(set(constructors) <= types, "unknown profile constructor")
        parameters = profile["parameterValidators"]
        require(len(parameters) == len(set(parameters)), "duplicate profile validator")
        require(set(parameters) <= validators, "unsupported profile parameter family")
        seen = set()
        for member in profile["operations"]:
            name = member["operation"]
            require(name not in seen, "duplicate profile membership")
            seen.add(name)
            require(name in operations, "unknown profile operation")
            op = operations[name]
            require(op["signature"]["kind"] == "fixed", "unsupported profile signature family")
            for key in ("scope", "stage", "signature", "requirements", "parameters"):
                require(member[key] == op[key], f"consumer operation {key} mismatch")
            require(op["parameters"]["validator"] in parameters, "unsupported profile validator")
            # Closed type dependencies: all scoped Type terms must be known
            # constructor applications. Open complete-Type roots/projections
            # need a separately specified profile family, not a default codec.
            kinds = []
            for scoped in op["scope"]:
                tag = scoped["kind"]
                if tag == "root":
                    result = scoped["parameter"]
                elif tag == "project":
                    parent = scoped["parent"]
                    require(parent < len(kinds), "unscoped profile projection")
                    matches = [m for m in catalog["members"]
                               if m["owner"] == kinds[parent] and m["name"] == scoped["member"]]
                    require(len(matches) == 1, "unknown profile associated member")
                    result = matches[0]["result"]
                else:
                    result = {"kind": "Type" if tag == "apply" else "Nat", "sort": ""}
                require(result["kind"] != "Type" or tag == "apply", "unsupported profile Type term")
                if tag == "apply":
                    require(scoped["constructor"] in constructors, "unsupported profile type constructor")
                    require(all(a < len(kinds) for a in scoped["arguments"]), "unscoped profile application")
                kinds.append(result)
            for port in op["signature"]["inputs"] + op["signature"]["outputs"]:
                if "term" in port:
                    index = port["term"]
                    require(index < len(kinds) and kinds[index]["kind"] == "Type",
                            "unsupported profile complete port")
                else:
                    require(port["constructor"] in constructors, "unsupported profile type constructor")


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
                                "sourceData",
                            )
                        },
                        "collection": nullable(
                            row(
                                {
                                    "rank": count,
                                    "element": one_of("parameter", "index", "byte"),
                                }
                            )
                        ),
                        "setup": nullable(one_of("prover", "verifier")),
                    }
                )
            ),
            "operations": sequence(operation),
            "consumerProfiles": sequence(consumer_profile),
            "members": sequence(row({"name": text, "owner": kind, "result": kind})),
            "rules": sequence(rule),
            "capabilities": sequence(row({"name": text, "parameters": sequence(kind)})),
            "exports": sequence(export),
            "frontendAssociations": sequence(row({
                "identity": text, "module": text, "name": text,
                "signature": one_of("RecordUnpack", "RecordInspect", "RecordRepack", "RandomConstructor"),
                "implicit": flag,
            })),
            "frontendHomes": sequence(row({"constructor": text, "module": text, "members": sequence(text)})),
            "serviceMethods": sequence(row({
                "name": text, "signature": one_of("RandomDraw", "RandomIndex", "RandomIndices"),
                "capability": text,
            })),
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
            "domains": sequence(domain_row),
            "logicalTypes": sequence(row({"kind": text, "domain": text})),
            "frameTags": sequence(
                row(
                    {
                        "tag": count,
                        "layout": one_of(*FRAME_LAYOUTS),
                        "shared": nullable(
                            row({"kind": text, "scheme": one_of(*COMMITMENT_SCHEMES)})
                        ),
                    }
                )
            ),
            "codecs": sequence(
                row(
                    {
                        "identity": text,
                        "kind": text,
                        "domain": text,
                        "frame": nullable(codec_frame),
                    }
                )
            ),
            "aggregateFrames": sequence(
                row({"constructor": text, "domain": text, "tag": count})
            ),
            "randomServices": sequence(row({"contract": text, "field": text})),
            "limits": sequence(
                row(
                    {
                        "name": text,
                        "value": limit_value,
                        "unit": one_of("roles", "bytes", "elements", "entries", "steps"),
                        "owner": text,
                        "scope": text,
                        "phase": one_of("formation", "admission", "publication", "execution"),
                    }
                )
            ),
            "finiteDefinitions": sequence(
                row(
                    {
                        "identity": text,
                        "mode": one_of("math", "local"),
                        "operation": one_of("fold", "collect"),
                        "collection": nullable(
                            one_of("vector", "groups", "sequence", "indices", "field_array")
                        ),
                        "filtered": flag,
                    }
                )
            ),
            "domainConstructors": sequence(
                row(
                    {
                        "identity": text,
                        "kind": one_of(*DOMAIN_CONSTRUCTOR_KINDS),
                        "axis": count,
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
        "consumerProfiles",
    ):
        names = [row["name"] for row in catalog[category]]
        require(len(names) == len(set(names)), f"duplicate {category} identity")
    require(len(catalog["sorts"]) == len(set(catalog["sorts"])), "duplicate sort")
    for row in catalog["operations"]:
        for key in ("scope", "requirements", "facets"):
            require(len(row[key]) <= 1024, "operation declaration limit")
        facets = [facet["kind"] for facet in row["facets"]]
        require(len(facets) == len(set(facets)), "duplicate semantic facet")
        for facet in row["facets"]:
            if facet["kind"] == "Succession":
                validate_succession(row, facet)
    validate_frontend(catalog)
    validate_profiles(catalog)
    validate_type_columns(catalog)
    validate_instances(catalog)


def validate_frontend(catalog):
    import re

    def path(value):
        return bool(re.fullmatch(r"zkc(?:::[A-Za-z_][A-Za-z_0-9]*)+", value))

    identities = {"record.unpack": "RecordUnpack", "record.inspect": "RecordInspect",
                  "record.repack": "RecordRepack", "service.random": "RandomConstructor"}
    owners = {(r["module"], r["name"]) for r in catalog["exports"]}
    seen = set()
    implicit = set()
    for row in catalog["frontendAssociations"]:
        require(identities.get(row["identity"]) == row["signature"], "frontend signature identity mismatch")
        require(row["identity"] not in seen, "duplicate frontend identity")
        seen.add(row["identity"])
        require(path(row["module"]) and bool(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", row["name"])), "invalid frontend owner")
        owner = (row["module"], row["name"])
        require(owner not in owners, "duplicate frontend ownership")
        owners.add(owner)
        if row["implicit"]:
            require(row["name"] not in implicit, "duplicate implicit frontend name")
            implicit.add(row["name"])
    heads = {t["name"] for t in catalog["types"]} | {"oracle", "oracle_sequence"}
    seen = set()
    for row in catalog["frontendHomes"]:
        require(row["constructor"] in heads and path(row["module"]), "invalid frontend home")
        require(row["constructor"] not in seen, "duplicate frontend home")
        seen.add(row["constructor"])
        require(len(row["members"]) == len(set(row["members"])) and all(path(member) for member in row["members"]), "invalid frontend home members")
    seen = set()
    rules = {"RandomDraw": "", "RandomIndex": "IndexRandomness", "RandomIndices": "IndexBlockRandomness"}
    for row in catalog["serviceMethods"]:
        require(bool(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", row["name"])), "invalid service method")
        require(row["name"] not in seen, "duplicate service method")
        seen.add(row["name"])
        require(rules.get(row["signature"]) == row["capability"], "service method capability mismatch")
        require(not row["capability"] or any(c["name"] == row["capability"] and c["parameters"] == [{"kind": "Domain", "sort": "Field"}] for c in catalog["capabilities"]), "unknown service capability")


FRAME_LAYOUTS = (
    "Scalar",
    "Vector",
    "SparseMatrix",
    "MerkleRoot",
    "MerklePath",
    "DigestRoot",
    "DigestProof",
    "PcsCommitment",
    "PcsProof",
    "Table",
    "Sequence",
    "Variant",
    "FieldArray",
)
# Frame fields beyond `tag` for each layout a codec may select. Aggregate
# layouts carry no codec frame.
CODEC_FRAME_FIELDS = {
    "Scalar": {"elementBytes"},
    "Vector": {"elementBytes"},
    "SparseMatrix": {"elementBytes"},
    "PcsCommitment": {"bytes"},
    "PcsProof": {"bytes", "bytesPerArity"},
    "MerkleRoot": set(),
    "MerklePath": set(),
    "DigestRoot": set(),
    "DigestProof": set(),
    "Table": set(),
}
AGGREGATE_LAYOUTS = {"sequence": "Sequence", "variant": "Variant", "field_array": "FieldArray"}
# The layout each codec kind's frame uses; commitment and proof frames follow
# their domain's commitment scheme.
KIND_LAYOUTS = {
    "field": "Scalar",
    "group": "Scalar",
    "bool": "Scalar",
    "index": "Scalar",
    "vector": "Vector",
    "groups": "Vector",
    "indices": "Vector",
    "bytes": "Vector",
    "matrix": "SparseMatrix",
    "table": "Table",
}
SCHEME_LAYOUTS = {
    "keccak256Rows": {"commitment": "MerkleRoot", "proof": "MerklePath"},
    "poseidon2Rows": {"commitment": "DigestRoot", "proof": "DigestProof"},
    "multilinearKzg": {"commitment": "PcsCommitment", "proof": "PcsProof"},
}
COMMITMENT_SCHEMES = ("keccak256Rows", "poseidon2Rows", "multilinearKzg")
# The pinned Poseidon2 instances and the field each permutes.
PERMUTATION_FIELDS = {
    "koala-bear.poseidon2-16": "koala-bear",
    "baby-bear.poseidon2-16": "baby-bear",
    "goldilocks.poseidon2-8": "goldilocks",
}
DOMAIN_CONSTRUCTOR_KINDS = (
    "Elements",
    "Indices",
    "Range",
    "Zip",
    "Product",
    "MatrixRow",
    "MatrixColumn",
    "MatrixCoordinates",
    "SourceArray",
)
PROVIDERS = ("arkworks", "blst", "dalek", "halo2curves-axiom", "plonky3", "spongefish")
UNITS = ("arkworks", "blst", "dalek", "halo2curves", "plonky3", "independent")
# Provider units the native-installation chapter states explicitly.
STATED_PROVIDER_UNITS = {"spongefish": "arkworks", "halo2curves-axiom": "halo2curves"}
STATIC_NATURAL_LIMIT = 1048576


def catalog_name(value):
    """The catalog name rule shared by every installed identity."""
    text(value)
    require(
        re.fullmatch(r"[A-Za-z_][A-Za-z0-9_./-]{0,255}", value) is not None,
        f"invalid catalog identity {value!r}",
    )


def decimal(value):
    text(value)
    require(re.fullmatch(r"0|[1-9][0-9]*", value) is not None, f"noncanonical decimal {value!r}")


def nonempty(value):
    text(value)
    require(value != "", "expected nonempty text")


def limit_value(value):
    # A ceiling is a count; the native projection carries it as a signed
    # 64-bit TableGen integer.
    require(type(value) is int and 0 <= value < 2**63, "invalid limit value")


def pair(value):
    require(isinstance(value, list) and len(value) == 2, "expected a pair")


def domain_member(value):
    pair(value)
    text(value[0])
    text(value[1])


def reduction_term(value):
    pair(value)
    count(value[0])
    decimal(value[1])


def field_structure(value):
    require(isinstance(value, dict), "expected field structure")
    if value.get("kind") == "prime":
        record(value, {"kind": one_of("prime")})
    else:
        record(
            value,
            {
                "kind": one_of("extension"),
                "over": one_of("BaseField", "PrimeSubfield"),
                "degree": count,
                "reduction": sequence(reduction_term),
            },
        )


def field_facts(value):
    record(
        value,
        {
            "characteristic": decimal,
            "structure": field_structure,
            "twoAdic": nullable(
                lambda v: record(
                    v,
                    {
                        "convention": catalog_name,
                        "maximalRoot": decimal,
                        "twoAdicity": count,
                        "ordering": one_of("powers"),
                    },
                )
            ),
        },
    )


def transcript_facts(value):
    record(
        value,
        {
            "family": one_of("merlin3", "spongefish0.8.0", "hash-chain"),
            "hash": nullable(one_of("keccak256")),
            "decoder": one_of("fr64be", "rejection31le", "rejection64le", "scalar64le"),
            "bindsSuite": flag,
        },
    )


def commitment_facts(value):
    require(isinstance(value, dict), "expected commitment facts")
    scheme = value.get("scheme")
    fields = {
        "keccak256Rows": {"digestBytes": count},
        "poseidon2Rows": {
            "permutation": one_of(*PERMUTATION_FIELDS),
            "digestBytes": count,
            "digestWordBytes": count,
        },
        "multilinearKzg": {},
    }
    require(isinstance(scheme, str) and scheme in fields, "unknown commitment scheme")
    record(value, {"scheme": one_of(scheme)} | fields[scheme])


def domain_row(value):
    require(isinstance(value, dict), "expected domain row")
    sort = value.get("sort")
    facts = {
        "Field": {"field": field_facts},
        "Transcript": {"transcript": transcript_facts},
        "Commitment": {"commitment": commitment_facts},
    }
    record(
        value,
        {
            "identity": catalog_name,
            "sort": text,
            "members": sequence(domain_member),
            "capabilities": sequence(text),
        }
        | (facts.get(sort, {}) if isinstance(sort, str) else {}),
    )


def codec_frame(value):
    # Exact fields depend on the referenced tag's layout and are checked with
    # the tag table.
    require(isinstance(value, dict) and "tag" in value, "expected codec frame")
    for key, item in value.items():
        require(key in {"tag", "elementBytes", "bytes", "bytesPerArity"}, f"unknown frame field {key}")
        count(item)


def validate_succession(operation, facet):
    """The identity transfer law of a Succession facet."""
    signature = operation["signature"]
    require(signature["kind"] == "fixed", "succession requires a fixed signature")
    scope = operation["scope"]

    def unit(port):
        # The scope term of a resource_unit application, or None.
        if "term" in port:
            require(port["term"] < len(scope), "unscoped succession port")
            term = scope[port["term"]]
            if term["kind"] != "apply":
                return None
            constructor, arguments = term["constructor"], term["arguments"]
        else:
            constructor, arguments = port["constructor"], port["arguments"]
        return tuple(arguments) if constructor == "resource_unit" else None

    inputs, outputs = signature["inputs"], signature["outputs"]
    state_input, state_output = facet["stateInput"], facet["stateOutput"]
    require(
        state_input < len(inputs) and state_output < len(outputs),
        "succession port outside signature",
    )
    received, returned = unit(inputs[state_input]), unit(outputs[state_output])
    require(
        received is not None and returned is not None,
        "succession ports must be resource units",
    )
    require(received == returned and len(received) == 1, "succession resource types differ")
    slot = received[0]
    require(
        slot < len(scope)
        and scope[slot]["kind"] == "root"
        and scope[slot]["parameter"] == {"kind": "Domain", "sort": "Slot"},
        "succession requires a Slot root",
    )
    others = [p for i, p in enumerate(inputs) if i != state_input]
    others += [p for i, p in enumerate(outputs) if i != state_output]
    require(
        all(unit(p) is None for p in others),
        "succession operation has another resource unit port",
    )


def validate_type_columns(catalog):
    for row in catalog["types"]:
        collection = row["collection"]
        if collection is None:
            continue
        require(collection["rank"] in (1, 2), "collection rank is 1 or 2")
        if collection["element"] == "parameter":
            parameters = row["parameters"]
            require(
                bool(parameters)
                and (
                    parameters[0] in ({"kind": "Domain", "sort": "Field"}, {"kind": "Domain", "sort": "Group"})
                    or parameters[0]["kind"] == "Type"
                ),
                "parameter collection element requires a Field, Group or Type first parameter",
            )


def unique_rows(rows, key, message):
    result = {}
    for row in rows:
        value = key(row)
        require(value not in result, message)
        result[value] = row
    return result


class Instances:
    """Resolved view of the installed-instance tables for cross-row checks."""

    def __init__(self, catalog):
        self.catalog = catalog
        self.types = {row["name"]: row for row in catalog["types"]}
        self.capabilities = {row["name"]: row for row in catalog["capabilities"]}
        self.domains = unique_rows(catalog["domains"], lambda r: r["identity"], "duplicate domain identity")
        self.codecs = {}
        for row in catalog["codecs"]:
            catalog_name(row["identity"])
            require(
                row["identity"] not in self.domains and row["identity"] not in self.codecs,
                "duplicate identity across domains and codecs",
            )
            self.codecs[row["identity"]] = row
        self.instances = set()
        self.tags = {}

    def member(self, identity, name):
        return dict(self.domains[identity]["members"]).get(name)

    def field(self, identity):
        row = self.domains.get(identity)
        require(row is not None and row["sort"] == "Field", f"{identity} is not a Field domain")
        return row["field"]

    def base_chain(self, identity):
        """Rows from `identity` along BaseField extensions, refusing cycles."""
        chain = [identity]
        while True:
            structure = self.field(chain[-1])["structure"]
            if structure["kind"] != "extension" or structure["over"] != "BaseField":
                return chain
            base = self.member(chain[-1], "BaseField")
            require(base is not None, "BaseField extension requires its BaseField member")
            require(base not in chain, "cyclic BaseField extension")
            chain.append(base)

    def prime_base(self, identity):
        last = self.base_chain(identity)[-1]
        return last if self.field(last)["structure"]["kind"] == "prime" else None

    def convention(self, identity):
        for row in self.base_chain(identity):
            if self.field(row)["twoAdic"] is not None:
                return self.field(row)["twoAdic"]
        return None

    def element_width(self, identity):
        """Canonical element bytes derived from the field structure, if any."""
        facts = self.field(identity)
        structure = facts["structure"]
        characteristic = int(facts["characteristic"])
        if structure["kind"] == "prime":
            return ((characteristic - 1).bit_length() + 7) // 8
        if structure["over"] == "BaseField":
            base = self.element_width(self.member(identity, "BaseField"))
            return None if base is None else structure["degree"] * base
        if characteristic == 2 and structure["degree"] % 8 == 0:
            return structure["degree"] // 8
        return None

    def resolves(self, sort, identity):
        row = self.domains.get(identity)
        return row is not None and row["sort"] == sort


def codec_layout(view, kind, domain):
    """The frame layout a codec's kind fixes, or None when it has none."""
    if kind in KIND_LAYOUTS:
        return KIND_LAYOUTS[kind]
    facts = view.domains[domain].get("commitment") if domain in view.domains else None
    if facts is not None and kind in ("commitment", "proof"):
        return SCHEME_LAYOUTS[facts["scheme"]][kind]
    return None


def validate_domains(view):
    catalog = view.catalog
    sorts = set(catalog["sorts"])
    members = {}
    for row in catalog["members"]:
        members.setdefault((row["owner"]["kind"], row["owner"]["sort"], row["name"]), row["result"])
    conventions = set()
    for row in view.domains.values():
        sort = row["sort"]
        require(sort in sorts and sort not in ("Codec", "Slot"), "invalid domain sort")
        named = {}
        for name, target in row["members"]:
            result = members.get(("Domain", sort, name))
            require(result is not None, f"{name} is not a member of sort {sort}")
            require(name not in named, "duplicate domain member")
            named[name] = target
            require(
                result["kind"] == "Domain"
                and target in view.domains
                and view.domains[target]["sort"] == result["sort"],
                "domain member sort mismatch",
            )
        capabilities = row["capabilities"]
        require(len(capabilities) == len(set(capabilities)), "duplicate capability fact")
        for name in capabilities:
            declared = view.capabilities.get(name)
            require(
                declared is not None
                and declared["parameters"] == [{"kind": "Domain", "sort": sort}],
                f"{name} is not a unary predicate over {sort}",
            )
        for premise, conclusion in catalog["rules"]:
            require(premise not in capabilities or conclusion in capabilities, "capabilities are not closed under rules")
        if "PairingField" in capabilities:
            groups = [named.get(m) for m in ("PairingG1", "PairingG2", "PairingGT")]
            require(
                groups[0] is not None and groups[1] is not None and len(set(filter(None, groups))) == len(list(filter(None, groups))),
                "pairing field requires distinct pairing groups",
            )
            for group in filter(None, groups):
                require(
                    "ScalarAction" in view.domains[group]["capabilities"]
                    and view.member(group, "Scalar") == row["identity"],
                    "pairing group must act with this field as Scalar",
                )
        if "PointField" in named or "EvaluationField" in named:
            require(
                sort == "Commitment" and row["commitment"]["scheme"] == "multilinearKzg",
                "PointField and EvaluationField occur only on multilinear KZG commitments",
            )
        if sort == "Field":
            facts = row["field"]
            characteristic = facts["characteristic"]
            require(len(characteristic) <= 1024 and int(characteristic) >= 2, "invalid characteristic")
            require(
                ("CharacteristicNotTwo" in capabilities) == (characteristic != "2"),
                "CharacteristicNotTwo disagrees with the characteristic",
            )
            structure = facts["structure"]
            prime = structure["kind"] == "prime"
            require(("PrimeField" in capabilities) == prime, "PrimeField disagrees with the structure")
            # Rows over BaseField are exactly the rows holding ExtensionField.
            over_base = not prime and structure["over"] == "BaseField"
            require(("ExtensionField" in capabilities) == over_base, "ExtensionField disagrees with the structure")
            require(("BaseField" in named) == over_base, "exactly the rows over BaseField have a BaseField member")
            if not prime:
                require(structure["degree"] >= 2, "extension degree is at least 2")
                require(bool(structure["reduction"]), "extension reduction is a nonempty list")
                exponents = [e for e, _ in structure["reduction"]]
                require(
                    all(a > b for a, b in zip(exponents, exponents[1:])),
                    "reduction exponents must strictly decrease",
                )
                require(all(e < structure["degree"] for e in exponents), "reduction exponent reaches the degree")
                for _, coefficient in structure["reduction"]:
                    require(
                        coefficient != "0" and int(coefficient) < int(characteristic),
                        "reduction coefficient must be a nonzero prime-subfield element",
                    )
                if over_base:
                    base = named.get("BaseField")
                    require(base is not None, "BaseField extension requires its BaseField member")
                    require(
                        view.field(base)["characteristic"] == characteristic,
                        "BaseField has another characteristic",
                    )
            two_adic = facts["twoAdic"]
            if two_adic is not None:
                require(prime, "a two-adic convention belongs to a prime row")
                require(1 <= two_adic["twoAdicity"] <= 64, "two-adicity is between 1 and 64")
                require(int(two_adic["maximalRoot"]) < int(characteristic), "maximal root is not a field element")
                require(two_adic["convention"] not in conventions, "duplicate coset convention")
                conventions.add(two_adic["convention"])
        if sort == "Transcript":
            facts = row["transcript"]
            require(
                (facts["hash"] == "keccak256") == (facts["family"] == "hash-chain"),
                "keccak256 hash exactly for hash-chain suites",
            )
            require({"Transcript", "FieldTranscript"} <= set(capabilities), "transcript row requires Transcript and FieldTranscript")
            challenge = named.get("ChallengeField")
            require(challenge is not None, "transcript row requires ChallengeField")
            decoder = facts["decoder"]
            challenge_facts = view.field(challenge)
            if decoder in ("fr64be", "scalar64le"):
                require(challenge_facts["structure"]["kind"] == "prime", f"{decoder} requires a prime challenge field")
            if decoder in ("rejection31le", "rejection64le"):
                bound = 2**31 if decoder == "rejection31le" else 2**64
                require(int(challenge_facts["characteristic"]) < bound, f"{decoder} challenge characteristic is too large")
        if sort == "Commitment":
            require("ValueField" in named, "commitment row requires ValueField")
    # Conventions and widths follow BaseField chains; check them once every
    # row's own facts are known.
    for row in view.domains.values():
        if row["sort"] != "Field":
            continue
        require(
            ("TwoAdicField" in row["capabilities"]) == (view.convention(row["identity"]) is not None),
            "TwoAdicField disagrees with the coset convention",
        )


def validate_codecs(view):
    catalog = view.catalog
    for row in catalog["logicalTypes"]:
        kind, domain = row["kind"], row["domain"]
        declared = view.types.get(kind)
        require(declared is not None and kind not in ("variant", "resource_unit"), f"invalid logical type constructor {kind}")
        parameters = declared["parameters"]
        if parameters:
            require(
                len(parameters) == 1
                and parameters[0]["kind"] == "Domain"
                and domain in view.domains
                and view.domains[domain]["sort"] == parameters[0]["sort"],
                f"invalid logical type instance {kind} {domain}",
            )
        else:
            require(domain == "", "a nullary instance has the empty domain")
        require((kind, domain) not in view.instances, "duplicate logical type instance")
        view.instances.add((kind, domain))
        if declared["setup"] is not None:
            require(
                view.domains[domain]["sort"] == "Commitment"
                and view.domains[domain]["commitment"]["scheme"] == "multilinearKzg",
                "setup keys exist only over multilinear KZG commitments",
            )
    for row in catalog["frameTags"]:
        require(1 <= row["tag"] <= 255 and row["tag"] not in view.tags, "invalid or duplicate frame tag")
        view.tags[row["tag"]] = row
        if row["shared"] is not None:
            require(row["shared"]["kind"] in view.types, "shared frame names an undeclared kind")
    users = {tag: [] for tag in view.tags}
    pairs = set()
    for row in catalog["codecs"]:
        kind, domain = row["kind"], row["domain"]
        require((kind, domain) in view.instances, "codec payload is not an admitted logical type")
        require((kind, domain) not in pairs, "second codec for one logical type")
        pairs.add((kind, domain))
        sorts = ["Codec"] + ([view.domains[domain]["sort"]] if domain else [])
        predicate = view.capabilities.get("Encodes." + kind)
        require(
            predicate is not None
            and predicate["parameters"] == [{"kind": "Domain", "sort": s} for s in sorts],
            f"codec kind {kind} lacks its Encodes predicate",
        )
        frame = row["frame"]
        message = view.types[kind]["message"]
        if frame is None:
            require(not message, "a message codec requires a frame")
            continue
        tag = view.tags.get(frame["tag"])
        require(tag is not None, "codec frame names an undeclared tag")
        layout = tag["layout"]
        require(message or layout == "Table", "only the input-only table frame may serve a non-message codec")
        require(layout in CODEC_FRAME_FIELDS, f"layout {layout} carries no codec frame")
        require(layout == codec_layout(view, kind, domain), f"codec kind {kind} fixes its frame layout")
        require(set(frame) == {"tag"} | CODEC_FRAME_FIELDS[layout], "frame fields disagree with the tag layout")
        users[frame["tag"]].append(row)
        if kind in ("field", "vector", "matrix"):
            width = view.element_width(domain)
            require(
                width is not None and frame.get("elementBytes") == width,
                f"{row['identity']} element width disagrees with the field structure",
            )
    by_pair = {(c["kind"], c["domain"]): c for c in catalog["codecs"]}
    for (kind, domain), row in by_pair.items():
        if kind != "group" or ("groups", domain) not in by_pair:
            continue
        frames = [row["frame"], by_pair[("groups", domain)]["frame"]]
        if all(frame is not None for frame in frames):
            widths = [frame.get("elementBytes") for frame in frames]
            require(widths[0] is not None and widths[0] == widths[1], "group and groups codecs disagree on elementBytes")
    aggregates = set()
    for row in catalog["aggregateFrames"]:
        constructor, domain = row["constructor"], row["domain"]
        require(constructor in AGGREGATE_LAYOUTS, f"no aggregate frame for {constructor}")
        if constructor == "field_array":
            require(
                domain in view.domains and view.domains[domain]["sort"] == "Field",
                "field_array frame names a Field domain",
            )
            scalar = by_pair.get(("field", domain))
            require(
                scalar is not None and scalar["frame"] is not None and "elementBytes" in scalar["frame"],
                "field_array frame requires the field's scalar frame",
            )
        else:
            require(domain == "", f"{constructor} frame has the empty domain")
        require((constructor, domain) not in aggregates, "duplicate aggregate frame")
        aggregates.add((constructor, domain))
        tag = view.tags.get(row["tag"])
        require(tag is not None and tag["layout"] == AGGREGATE_LAYOUTS[constructor], "aggregate frame tag layout mismatch")
        users[row["tag"]].append(row)
    for number, tag in view.tags.items():
        used = users[number]
        if tag["shared"] is None:
            require(len(used) == 1, f"frame tag {number} needs exactly one user")
            continue
        kind, scheme = tag["shared"]["kind"], tag["shared"]["scheme"]
        expected = [
            c["identity"]
            for c in catalog["codecs"]
            if c["kind"] == kind
            and c["domain"] in view.domains
            and view.domains[c["domain"]]["sort"] == "Commitment"
            and view.domains[c["domain"]]["commitment"]["scheme"] == scheme
        ]
        require(
            all("identity" in u for u in used)
            and sorted(u["identity"] for u in used) == sorted(expected)
            and len(expected) >= 2,
            f"shared frame tag {number} users disagree with its kind and scheme",
        )
    # Poseidon2 digest words take the permutation field's codec width.
    for row in view.domains.values():
        facts = row.get("commitment")
        if facts is None:
            continue
        if facts["scheme"] in ("keccak256Rows", "poseidon2Rows"):
            require(facts["digestBytes"] == 32, "row commitments have 32-byte digests")
        if facts["scheme"] == "poseidon2Rows":
            field = PERMUTATION_FIELDS[facts["permutation"]]
            value = view.member(row["identity"], "ValueField")
            require(field in (value, view.prime_base(value)), "permutation field is not the value field or its prime base")
            scalar = by_pair.get(("field", field))
            require(
                scalar is not None
                and scalar["frame"] is not None
                and scalar["frame"].get("elementBytes") == facts["digestWordBytes"],
                "digest word width disagrees with the permutation field's codec frame",
            )


def validate_instances(catalog):
    view = Instances(catalog)
    validate_domains(view)
    validate_codecs(view)
    rng = {domain for kind, domain in view.instances if kind == "rng"}
    unique_rows(catalog["randomServices"], lambda r: r["contract"], "duplicate random service contract")
    fields = unique_rows(catalog["randomServices"], lambda r: r["field"], "duplicate random service field")
    for row in catalog["randomServices"]:
        catalog_name(row["contract"])
        view.field(row["field"])
    require(set(fields) == rng, "random services and rng logical types disagree")
    unique_rows(catalog["limits"], lambda r: r["name"], "duplicate limit")
    for row in catalog["limits"]:
        catalog_name(row["name"])
        nonempty(row["owner"])
        nonempty(row["scope"])
    unique_rows(catalog["finiteDefinitions"], lambda r: r["identity"], "duplicate finite definition")
    for row in catalog["finiteDefinitions"]:
        catalog_name(row["identity"])
        require((row["operation"] == "fold") == (row["collection"] is None), "only collect names a collection")
        require(not (row["filtered"] and row["collection"] == "field_array"), "field_array collection cannot be filtered")
    unique_rows(catalog["domainConstructors"], lambda r: r["identity"], "duplicate domain constructor")
    for row in catalog["domainConstructors"]:
        catalog_name(row["identity"])
        require(row["axis"] in (0, 1), "domain constructor axis is 0 or 1")
    return view


def pattern_shape(value):
    require(isinstance(value, list) and value, "expected argument pattern")
    tag = value[0]
    if tag == "any":
        require(len(value) == 1, "malformed any pattern")
    elif tag == "domain":
        require(len(value) == 3, "malformed domain pattern")
        text(value[1])
        text(value[2])
    elif tag == "type":
        require(len(value) == 2, "malformed type pattern")
        type_tree_shape(value[1], 0)
    elif tag == "natRange":
        require(len(value) == 3, "malformed natural range")
        decimal(value[1])
        decimal(value[2])
    else:
        raise ValueError("unknown argument pattern")


def type_tree_shape(value, depth):
    require(depth < 64, "type tree depth limit")
    require(
        isinstance(value, list) and len(value) == 3 and value[0] == "apply",
        "installation type patterns are constructor applications",
    )
    text(value[1])
    require(isinstance(value[2], list), "expected type arguments")
    for argument in value[2]:
        require(isinstance(argument, list) and argument, "expected type argument")
        if argument[0] == "domain":
            require(len(argument) == 3, "malformed domain argument")
            text(argument[1])
            text(argument[2])
        elif argument[0] == "type":
            require(len(argument) == 2, "malformed type argument")
            type_tree_shape(argument[1], depth + 1)
        elif argument[0] == "nat":
            require(len(argument) == 2, "malformed natural argument")
            decimal(argument[1])
        else:
            raise ValueError("unknown type argument")


def validate_installation(installation, catalog):
    """Check the native installation document against its declarations.

    The declaration document must already be valid; its instance tables are
    resolved again here so that every reference checks the referenced facts.
    """
    view = validate_instances(catalog)

    def row(fields):
        return lambda value: record(value, fields)

    record(
        installation,
        {
            "format": one_of("zkc.native-installation/0"),
            "representations": sequence(
                row(
                    {
                        "identity": text,
                        "kind": text,
                        "domain": text,
                        "default": flag,
                        "layout": text,
                        "frame": one_of("canonical", "local"),
                        "unit": one_of(*UNITS),
                    }
                )
            ),
            "appliedRepresentations": sequence(
                row(
                    {
                        "constructor": text,
                        "arguments": sequence(pattern_shape),
                        "identity": text,
                        "default": flag,
                        "child": nullable(row({"kind": text, "domain": text, "representation": text})),
                        "frame": one_of("canonical", "local"),
                        "unit": one_of(*UNITS),
                    }
                )
            ),
            "providers": sequence(
                row(
                    {
                        "domain": text,
                        "default": one_of(*PROVIDERS),
                        "alternatives": sequence(one_of(*PROVIDERS)),
                    }
                )
            ),
            "providerUnits": sequence(row({"provider": one_of(*PROVIDERS), "unit": one_of(*UNITS)})),
            "fieldForms": sequence(
                row(
                    {
                        "field": text,
                        "arithmetic": nullable(row({"form": one_of("residue"), "representation": text})),
                        "montgomery": nullable(row({"wordBytes": count, "radixBits": count})),
                        "byteEncoding": nullable(row({"codec": text, "order": one_of("littleEndian")})),
                    }
                )
            ),
            "physicalArguments": sequence(row({"operation": text})),
        },
    )
    # Providers first: default storage units are checked against them.
    providers = unique_rows(installation["providers"], lambda r: r["domain"], "duplicate provider row")
    for row_ in installation["providers"]:
        require(row_["domain"] in view.domains, "provider row names an undeclared domain")
        names = [row_["default"], *row_["alternatives"]]
        require(len(names) == len(set(names)), "provider appears twice in one row")
    require(set(providers) == set(view.domains), "every domain has exactly one provider row")
    units = {}
    for row_ in installation["providerUnits"]:
        require(row_["provider"] not in units, "duplicate provider unit")
        require(row_["unit"] != "independent", "a provider owns a library unit")
        units[row_["provider"]] = row_["unit"]
    require(set(units) == set(PROVIDERS), "every provider has exactly one unit")
    for provider, unit in STATED_PROVIDER_UNITS.items():
        require(units[provider] == unit, f"{provider} is installed by {unit}")

    # Value bytes can be a codec frame only where the instance has one; the
    # input-only table codec is framed too.
    framed = {(c["kind"], c["domain"]) for c in catalog["codecs"] if c["frame"] is not None}
    keys, defaults, layouts = set(), {}, set()
    for row_ in installation["representations"]:
        catalog_name(row_["identity"])
        instance = (row_["kind"], row_["domain"])
        require(instance in view.instances, "representation names an undeclared logical type instance")
        require((*instance, row_["identity"]) not in keys, "duplicate representation")
        keys.add((*instance, row_["identity"]))
        require(
            row_["frame"] == "local" or instance in framed,
            "a canonical representation requires a framed codec for its instance",
        )
        if row_["default"]:
            require(instance not in defaults, "second default representation")
            defaults[instance] = row_
        if row_["layout"]:
            catalog_name(row_["layout"])
            require((*instance, row_["layout"]) not in layouts, "duplicate representation layout")
            layouts.add((*instance, row_["layout"]))
    for instance in view.instances:
        require(instance in defaults, "logical type instance has no default representation")
    for (kind, domain), row_ in defaults.items():
        if (kind, domain) in framed:
            require(row_["frame"] == "canonical", "the default of a framed instance is canonical")
        expected = units[providers[domain]["default"]] if domain else "independent"
        require(row_["unit"] == expected, "default storage unit disagrees with the default provider")

    def resolved(pattern_or_argument, parameter):
        tag = pattern_or_argument[0]
        if tag == "domain":
            require(
                parameter["kind"] == "Domain"
                and pattern_or_argument[1] == parameter["sort"]
                and view.resolves(parameter["sort"], pattern_or_argument[2]),
                "domain argument disagrees with its parameter",
            )
        elif tag == "type":
            require(parameter["kind"] == "Type", "type argument disagrees with its parameter")
            logical_type(pattern_or_argument[1])
        else:
            require(parameter["kind"] == "Nat", "natural argument disagrees with its parameter")
            values = pattern_or_argument[1:]
            require(all(int(v) <= STATIC_NATURAL_LIMIT for v in values), "natural exceeds the static bound")
            require(int(values[0]) <= int(values[-1]), "empty natural range")

    def logical_type(tree):
        constructor, arguments = tree[1], tree[2]
        domain = ""
        if arguments:
            require(
                len(arguments) == 1 and arguments[0][0] == "domain",
                "type pattern is not a logical type instance",
            )
            require(view.resolves(arguments[0][1], arguments[0][2]), "domain argument disagrees with its parameter")
            domain = arguments[0][2]
        require((constructor, domain) in view.instances, "type pattern is not a logical type instance")

    applied = installation["appliedRepresentations"]
    aggregates = {(row_["constructor"], row_["domain"]) for row_ in catalog["aggregateFrames"]}
    for row_ in applied:
        catalog_name(row_["identity"])
        constructor = row_["constructor"]
        if constructor == "variant":
            parameters, declared = [], None
        else:
            declared = view.types.get(constructor)
            require(declared is not None and declared["parameters"], "applied representation needs a parameterized constructor")
            parameters = declared["parameters"]
        require(len(row_["arguments"]) == len(parameters), "applied representation pattern count differs")
        for pattern, parameter in zip(row_["arguments"], parameters):
            if pattern[0] != "any":
                resolved(pattern, parameter)
        child = row_["child"]
        if child is not None:
            collection = declared["collection"] if declared else None
            first = row_["arguments"][0] if row_["arguments"] else ["any"]
            require(
                collection is not None and collection["element"] == "parameter" and first[0] != "any",
                "a child representation needs a determined dense element",
            )
            if first[0] == "domain":
                element = ({"Field": "field", "Group": "group"}.get(first[1]), first[2])
            else:
                tree = first[1]
                element = (tree[1], tree[2][0][2] if tree[2] and tree[2][0][0] == "domain" else "")
                require(
                    not tree[2] or (len(tree[2]) == 1 and tree[2][0][0] == "domain"),
                    "a dense element is an atomic instance",
                )
            require((child["kind"], child["domain"]) == element, "child is not the logical element")
            require(
                (child["kind"], child["domain"], child["representation"]) in keys,
                "child names no representation row",
            )
        if row_["frame"] == "canonical":
            # field_array frames are granted per field: the row names it exactly.
            first = row_["arguments"][0] if row_["arguments"] else ["any"]
            identity = first[2] if constructor == "field_array" and first[0] == "domain" else ""
            require(
                (constructor == "field_array") == bool(identity)
                and (constructor, identity) in aggregates,
                "a canonical applied representation requires its aggregate frame",
            )

    def overlaps(left, right):
        if left[0] == "any" or right[0] == "any":
            return True
        if left[0] == "natRange" and right[0] == "natRange":
            return int(left[1]) <= int(right[2]) and int(right[1]) <= int(left[2])
        return left == right

    for i, row_ in enumerate(applied):
        for other in applied[:i]:
            if other["constructor"] != row_["constructor"]:
                continue
            if all(overlaps(a, b) for a, b in zip(row_["arguments"], other["arguments"])):
                require(row_["identity"] != other["identity"], "overlapping applied representations share an identity")
                require(not (row_["default"] and other["default"]), "overlapping applied representations are both defaults")

    forms = unique_rows(installation["fieldForms"], lambda r: r["field"], "duplicate field form")
    for field, row_ in forms.items():
        facts = view.field(field)
        arithmetic, montgomery, encoding = row_["arithmetic"], row_["montgomery"], row_["byteEncoding"]
        if arithmetic is not None:
            default = defaults.get(("field", field))
            require(
                default is not None and default["identity"] == arithmetic["representation"],
                "residue arithmetic names the field's default representation",
            )
        if montgomery is not None:
            require(arithmetic is not None, "Montgomery words require residue arithmetic")
            require(montgomery["wordBytes"] * 8 == montgomery["radixBits"], "Montgomery radix is the word width")
            require(int(facts["characteristic"]) < 2 ** montgomery["radixBits"], "characteristic exceeds the Montgomery radix")
        if encoding is not None:
            codec = view.codecs.get(encoding["codec"])
            require(
                codec is not None
                and codec["kind"] == "field"
                and codec["domain"] == field
                and codec["frame"] is not None,
                "byte encoding names the field's framed field codec",
            )
    operations = {row_["name"] for row_ in catalog["operations"]}
    unique_rows(installation["physicalArguments"], lambda r: r["operation"], "duplicate physical argument row")
    for row_ in installation["physicalArguments"]:
        require(row_["operation"] in operations, "physical argument row names an undeclared operation")


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate key {key}")
        result[key] = value
    return result


def load(path):
    data = path.read_bytes()
    require(len(data) <= 64 * 1024 * 1024, "declaration byte limit")
    return json.loads(data, object_pairs_hook=unique)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--installation", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    catalog = load(args.source)
    installation = load(args.installation)
    validate(catalog)
    validate_installation(installation, catalog)
    declarations, mathematical, native = project(catalog, installation)
    args.output.mkdir(parents=True, exist_ok=True)
    for name, content in (
        ("Catalog.td", declarations),
        ("Mathematical.td", mathematical),
        ("NativeInstallation.td", native),
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
