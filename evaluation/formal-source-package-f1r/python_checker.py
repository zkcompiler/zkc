#!/usr/bin/env python3
"""Independent stdlib-only checker for the temporary F1-R package."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterable


FORMAT = "zkc.formal-source-package.f1r.v0"
CONTRACT_SCHEMA = "zkc.formal-source-contract.f1r.v0"
CONTRACT_DOMAIN = "zkc/f1r/contract/v0"
AUTH_DOMAIN = "zkc/f1r/auth-node/v0"
PACKAGE_DOMAIN = "zkc/f1r/package/v0"
MANIFEST_DOMAIN = "zkc/f1r/manifest/v0"
PROPOSITION_DOMAIN = "zkc/f1r/proposition/v0"
RESULT_DOMAIN = "zkc/f1r/result/v0"
MAX_WIRE_BYTES = 1 << 20
MAX_DEPTH = 64
MAX_AUTH_NODES = 128
MAX_READS = 512
U64_MAX = (1 << 64) - 1
EXPECTED_EXCLUSIONS = (
    "CausalCapability",
    "ConfidentialValue",
    "MutablePlanState",
    "SecretWitnessValue",
)
DIGEST_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")


Json = Any


class Finding(Exception):
    def __init__(self, outcome_class: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome_class = outcome_class
        self.code = code
        self.detail = detail


class DuplicateKey(ValueError):
    pass


def fail(outcome_class: str, code: str, detail: str) -> None:
    raise Finding(outcome_class, code, detail)


def strict_object(pairs: list[tuple[str, Json]]) -> dict[str, Json]:
    result: dict[str, Json] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKey(key)
        result[key] = value
    return result


def parse_u64(text: str) -> int:
    value = int(text, 10)
    if value > U64_MAX:
        raise ValueError("integer exceeds u64")
    return value


def reject_number(_: str) -> Json:
    raise ValueError("non-u64 JSON number")


def load_wire(path: Path) -> Json:
    try:
        raw = path.read_bytes()
    except OSError as error:
        fail("Malformed", "F1R-M-IO", str(error))
    if len(raw) > MAX_WIRE_BYTES:
        fail(
            "DeterministicLimitExceeded",
            "F1R-L-WIRE",
            "wire exceeds the fixed 1 MiB bound",
        )
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        fail("Malformed", "F1R-M-UTF8", "wire is not UTF-8")
    try:
        value = json.loads(
            text,
            object_pairs_hook=strict_object,
            parse_int=parse_u64,
            parse_float=reject_number,
            parse_constant=reject_number,
        )
    except DuplicateKey as error:
        fail(
            "Malformed",
            "F1R-M-DUPLICATE-KEY",
            f"duplicate JSON object key {error.args[0]!r}",
        )
    except RecursionError:
        fail(
            "DeterministicLimitExceeded",
            "F1R-L-DEPTH",
            "wire nesting exceeds the parser bound",
        )
    except (json.JSONDecodeError, ValueError) as error:
        fail("Malformed", "F1R-M-JSON", str(error))
    validate_value(value, 0)
    return value


def validate_symbol(value: Json, label: str) -> str:
    if type(value) is not str or not value:
        fail("Malformed", "F1R-M-SCHEMA", f"{label} is not nonempty text")
    try:
        raw = value.encode("ascii")
    except UnicodeEncodeError:
        fail("Malformed", "F1R-M-SCHEMA", f"{label} is not ASCII")
    if any(byte < 0x20 or byte > 0x7E for byte in raw):
        fail(
            "Malformed",
            "F1R-M-SCHEMA",
            f"{label} contains a non-printable ASCII octet",
        )
    return value


def validate_value(value: Json, depth: int) -> None:
    if depth > MAX_DEPTH:
        fail(
            "DeterministicLimitExceeded",
            "F1R-L-DEPTH",
            "decoded value exceeds depth 64",
        )
    if value is None or type(value) is bool:
        return
    if type(value) is int:
        if not 0 <= value <= U64_MAX:
            fail("Malformed", "F1R-M-SCHEMA", "integer is not a u64")
        return
    if type(value) is str:
        validate_symbol(value, "string")
        return
    if type(value) is list:
        for item in value:
            validate_value(item, depth + 1)
        return
    if type(value) is dict:
        for key, item in value.items():
            validate_symbol(key, "object key")
            validate_value(item, depth + 1)
        return
    fail("Malformed", "F1R-M-SCHEMA", "unsupported decoded JSON value")


def quote_ascii(value: str) -> bytes:
    output = bytearray(b'"')
    for byte in value.encode("ascii"):
        if byte in (0x22, 0x5C):
            output.append(0x5C)
        output.append(byte)
    output.append(0x22)
    return bytes(output)


def canonical(value: Json) -> bytes:
    """Checker-local canonical encoder, independent of the exporter."""

    if value is None:
        return b"null"
    if type(value) is bool:
        return b"true" if value else b"false"
    if type(value) is int:
        return str(value).encode("ascii")
    if type(value) is str:
        return quote_ascii(value)
    if type(value) is list:
        return b"[" + b",".join(canonical(item) for item in value) + b"]"
    if type(value) is dict:
        fields = []
        for key in sorted(value, key=lambda item: item.encode("ascii")):
            fields.append(quote_ascii(key) + b":" + canonical(value[key]))
        return b"{" + b",".join(fields) + b"}"
    fail("Malformed", "F1R-M-SCHEMA", "cannot canonically encode value")


def value_id(domain: str, value: Json) -> str:
    digest = hashlib.sha256(
        domain.encode("ascii") + b"\x00" + canonical(value)
    ).hexdigest()
    return f"sha256:{digest}"


def exact_object(value: Json, fields: Iterable[str], label: str) -> dict[str, Json]:
    if type(value) is not dict:
        fail("Malformed", "F1R-M-SCHEMA", f"{label} is not an object")
    expected = set(fields)
    actual = set(value)
    if actual != expected:
        fail(
            "Malformed",
            "F1R-M-SCHEMA",
            f"{label} fields differ: missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}",
        )
    return value


def sequence(value: Json, label: str) -> list[Json]:
    if type(value) is not list:
        fail("Malformed", "F1R-M-SCHEMA", f"{label} is not an array")
    return value


def u64(value: Json, label: str) -> int:
    if type(value) is not int or not 0 <= value <= U64_MAX:
        fail("Malformed", "F1R-M-SCHEMA", f"{label} is not a u64")
    return value


def digest(value: Json, label: str) -> str:
    text = validate_symbol(value, label)
    if DIGEST_RE.fullmatch(text) is None:
        fail("Malformed", "F1R-M-DIGEST", f"{label} is not a SHA-256 ID")
    return text


def sorted_unique_strings(value: Json, label: str) -> list[str]:
    result = [validate_symbol(item, f"{label} item") for item in sequence(value, label)]
    if result != sorted(set(result), key=lambda item: item.encode("ascii")):
        fail(
            "Malformed",
            "F1R-M-NONCANONICAL-SEQUENCE",
            f"{label} is not sorted-unique",
        )
    return result


def rows_by_coordinate(
    value: Json,
    fields: Iterable[str],
    label: str,
) -> tuple[list[dict[str, Json]], dict[str, dict[str, Json]]]:
    rows: list[dict[str, Json]] = []
    coordinates: list[str] = []
    for ordinal, item in enumerate(sequence(value, label)):
        row = exact_object(item, fields, f"{label} row {ordinal}")
        coordinate = validate_symbol(row["coordinate"], f"{label} coordinate")
        rows.append(row)
        coordinates.append(coordinate)
    if coordinates != sorted(set(coordinates), key=lambda item: item.encode("ascii")):
        fail(
            "Malformed",
            "F1R-M-NONCANONICAL-SEQUENCE",
            f"{label} is not coordinate-sorted-unique",
        )
    return rows, dict(zip(coordinates, rows, strict=True))


def validate_shape(package_value: Json) -> dict[str, Json]:
    package = exact_object(
        package_value,
        (
            "asserted_package_id",
            "authentication",
            "contract",
            "format",
            "ledger",
            "manifest",
            "projection",
            "semantic_profile",
        ),
        "package",
    )
    if validate_symbol(package["format"], "package format") != FORMAT:
        fail("Malformed", "F1R-M-SCHEMA", "unsupported package format")
    validate_symbol(package["semantic_profile"], "package semantic profile")
    digest(package["asserted_package_id"], "asserted package ID")

    contract = exact_object(package["contract"], ("asserted_id", "body"), "contract")
    digest(contract["asserted_id"], "contract asserted ID")
    body = exact_object(
        contract["body"],
        (
            "contract_schema",
            "excluded_support_kinds",
            "finite_controls",
            "package_schema",
            "protected_observations",
            "read_catalog",
            "read_roots",
            "root_requirements",
            "semantic_profile",
        ),
        "contract body",
    )
    if validate_symbol(body["contract_schema"], "contract schema") != CONTRACT_SCHEMA:
        fail("Malformed", "F1R-M-SCHEMA", "unsupported contract schema")
    if validate_symbol(body["package_schema"], "contract package schema") != FORMAT:
        fail("Malformed", "F1R-M-SCHEMA", "contract names another package schema")
    validate_symbol(body["semantic_profile"], "contract semantic profile")
    exclusions = sorted_unique_strings(
        body["excluded_support_kinds"], "excluded support kinds"
    )
    if tuple(exclusions) != EXPECTED_EXCLUSIONS:
        fail("Malformed", "F1R-M-SCHEMA", "wrong excluded-support catalog")
    observations = body["protected_observations"]
    if type(observations) is not dict or not observations:
        fail(
            "Malformed",
            "F1R-M-SCHEMA",
            "protected observations are not a nonempty object",
        )
    for observation, covered_reads in observations.items():
        validate_symbol(observation, "protected observation")
        if not sorted_unique_strings(
            covered_reads, f"protected observation {observation} reads"
        ):
            fail(
                "Malformed",
                "F1R-M-SCHEMA",
                f"protected observation {observation} covers no reads",
            )
    sorted_unique_strings(body["read_roots"], "read roots")

    controls = exact_object(
        body["finite_controls"],
        ("max_auth_nodes", "max_depth", "max_reads", "max_wire_bytes"),
        "finite controls",
    )
    expected_controls = {
        "max_auth_nodes": MAX_AUTH_NODES,
        "max_depth": MAX_DEPTH,
        "max_reads": MAX_READS,
        "max_wire_bytes": MAX_WIRE_BYTES,
    }
    for key, expected in expected_controls.items():
        if u64(controls[key], f"finite control {key}") != expected:
            fail("Malformed", "F1R-M-SCHEMA", f"finite control {key} differs")

    requirements, _ = rows_by_coordinate(
        body["root_requirements"],
        ("coordinate", "kind", "profile"),
        "root requirements",
    )
    for row in requirements:
        validate_symbol(row["kind"], "root requirement kind")
        validate_symbol(row["profile"], "root requirement profile")

    read_rows, _ = rows_by_coordinate(
        body["read_catalog"],
        ("coordinate", "requires", "source_node", "source_pointer", "value_kind"),
        "read catalog",
    )
    if len(read_rows) > MAX_READS:
        fail(
            "DeterministicLimitExceeded",
            "F1R-L-READS",
            "read catalog exceeds its fixed bound",
        )
    for row in read_rows:
        validate_symbol(row["source_node"], "read source node")
        validate_symbol(row["source_pointer"], "read source pointer")
        validate_symbol(row["value_kind"], "read value kind")
        sorted_unique_strings(row["requires"], "read requirements")

    authentication = exact_object(
        package["authentication"], ("nodes", "roots"), "authentication"
    )
    sorted_unique_strings(authentication["roots"], "authentication roots")
    node_rows, _ = rows_by_coordinate(
        authentication["nodes"],
        ("asserted_id", "body", "coordinate", "dependencies", "kind", "profile"),
        "authentication nodes",
    )
    if len(node_rows) > MAX_AUTH_NODES:
        fail(
            "DeterministicLimitExceeded",
            "F1R-L-AUTH-NODES",
            "authentication closure exceeds its fixed bound",
        )
    for row in node_rows:
        digest(row["asserted_id"], "authentication node asserted ID")
        validate_symbol(row["kind"], "authentication node kind")
        validate_symbol(row["profile"], "authentication node profile")
        sorted_unique_strings(row["dependencies"], "authentication dependencies")
        node_body = row["body"]
        if type(node_body) is not dict:
            fail("Malformed", "F1R-M-SCHEMA", "authentication body is not an object")
        if "imports" not in node_body:
            fail("Malformed", "F1R-M-SCHEMA", "authentication body has no imports")
        sorted_unique_strings(node_body["imports"], "authentication imports")

    sorted_unique_strings(package["manifest"], "package manifest")
    projection_rows, _ = rows_by_coordinate(
        package["projection"],
        ("coordinate", "source_node", "source_pointer", "value", "value_kind"),
        "projection",
    )
    ledger_rows, _ = rows_by_coordinate(
        package["ledger"],
        ("coordinate", "source_node", "source_pointer"),
        "ledger",
    )
    if len(projection_rows) > MAX_READS or len(ledger_rows) > MAX_READS:
        fail(
            "DeterministicLimitExceeded",
            "F1R-L-READS",
            "realized reads exceed their fixed bound",
        )
    for row in projection_rows:
        validate_symbol(row["source_node"], "projection source node")
        validate_symbol(row["source_pointer"], "projection source pointer")
        validate_symbol(row["value_kind"], "projection value kind")
    for row in ledger_rows:
        validate_symbol(row["source_node"], "ledger source node")
        validate_symbol(row["source_pointer"], "ledger source pointer")
    return package


def package_without_id(package: dict[str, Json]) -> dict[str, Json]:
    return {key: value for key, value in package.items() if key != "asserted_package_id"}


def authenticate_nodes(
    package: dict[str, Json], contract_body: dict[str, Json]
) -> tuple[dict[str, str], list[dict[str, str]]]:
    authentication = package["authentication"]
    nodes = {
        str(row["coordinate"]): row for row in authentication["nodes"]
    }
    roots = [str(item) for item in authentication["roots"]]
    memo: dict[str, str] = {}
    active: set[str] = set()

    def compute(coordinate: str) -> str:
        if coordinate in memo:
            return memo[coordinate]
        if coordinate in active:
            fail("Malformed", "F1R-M-AUTH-CYCLE", "authentication graph is cyclic")
        current = nodes.get(coordinate)
        if current is None:
            fail(
                "Negative",
                "F1R-N-MISSING-AUTH-NODE",
                f"missing authentication node {coordinate}",
            )
        active.add(coordinate)
        dependencies = [str(item) for item in current["dependencies"]]
        imports = [str(item) for item in current["body"]["imports"]]
        if imports != dependencies:
            fail(
                "Negative",
                "F1R-N-AUTH-DEPENDENCY",
                f"node {coordinate} imports and dependencies disagree",
            )
        dependencies = []
        for dependency_value in current["dependencies"]:
            dependency = str(dependency_value)
            dependencies.append(
                {"coordinate": dependency, "id": compute(dependency)}
            )
        preimage = {
            "body": current["body"],
            "coordinate": coordinate,
            "dependencies": dependencies,
            "kind": current["kind"],
            "profile": current["profile"],
        }
        computed = value_id(AUTH_DOMAIN, preimage)
        active.remove(coordinate)
        if computed != current["asserted_id"]:
            fail(
                "Negative",
                "F1R-N-AUTH-ID",
                f"authentication ID mismatch at {coordinate}",
            )
        memo[coordinate] = computed
        return computed

    for coordinate in roots:
        compute(coordinate)
    reached = set(memo)
    all_nodes = set(nodes)
    if reached != all_nodes:
        missing = sorted(all_nodes - reached)
        fail(
            "Negative",
            "F1R-N-EXTRA-AUTH-NODE",
            f"unreachable authentication nodes {missing}",
        )

    requirements = {
        str(row["coordinate"]): row for row in contract_body["root_requirements"]
    }
    if set(roots) != set(requirements):
        fail(
            "Negative",
            "F1R-N-ROOT-SET",
            "authentication roots differ from contract roots",
        )
    for coordinate in roots:
        node_row = nodes[coordinate]
        requirement = requirements[coordinate]
        if (
            node_row["kind"] != requirement["kind"]
            or node_row["profile"] != requirement["profile"]
        ):
            fail(
                "KindMismatch",
                "F1R-K-ROOT",
                f"root kind/profile mismatch at {coordinate}",
            )
    root_ids = [
        {"coordinate": coordinate, "id": memo[coordinate]}
        for coordinate in roots
    ]
    return memo, root_ids


def required_reads(contract_body: dict[str, Json]) -> list[str]:
    catalog = {
        str(row["coordinate"]): row for row in contract_body["read_catalog"]
    }
    seen: set[str] = set()
    active: set[str] = set()

    def visit(coordinate: str) -> None:
        if coordinate in seen:
            return
        if coordinate in active:
            fail("Malformed", "F1R-M-READ-CYCLE", "read graph is cyclic")
        row = catalog.get(coordinate)
        if row is None:
            fail(
                "Malformed",
                "F1R-M-SCHEMA",
                f"read graph names unknown coordinate {coordinate}",
            )
        active.add(coordinate)
        for dependency in row["requires"]:
            visit(str(dependency))
        active.remove(coordinate)
        seen.add(coordinate)

    for root in contract_body["read_roots"]:
        visit(str(root))
    expected = sorted(seen, key=lambda item: item.encode("ascii"))
    if set(catalog) != seen:
        fail(
            "Malformed",
            "F1R-M-READ-CLOSURE",
            "read catalog contains a coordinate outside the required closure",
        )

    source_bindings: set[tuple[str, str]] = set()
    for coordinate, row in catalog.items():
        binding = (str(row["source_node"]), str(row["source_pointer"]))
        if binding in source_bindings:
            fail(
                "Malformed",
                "F1R-M-ALIASED-SOURCE",
                f"read catalog aliases source binding {binding} at {coordinate}",
            )
        source_bindings.add(binding)

    covered: set[str] = set()
    observations = contract_body["protected_observations"]
    for observation, raw_reads in observations.items():
        reads = sorted_unique_strings(
            raw_reads, f"protected observation {observation} reads"
        )
        unknown = set(reads) - seen
        if unknown:
            fail(
                "Malformed",
                "F1R-M-OBSERVATION-COVERAGE",
                f"protected observation {observation} names unknown reads",
            )
        covered.update(reads)
    if covered != seen:
        fail(
            "Malformed",
            "F1R-M-OBSERVATION-COVERAGE",
            "protected observations do not cover the exact read closure",
        )
    return expected


def decode_pointer_token(token: str) -> str:
    output: list[str] = []
    index = 0
    while index < len(token):
        if token[index] != "~":
            output.append(token[index])
            index += 1
            continue
        if index + 1 >= len(token) or token[index + 1] not in "01":
            fail("Malformed", "F1R-M-POINTER", "invalid JSON Pointer escape")
        output.append("~" if token[index + 1] == "0" else "/")
        index += 2
    return "".join(output)


def select_pointer(node_body: Json, pointer: str) -> Json:
    if not pointer.startswith("/body"):
        fail("Malformed", "F1R-M-POINTER", "source pointer is not rooted at /body")
    current: Json = {"body": node_body}
    for encoded in pointer.split("/")[1:]:
        token = decode_pointer_token(encoded)
        if type(current) is dict:
            if token not in current:
                fail(
                    "Negative",
                    "F1R-N-SOURCE-SELECTION",
                    f"source pointer {pointer} selects no object field",
                )
            current = current[token]
        elif type(current) is list:
            if not token.isdigit() or (len(token) > 1 and token[0] == "0"):
                fail("Malformed", "F1R-M-POINTER", "noncanonical array index")
            index = int(token, 10)
            if index >= len(current):
                fail(
                    "Negative",
                    "F1R-N-SOURCE-SELECTION",
                    f"source pointer {pointer} exceeds its array",
                )
            current = current[index]
        else:
            fail(
                "Negative",
                "F1R-N-SOURCE-SELECTION",
                f"source pointer {pointer} descends through a scalar",
            )
    return current


def compare_reads(package: dict[str, Json], contract_body: dict[str, Json]) -> list[str]:
    expected = required_reads(contract_body)
    manifest = [str(item) for item in package["manifest"]]
    missing = sorted(set(expected) - set(manifest))
    if missing:
        fail(
            "Negative",
            "F1R-N-MISSING-READ",
            f"missing required reads {missing}",
        )
    extra = sorted(set(manifest) - set(expected))
    if extra:
        fail("Negative", "F1R-N-EXTRA-READ", f"extra reads {extra}")
    if manifest != expected:
        fail("Malformed", "F1R-M-NONCANONICAL-SEQUENCE", "manifest order differs")

    projection = {
        str(row["coordinate"]): row for row in package["projection"]
    }
    ledger = {str(row["coordinate"]): row for row in package["ledger"]}
    for actual, label in ((projection, "projection"), (ledger, "ledger")):
        missing = sorted(set(expected) - set(actual))
        if missing:
            fail(
                "Negative",
                "F1R-N-MISSING-READ",
                f"{label} misses required reads {missing}",
            )
        extra = sorted(set(actual) - set(expected))
        if extra:
            fail("Negative", "F1R-N-EXTRA-READ", f"{label} has extra reads {extra}")

    catalog = {
        str(row["coordinate"]): row for row in contract_body["read_catalog"]
    }
    nodes = {
        str(row["coordinate"]): row
        for row in package["authentication"]["nodes"]
    }
    for coordinate in expected:
        specification = catalog[coordinate]
        projected = projection[coordinate]
        recorded = ledger[coordinate]
        source_node = specification["source_node"]
        source_pointer = specification["source_pointer"]
        binding = (source_node, source_pointer)
        if (
            projected["source_node"],
            projected["source_pointer"],
        ) != binding or (
            recorded["source_node"],
            recorded["source_pointer"],
        ) != binding:
            fail(
                "Negative",
                "F1R-N-COORDINATE-BINDING",
                f"source binding mismatch at {coordinate}",
            )
        if projected["value_kind"] != specification["value_kind"]:
            fail(
                "KindMismatch",
                "F1R-K-VALUE",
                f"value kind mismatch at {coordinate}",
            )
        source = nodes.get(str(source_node))
        if source is None:
            fail(
                "Negative",
                "F1R-N-MISSING-AUTH-NODE",
                f"read source node {source_node} is absent",
            )
        selected = select_pointer(source["body"], str(source_pointer))
        if projected["value"] != selected:
            if coordinate == "view.shared-challenge.binding":
                code = "F1R-N-SHARED-CHALLENGE"
            elif coordinate == "view.execution.order":
                code = "F1R-N-EXECUTION-ORDER"
            else:
                code = "F1R-N-OBSERVATION-VALUE"
            fail("Negative", code, f"projected value mismatch at {coordinate}")
    return expected


def check(package_value: Json) -> dict[str, Json]:
    package = validate_shape(package_value)
    contract = package["contract"]
    contract_body_value = contract["body"]

    excluded = set(contract_body_value["excluded_support_kinds"])
    for row in package["projection"]:
        if row["value_kind"] in excluded:
            fail(
                "Refused",
                "F1R-R-EXCLUDED-SUPPORT",
                f"projection {row['coordinate']} serializes excluded support",
            )

    if package["semantic_profile"] != contract_body_value["semantic_profile"]:
        fail(
            "KindMismatch",
            "F1R-K-PROFILE",
            "package and contract semantic profiles differ",
        )

    computed_contract_id = value_id(CONTRACT_DOMAIN, contract_body_value)
    if contract["asserted_id"] != computed_contract_id:
        fail("Negative", "F1R-N-CONTRACT-ID", "contract ID mismatch")

    computed_package_id = value_id(PACKAGE_DOMAIN, package_without_id(package))
    if package["asserted_package_id"] != computed_package_id:
        fail("Negative", "F1R-N-PACKAGE-ID", "package ID mismatch")

    _, root_ids = authenticate_nodes(package, contract_body_value)
    reads = compare_reads(package, contract_body_value)
    manifest_id = value_id(MANIFEST_DOMAIN, reads)
    proposition = {
        "contract_id": computed_contract_id,
        "direction": "ExactSemanticReadAgreement",
        "manifest_id": manifest_id,
        "package_id": computed_package_id,
        "root_ids": root_ids,
        "semantic_profile": package["semantic_profile"],
    }
    proposition_id = value_id(PROPOSITION_DOMAIN, proposition)
    agreement: dict[str, Json] = {
        "class": "Affirmative",
        "code": "F1R-AFFIRMATIVE",
        "contract_id": computed_contract_id,
        "manifest_id": manifest_id,
        "package_id": computed_package_id,
        "proposition_id": proposition_id,
        "required_reads": reads,
        "root_ids": root_ids,
    }
    agreement["result_id"] = value_id(RESULT_DOMAIN, agreement)
    return agreement


def emit(checker: str, outcome: dict[str, Json]) -> None:
    print(
        json.dumps(
            {"checker": checker, "outcome": outcome},
            ensure_ascii=True,
            separators=(",", ":"),
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if len(args) != 1:
        emit(
            "python-stdlib-v0",
            {"class": "Malformed", "code": "F1R-M-INVOCATION"},
        )
        return 2
    try:
        package = load_wire(Path(args[0]))
        outcome = check(package)
        emit("python-stdlib-v0", outcome)
        return 0
    except Finding as finding:
        print(f"python checker: {finding.detail}", file=sys.stderr)
        emit(
            "python-stdlib-v0",
            {"class": finding.outcome_class, "code": finding.code},
        )
        return 1 if finding.outcome_class == "Negative" else 2
    except Exception as error:  # pragma: no cover - implementation failure path
        print(f"python checker failed: {error}", file=sys.stderr)
        emit(
            "python-stdlib-v0",
            {"class": "CheckerFailure", "code": "F1R-CHECKER-FAILURE"},
        )
        return 3


if __name__ == "__main__":
    raise SystemExit(main())
