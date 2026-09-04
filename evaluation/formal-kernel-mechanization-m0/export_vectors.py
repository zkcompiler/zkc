#!/usr/bin/env python3
"""Export the golden vectors the M0 mechanized kernel definition spike compares.

Three sources feed the vectors:

- the frozen K1 oracle JSONL cases under
  ``evaluation/k1-executable-foundations/oracle/cases`` (every case whose
  expected record carries a canonical body, plus the two malformed decode
  cases), in the oracle's own JSON value transport;
- crafted noncanonical octet strings, one per malformation the Foundation page
  names (``docs-next/foundation/executable-foundations.md`` Section 2.1), each
  confirmed refused by the K1 Python decoder at export time; and
- the five D1 carriers of
  ``evaluation/formal-source-integrated-graph-f0v2b2d1``: their profiled Core
  bodies and ``PublicCoinView`` bodies (pinned by digest and regenerated at
  check time because they total about 430 KiB), plus canonical admitted-Core
  and used semantic-module declaration bytes as construction inputs. Every
  graph table is a frozen expected output, never a Lean construction input.

The export is deterministic. ``run.py`` regenerates it into a scratch
directory and compares the result with the committed files, so a drift in
either predecessor package is reported rather than silently absorbed.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
VECTORS = HERE / "vectors"
K1_MODEL = ROOT / "evaluation/k1-executable-foundations/reference_model.py"
ORACLE_CASES = ROOT / "evaluation/k1-executable-foundations/oracle/cases"
D1_MODEL = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/model.py"
D1_M1_EXPORT = ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/export_m1_vectors.py"

CLASS_NAMES = ("StaticPublic", "PublicHistory", "VerifierPrivate", "Invalid")


class ExportError(RuntimeError):
    """A predecessor package no longer yields the export this package expects."""


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise ExportError(detail)


# --- datum <-> oracle JSON transport -------------------------------------------


def datum_of_transport(k1: ModuleType, raw: Any) -> Any:
    """The oracle's JSON value transport, read as a K1 datum."""

    _require(isinstance(raw, dict), "transport datum must be an object")
    tag = raw.get("tag")
    if tag == "unit":
        return k1.UNIT
    if tag == "bool":
        _require(type(raw["value"]) is bool, "bool transport must be a JSON boolean")
        return raw["value"]
    if tag == "nat":
        return k1.Nat(int(raw["value"]))
    if tag == "int":
        return k1.IntValue(int(raw["value"]))
    if tag == "bytes":
        return k1.BytesValue(bytes.fromhex(str(raw["value"])))
    if tag == "symbol":
        return k1.Symbol(str(raw["value"]))
    if tag == "seq":
        return k1.DatumSeq(tuple(datum_of_transport(k1, item) for item in raw["items"]))
    if tag == "record":
        return k1.DatumRecord(
            tuple(
                (int(field["ordinal"]), datum_of_transport(k1, field["value"]))
                for field in raw["fields"]
            )
        )
    if tag == "variant":
        return k1.DatumVariant(int(raw["case"]), datum_of_transport(k1, raw["value"]))
    raise ExportError(f"unknown transport tag {tag!r}")


def transport_of_datum(k1: ModuleType, value: Any) -> Any:
    """A K1 datum, written in the oracle's JSON value transport."""

    if type(value) is k1.Unit:
        return {"tag": "unit"}
    if type(value) is bool:
        return {"tag": "bool", "value": value}
    if type(value) is k1.Nat:
        return {"tag": "nat", "value": str(value.value)}
    if type(value) is k1.IntValue:
        return {"tag": "int", "value": str(value.value)}
    if type(value) is k1.BytesValue:
        return {"tag": "bytes", "value": value.value.hex()}
    if type(value) is k1.Symbol:
        return {"tag": "symbol", "value": value.value}
    if type(value) is k1.DatumSeq:
        return {"tag": "seq", "items": [transport_of_datum(k1, item) for item in value.values]}
    if type(value) is k1.DatumRecord:
        return {
            "tag": "record",
            "fields": [
                {"ordinal": str(ordinal), "value": transport_of_datum(k1, child)}
                for ordinal, child in value.fields
            ],
        }
    if type(value) is k1.DatumVariant:
        return {
            "tag": "variant",
            "case": str(value.case),
            "value": transport_of_datum(k1, value.payload),
        }
    raise ExportError(f"unsupported datum carrier {type(value)!r}")


# --- K1 oracle vectors -----------------------------------------------------------


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def k1_oracle_vectors(k1: ModuleType) -> dict[str, Any]:
    requests = _read_jsonl(ORACLE_CASES / "requests.jsonl")
    expected = _read_jsonl(ORACLE_CASES / "expected.jsonl")
    _require(len(requests) == len(expected), "oracle request/expected line counts differ")
    encode: list[dict[str, Any]] = []
    reject: list[dict[str, Any]] = []
    skipped: list[dict[str, str]] = []
    for request, record in zip(requests, expected):
        _require(request["case"] == record["case"], "oracle case names diverge")
        case = request["case"]
        if record["outcome"] == "Completed" and "canonical_hex" in record:
            value = record["value"] if request["op"] == "decode" else request["value"]
            datum = datum_of_transport(k1, value)
            hex_body = record["canonical_hex"]
            _require(
                k1.encode_datum(datum).hex() == hex_body,
                f"K1 reference encoder disagrees with the frozen oracle body for {case}",
            )
            encode.append(
                {
                    "name": f"k1-oracle/{case}",
                    "source": "k1-oracle",
                    "op": request["op"],
                    "value": value,
                    "hex": hex_body,
                }
            )
        elif request["op"] == "decode" and record["outcome"] == "Malformed":
            hex_body = request["canonical_hex"]
            try:
                k1.decode_datum(bytes.fromhex(hex_body))
            except k1.CanonicalError:
                pass
            else:
                raise ExportError(f"K1 reference decoder accepts the oracle's malformed {case}")
            reject.append(
                {
                    "name": f"k1-oracle/{case}",
                    "source": "k1-oracle",
                    "hex": hex_body,
                    "oracle_code": record["code"],
                }
            )
        else:
            skipped.append(
                {
                    "case": case,
                    "op": request["op"],
                    "outcome": record["outcome"],
                    "reason": (
                        "oracle-local resource profile, not a constitutional rule"
                        if record["outcome"] == "ResourceExceeded"
                        else "identity or refusal vector without a canonical body"
                    ),
                }
            )
    boundary = json.loads((ORACLE_CASES / "natural-byte-bound.json").read_text(encoding="utf-8"))
    _require(
        [item["expected"]["outcome"] for item in boundary["vectors"]]
        == ["Completed", "Malformed"],
        "natural byte-bound vectors are not one positive and one negative case",
    )
    return {"encode": encode, "reject": reject, "skipped": skipped, "boundary": boundary}


# --- crafted noncanonical inputs -------------------------------------------------


def _u64(n: int) -> bytes:
    return n.to_bytes(8, "big")


def _frame(body: bytes) -> bytes:
    return _u64(len(body)) + body


def structural_negatives(k1: ModuleType) -> list[dict[str, Any]]:
    nat_one = b"\x03" + _frame(b"\x01")
    unit = b"\x00"
    crafted: list[tuple[str, str, bytes]] = [
        ("unknown-tag", "unknown tag 0x0a", b"\x0a"),
        ("empty-input", "no tag octet at all", b""),
        ("trailing-octet", "one value followed by a trailing octet", unit + b"\x00"),
        ("nat-empty-magnitude", "zero-length magnitude; zero is one zero octet", b"\x03" + _frame(b"")),
        (
            "nat-leading-zero",
            "overlong magnitude with a leading zero octet",
            b"\x03" + _frame(b"\x00\x01"),
        ),
        ("nat-truncated-magnitude", "magnitude frame longer than the input", b"\x03" + _u64(2) + b"\x01"),
        ("int-negative-zero", "negative zero", b"\x04\x01" + _frame(b"\x00")),
        ("int-sign-two", "sign octet other than 0 or 1", b"\x04\x02" + _frame(b"\x01")),
        ("int-missing-sign", "signed integer with no sign octet", b"\x04"),
        ("symbol-empty", "empty symbol", b"\x06" + _frame(b"")),
        ("symbol-space", "symbol octet 0x20 below the printable range", b"\x06" + _frame(b"a b")),
        ("symbol-del", "symbol octet 0x7f above the printable range", b"\x06" + _frame(b"a\x7f")),
        ("symbol-high-bit", "symbol octet 0xc3 outside ASCII", b"\x06" + _frame("é".encode())),
        ("bytes-length-short", "bytes frame declares more octets than follow", b"\x05" + _u64(3) + b"ab"),
        ("seq-count-short", "sequence declares two children but carries one", b"\x07" + _u64(2) + _frame(unit)),
        ("seq-child-trailing", "child frame carries a trailing octet", b"\x07" + _u64(1) + _frame(unit + b"\x00")),
        ("seq-child-frame-short", "child frame longer than the remaining input", b"\x07" + _u64(1) + _u64(2) + unit),
        (
            "record-duplicate-ordinal",
            "two fields with ordinal 0",
            b"\x08" + _u64(2) + _u64(0) + _frame(unit) + _u64(0) + _frame(unit),
        ),
        (
            "record-unsorted-ordinals",
            "field ordinal 1 before ordinal 0",
            b"\x08" + _u64(2) + _u64(1) + _frame(unit) + _u64(0) + _frame(unit),
        ),
        ("record-count-short", "record declares one field but carries none", b"\x08" + _u64(1)),
        ("variant-payload-trailing", "variant payload frame carries a trailing octet", b"\x09" + _u64(0) + _frame(nat_one + b"\x00")),
        ("variant-missing-payload", "variant with a case but no payload frame", b"\x09" + _u64(0)),
        ("variant-payload-unknown-tag", "variant payload with an unknown tag", b"\x09" + _u64(0) + _frame(b"\xff")),
    ]
    rows: list[dict[str, Any]] = []
    for name, reason, octets in crafted:
        try:
            k1.decode_datum(octets)
        except k1.CanonicalError as error:
            python_detail = str(error)
        else:
            raise ExportError(f"K1 reference decoder accepts crafted {name}")
        rows.append(
            {
                "name": f"crafted/{name}",
                "source": "crafted",
                "reason": reason,
                "hex": octets.hex(),
                "python_detail": python_detail,
            }
        )
    return rows


# --- D1 carriers ----------------------------------------------------------------


def _producer_index(model: ModuleType, node_index: dict[tuple[int, ...], int], reference: object) -> int:
    return node_index[model._producer_node(reference)]


def _transfer_for(
    model: ModuleType,
    core: object,
    node: tuple[int, ...],
    node_index: dict[tuple[int, ...], int],
    positions: dict[str, dict[int, int]],
    module_outputs: dict[tuple[int, ...], object],
) -> dict[str, Any]:
    """The Section 11 transfer the D1 typed model applies to one node.

    This mirrors the class loop of ``derive_graph`` case for case; the Lean
    fold applies the lattice, and agreement on the exported class table is the
    check that this mirror and the Lean transcription together reproduce D1.
    """

    base, foundation, oracle = model.base, model.foundation, model.oracle
    tag = node[0]
    if tag in (0, 2):
        return {"kind": "constant", "class": "StaticPublic"}
    if tag == 1:
        return {"kind": "constant", "class": "VerifierPrivate"}
    if node in module_outputs:
        transfer = module_outputs[node].transfer
        if transfer is model.ModuleOutputTransfer.DETERMINISTIC:
            return {"kind": "join-incoming"}
        if transfer is model.ModuleOutputTransfer.PROVER_PUBLICATION:
            return {"kind": "publish-join-incoming"}
        return {"kind": "constant", "class": "Invalid"}
    if tag == 7:
        occurrence_ref = node[1]
        effect = core.occurrences[occurrence_ref].effect
        activity = node_index[(6, occurrence_ref)]
        if (
            type(effect) is oracle.PublishOracleEffect
            and type(core.oracles[effect.oracle].publication_mode) is oracle.LogicalAccessOracle
        ):
            return {"kind": "publish-of", "node": activity}
        if type(effect) is oracle.QueryOracleEffect:
            if effect.visibility is oracle.OracleVisibility.VERIFIER_ONLY:
                return {"kind": "constant", "class": "VerifierPrivate"}
            return {
                "kind": "join-of",
                "nodes": [activity, _producer_index(model, node_index, effect.index)],
            }
        if type(effect) is oracle.AnswerOracleEffect:
            query = core.occurrences[effect.query].effect
            if query.visibility is oracle.OracleVisibility.VERIFIER_ONLY:
                return {"kind": "constant", "class": "VerifierPrivate"}
            return {"kind": "join-incoming"}
        return {"kind": "join-incoming"}
    if tag == 8:
        occurrence_ref = node[1]
        effect = core.occurrences[occurrence_ref].effect
        activity = node_index[(6, occurrence_ref)]
        if type(effect) is base.ProverMessageEffect:
            return {"kind": "publish-of", "node": activity}
        if type(effect) is foundation.VerifierMessageEffect:
            return {
                "kind": "join-of",
                "nodes": [activity]
                + [_producer_index(model, node_index, item) for item in effect.inputs],
            }
        if type(effect) is base.ChallengeEffect:
            challenge = core.challenges[effect.challenge]
            priors = (
                [
                    node_index[(8, positions["challenge"][item], 0)]
                    for item in challenge.correlation.prior_members
                ]
                if type(challenge.correlation) is base.JointCorrelation
                else []
            )
            return {
                "kind": "challenge",
                "challenge_ref": effect.challenge,
                "activity": activity,
                "conditions": [
                    _producer_index(model, node_index, item)
                    for item in challenge.public_conditions
                ],
                "priors": priors,
            }
        if type(effect) is oracle.PublishOracleEffect:
            return {"kind": "publish-of", "node": activity}
        if type(effect) is oracle.AnswerOracleEffect:
            query = core.occurrences[effect.query].effect
            if query.visibility is oracle.OracleVisibility.VERIFIER_ONLY:
                return {"kind": "constant", "class": "VerifierPrivate"}
            return {"kind": "publish-of", "node": activity}
        return {"kind": "join-incoming"}
    return {"kind": "join-incoming"}


def _module_output_specs(model: ModuleType, core: object, scenario: str) -> dict[tuple[int, ...], object]:
    """The module output specifications keyed by their ``ModuleOutputNode``."""

    private_sink = scenario == "invalid-module-control-sink"
    semantics = model._module_occurrence_semantics(core, private_sink)
    specs: dict[tuple[int, ...], object] = {}
    for occurrence_ref, occurrence_semantics in semantics.items():
        for output_ordinal, output in enumerate(occurrence_semantics.outputs):
            specs[(13, occurrence_ref, output_ordinal)] = output
    return specs


def d1_carriers(model: ModuleType, k1: ModuleType) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    bodies: list[dict[str, Any]] = []
    tables: list[dict[str, Any]] = []
    for name, fixture in model.fixtures().items():
        admitted = model.admit_core(fixture.candidate, fixture.environment)
        _require(admitted.outcome == "Affirmative", f"D1 no longer admits {name}")
        handle = admitted.handle
        core_body = fixture.candidate.profiled_body
        public_coin_body = model.public_coin_body(handle)
        for kind, body in (("core-body", core_body), ("public-coin-body", public_coin_body)):
            decoded = k1.decode_datum(body)
            _require(k1.encode_datum(decoded) == body, f"{name} {kind} does not round-trip in K1")
            bodies.append(
                {
                    "name": f"d1/{name}/{kind}",
                    "source": f"d1-{kind}",
                    "carrier": name,
                    "length": len(body),
                    "sha256": hashlib.sha256(body).hexdigest(),
                }
            )
        core, scenario = model._retained_core(handle)
        _require(scenario == name, f"D1 scenario recognition drifted for {name}")
        _graph, evidence = model.derive_graph(core, scenario)
        node_index = {node: index for index, node in enumerate(evidence.nodes)}
        positions = model._positions(core)
        module_outputs = _module_output_specs(model, core, scenario)
        transfers = [
            _transfer_for(model, core, node, node_index, positions, module_outputs)
            for node in evidence.nodes
        ]
        tables.append(
            {
                "carrier": name,
                "nodes": [
                    {"tag": node[0], "args": list(node[1:]), "key": model._pc_key(node).hex()}
                    for node in evidence.nodes
                ],
                "edges": [[node_index[source], node_index[target]] for source, target in evidence.edges],
                "transfers": transfers,
                "expected_order": [node_index[node] for node in evidence.topological],
                "expected_classes": [CLASS_NAMES[evidence.classes[node]] for node in evidence.nodes],
                "eligible": evidence.eligible,
            }
        )
    return bodies, tables


def regenerate_bodies(model: ModuleType, k1: ModuleType) -> dict[str, dict[str, Any]]:
    """The ten D1 bodies as encode vectors (hex plus transport), keyed by name."""

    rows: dict[str, dict[str, Any]] = {}
    for name, fixture in model.fixtures().items():
        admitted = model.admit_core(fixture.candidate, fixture.environment)
        _require(admitted.outcome == "Affirmative", f"D1 no longer admits {name}")
        for kind, body in (
            ("core-body", fixture.candidate.profiled_body),
            ("public-coin-body", model.public_coin_body(admitted.handle)),
        ):
            vector_name = f"d1/{name}/{kind}"
            rows[vector_name] = {
                "name": vector_name,
                "source": f"d1-{kind}",
                "value": transport_of_datum(k1, k1.decode_datum(body)),
                "hex": body.hex(),
                "sha256": hashlib.sha256(body).hexdigest(),
            }
    return rows


# --- export ---------------------------------------------------------------------


def export() -> dict[str, Any]:
    k1 = _load("_zkc_m0_k1", K1_MODEL)
    model = _load("_zkc_m0_d1_model", D1_MODEL)
    oracle = k1_oracle_vectors(k1)
    negatives = structural_negatives(k1)
    bodies, _ = d1_carriers(model, k1)
    d1_export = _load("_zkc_d1_m1_export", D1_M1_EXPORT)
    construction = d1_export.export()
    return {
        "k1-encoding-vectors.json": {
            "source": "evaluation/k1-executable-foundations/oracle/cases",
            "encode": oracle["encode"],
            "reject": oracle["reject"],
            "skipped": oracle["skipped"],
            "natural_byte_bound": oracle["boundary"],
        },
        "structural-negatives.json": {
            "source": "docs-next/foundation/executable-foundations.md Section 2.1 malformation list",
            "reject": negatives,
        },
        "body-digests.json": {
            "source": "evaluation/formal-source-integrated-graph-f0v2b2d1",
            "note": "Regenerated at check time from the D1 typed model and compared with these digests before use.",
            "bodies": bodies,
        },
        "pcgraph-construction.json": construction,
    }


def _scalar(value: Any) -> bool:
    return value is None or isinstance(value, (bool, int, float, str))


def _render(value: Any, indent: int) -> str:
    """Deterministic JSON with scalar lists inline and everything else nested.

    ``json.dumps(indent=...)`` puts every list element on its own line, which
    turns an edge table into thousands of lines; this keeps lists of scalars on
    one line so the committed tables stay reviewable.
    """

    pad = " " * indent
    inner = " " * (indent + 1)
    if isinstance(value, dict):
        if not value:
            return "{}"
        items = [
            f"{inner}{json.dumps(key)}: {_render(value[key], indent + 1)}"
            for key in sorted(value)
        ]
        return "{\n" + ",\n".join(items) + "\n" + pad + "}"
    if isinstance(value, list):
        if not value:
            return "[]"
        if all(_scalar(item) for item in value):
            return json.dumps(value, separators=(", ", ": "))
        items = [f"{inner}{_render(item, indent + 1)}" for item in value]
        return "[\n" + ",\n".join(items) + "\n" + pad + "]"
    return json.dumps(value)


def _dump(value: Any) -> str:
    text = _render(value, 0) + "\n"
    if json.loads(text) != value:  # pragma: no cover - renderer defect guard
        raise ExportError("vector renderer is not faithful")
    return text


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=VECTORS, help="output directory")
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the regenerated export with the committed files instead of writing",
    )
    args = parser.parse_args()
    files = export()
    if args.check:
        drift = [
            name
            for name, value in files.items()
            if not (VECTORS / name).is_file()
            or (VECTORS / name).read_text(encoding="utf-8") != _dump(value)
        ]
        if drift:
            print("vector drift: " + ", ".join(drift))
            return 1
        print(f"{len(files)} vector files match the committed export")
        return 0
    args.out.mkdir(parents=True, exist_ok=True)
    for name, value in files.items():
        (args.out / name).write_text(_dump(value), encoding="utf-8")
        print(f"wrote {args.out / name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
