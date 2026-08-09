#!/usr/bin/env python3
"""Closed-schema check for the synthetic Ext4 transcript schedule."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


vector_mode = len(sys.argv) == 3 and sys.argv[1] == "--vector"
require(len(sys.argv) == (3 if vector_mode else 2), "invalid invocation")
schedule_path = Path(sys.argv[2] if vector_mode else sys.argv[1])
document = json.loads(schedule_path.read_text(encoding="utf-8"))
require(
    set(document)
    == {
        "artifact_id",
        "endpoint_kind",
        "events",
        "limits",
        "schema",
        "source",
        "sponge",
    },
    "unexpected top-level schedule fields",
)
require(document["schema"] == "zkc.oir.transcript_schedule", "wrong schema")
require(document["endpoint_kind"] == "verifier", "wrong endpoint")
require(
    re.fullmatch(r"[0-9a-f]{64}", document["artifact_id"]) is not None,
    "artifact identity is not canonical",
)
require(
    re.fullmatch(r"sha256:[0-9a-f]{64}", document["source"]) is not None,
    "source citation is not canonical",
)
if vector_mode:
    require(
        document["sponge"]
        == {"construction": "toy_duplex", "iv": "artifact-id"},
        "wrong construction route",
    )
    require(
        document["events"]
        == [
            {
                "codec": "ts_be8",
                "index": 0,
                "kind": "absorb",
                "payload_class": "rs",
                "source_positions": [0],
            },
            {
                "codec": "ts_be8",
                "count": "2",
                "domain": "fri.query",
                "index": 1,
                "kind": "squeeze",
                "label": "query",
                "payload_class": "query_index",
                "rule": "uniform_independent",
                "source_positions": [1],
                "space": "1024",
            },
        ],
        "counted vector event schedule differs",
    )
else:
    require(
        document["sponge"]
        == {
            "construction": "plonky3_bb31_poseidon2_w16_r8_lenpad",
            "iv": "artifact-id",
        },
        "wrong construction route",
    )
    codec = "plonky3_bb31_ext4_tuple"
    require(
        document["events"]
        == [
            {
                "codec": codec,
                "index": 0,
                "kind": "absorb",
                "payload_class": "tg",
                "source_positions": [0],
            },
            {
                "codec": codec,
                "index": 1,
                "kind": "absorb",
                "payload_class": "tg",
                "source_positions": [1],
            },
            {
                "codec": codec,
                "count": "1",
                "domain": "fixture.ext4.challenge",
                "index": 2,
                "kind": "squeeze",
                "label": "challenge",
                "payload_class": "scalar",
                "rule": "uniform",
                "source_positions": [2],
                "space": "16428751811598850197311699254593454081",
            },
            {
                "codec": codec,
                "index": 3,
                "kind": "absorb",
                "payload_class": "scalar",
                "source_positions": [3],
            },
        ],
        "typed event schedule differs",
    )
require(
    document["limits"]
    == {
        "challenge_codec_selection": "per_event_payload_class",
        "challenge_values": "not_computed",
        "construction_execution": "not_performed",
        "domain_evidence": "declaration_only",
        "protocol_correspondence": "not_evaluated",
        "squeeze_projection": "counted_scalar_or_vector",
    },
    "schedule limitations differ",
)
if vector_mode:
    print("counted vector transcript schedule matched")
else:
    print("synthetic Ext4 transcript schedule matched")
