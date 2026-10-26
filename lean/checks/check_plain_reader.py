#!/usr/bin/env python3
"""Strict-reader controls for recursive nominal construction data and profiles."""
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
from bridges.common.lean_render import Refused  # noqa: E402
from bridges.construction import render  # noqa: E402

spec = importlib.util.spec_from_file_location("fixture_variant", ROOT / "common/tests/support/variant_codec.py")
variant = importlib.util.module_from_spec(spec)
spec.loader.exec_module(variant)


def refused(label, action):
    try:
        action()
    except (Refused, ValueError):
        return
    raise AssertionError("reader accepted " + label)


def main():
    descriptor = variant.descriptor("example.Opening", [("opening", ["field:koala-bear", "field:koala-bear"])])
    spelling = '!data.sequence<!local.variant<"' + descriptor + '">>'
    term, kind = render.sort(spelling)
    assert kind[0] == "data" and '.sequence (.product "\\\"example.Opening\\\"" "opening"' in term
    other = variant.descriptor("other.Opening", [("opening", ["field:koala-bear", "field:koala-bear"])])
    assert render.sort('!data.sequence<!local.variant<"' + other + '">>') != (term, kind)
    # Canonical node tables have no unreachable or duplicate nodes.
    value = json.loads(bytes.fromhex(descriptor[8:]))
    value[1].append("unused")
    noncanonical = "variant:" + json.dumps(value, separators=(",", ":")).encode().hex()
    refused("noncanonical product", lambda: render.sort('!local.variant<"' + noncanonical + '">'))
    service = variant.descriptor("example.Private", [("private", ["service:random.koala-bear/0"])])
    refused("nested service", lambda: render.sort('!data.sequence<!local.variant<"' + service + '">>'))
    sum_type = variant.descriptor("example.Sum", [("left", []), ("right", [])])
    refused("multiple constructors", lambda: render.sort('!local.variant<"' + sum_type + '">'))
    refused("trailing type suffix", lambda: render.sort(spelling + "garbage"))
    refused("unsupported capability", lambda: render.sort('!data.sequence<!local.capability<"private">>'))
    plain = ["zkc.native-proof-policy/0", "entry", "P", "V", "0", "", [], ["0"], [], "zkc.framed/0", ""]
    render.policy(plain)
    forged = list(plain)
    forged[6] = ["1"]
    refused("plain replacement service", lambda: render.policy(forged))
    forged = list(plain)
    forged[8] = [["query", "delivery"]]
    refused("plain draw schedule", lambda: render.policy(forged))
    fake = [render.FORMAT, "sha256:" + "0" * 64, "sha256:" + "1" * 64, plain, "V",
            ['!local.capability<"transcript:invented">'], ["i1"], [], [], []]
    refused("plain transcript ABI", lambda: render.render_declaration(fake, "ForgedPlain"))
    print("plain construction reader: 3 positive, 8 refusal controls passed")


if __name__ == "__main__":
    main()
