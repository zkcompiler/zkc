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


def require(condition, label):
    if not condition:
        raise AssertionError("reader " + label)


def main():
    descriptor = variant.descriptor("example.Opening", [("opening", ["field:koala-bear", "field:koala-bear"])])
    spelling = '!data.sequence<!data.variant<"' + descriptor + '">>'
    term, kind = render.sort(spelling)
    require(kind[0] == "data" and '.sequence (.product "\\\"example.Opening\\\"" "opening"' in term,
            "lost the nominal sequence")
    other = variant.descriptor("other.Opening", [("opening", ["field:koala-bear", "field:koala-bear"])])
    require(render.sort('!data.sequence<!data.variant<"' + other + '">>') != (term, kind),
            "merged distinct nominal identities")
    # Canonical node tables have no unreachable or duplicate nodes.
    value = json.loads(bytes.fromhex(descriptor[8:]))
    value[1].append("unused")
    noncanonical = "variant:" + json.dumps(value, separators=(",", ":")).encode().hex()
    refused("noncanonical product", lambda: render.sort('!data.variant<"' + noncanonical + '">'))
    service = variant.descriptor("example.Private", [("private", ["service:random.koala-bear/0"])])
    refused("nested service", lambda: render.sort('!data.sequence<!data.variant<"' + service + '">>'))
    sum_type = variant.descriptor("example.Sum", [("left", []), ("right", [])])
    refused("multiple constructors", lambda: render.sort('!data.variant<"' + sum_type + '">'))
    refused("retired variant namespace", lambda: render.sort('!local.variant<"' + descriptor + '">'))
    refused("trailing type suffix", lambda: render.sort(spelling + "garbage"))
    refused("unsupported capability", lambda: render.sort('!data.sequence<!runtime.capability<"private">>'))
    plain = ["zkc.native-proof-policy/0", "entry", "P", "V", "0", "", [], ["0"], [], "zkc.framed/0", ""]
    render.policy(plain)
    forged = list(plain)
    forged[6] = ["1"]
    refused("plain replacement service", lambda: render.policy(forged))
    forged = list(plain)
    forged[8] = [["query", "delivery"]]
    refused("plain draw schedule", lambda: render.policy(forged))
    fake = [render.FORMAT, "sha256:" + "0" * 64, "sha256:" + "1" * 64, plain, "V",
            ['!runtime.capability<"transcript:invented">'], ["i1"], [], [], []]
    refused("plain transcript ABI", lambda: render.render_declaration(fake, "ForgedPlain"))
    print("plain construction reader: 3 positive, 9 refusal controls passed")


if __name__ == "__main__":
    main()
