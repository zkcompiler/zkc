#!/usr/bin/env python3
"""Validate the pinned source-name profile and generate private C++ tables.

Uses only the Python standard library, never the host Unicode database.
--json exposes the decoded range sets for independent implementation checks.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def codepoint(text):
    require(re.fullmatch(r"[0-9A-F]{4,6}", text), f"invalid code point: {text}")
    value = int(text, 16)
    require(value <= 0x10FFFF, f"out-of-range code point: {text}")
    return value


def interval(text):
    parts = text.split("..")
    require(len(parts) in (1, 2), f"invalid interval: {text}")
    first, last = codepoint(parts[0]), codepoint(parts[-1])
    require(first <= last, f"reversed interval: {text}")
    return first, last


def records(text):
    for line in text.splitlines():
        line = line.split("#", 1)[0].strip()
        if line and not line.startswith("@"):
            yield [field.strip() for field in line.split(";")]


def properties(text):
    result = {}
    for row in records(text):
        require(len(row) in (2, 3), "malformed property row")
        key = ";".join(row[1:])
        require(all(re.fullmatch(r"[A-Za-z_]+", p) for p in row[1:]),
                "invalid property name")
        first, last = interval(row[0])
        values = result.setdefault(key, set())
        addition = set(range(first, last + 1))
        require(values.isdisjoint(addition), f"overlapping {key} intervals")
        values.update(addition)
    return result


def categories(text):
    result = {}
    previous = -1
    pending = None
    for row in records(text):
        require(len(row) == 15, "malformed UnicodeData row")
        value = codepoint(row[0])
        require(value > previous, "overlapping or unordered UnicodeData rows")
        previous = value
        require(re.fullmatch(r"[A-Z][a-z]", row[2]), "invalid general category")
        if row[1].endswith(", First>"):
            require(pending is None, "nested UnicodeData range")
            pending = row
            continue
        if pending is not None:
            require(row[1] == pending[1].replace(", First>", ", Last>")
                    and row[2:] == pending[2:], "unmatched UnicodeData range")
            first = codepoint(pending[0])
            pending = None
        else:
            require(not row[1].endswith(", Last>"), "orphan UnicodeData range")
            first = value
        if row[2] in ("Sm", "Ps", "Pe"):
            result.setdefault(row[2], set()).update(range(first, value + 1))
    require(pending is None, "unterminated UnicodeData range")
    return result


def brackets(text):
    result = {}
    for row in records(text):
        require(len(row) == 3 and row[2] in ("o", "c"), "invalid bracket row")
        scalar, partner = codepoint(row[0]), codepoint(row[1])
        require(scalar not in result, "duplicate bracket")
        require(scalar != partner, "self-paired bracket")
        result[scalar] = (partner, row[2])
    for scalar, (partner, kind) in result.items():
        require(result.get(partner) == (scalar, "c" if kind == "o" else "o"),
                "non-reciprocal bracket pair")
    return result


def ranges(values):
    result = []
    for value in sorted(values):
        if result and result[-1][1] + 1 == value:
            result[-1][1] = value
        else:
            result.append([value, value])
    return result


def load_profile(root):
    raw_manifest = (root / "manifest.json").read_bytes()
    manifest = json.loads(raw_manifest)
    required = {
        "schema": "zkc.source-name-profile/0", "profile": "zkc.source-names/0",
        "unicode_version": "17.0.0", "normalization": "NFC",
        "identifier_start_additions": ["005F"],
        "identifier_continue_additions": ["2080..2089"],
        "identifier_exclusions": ["Default_Ignorable_Code_Point", "Bidi_Control"],
        "operator_category": "Sm", "operator_reserved": ["2211", "220F"],
        "delimiter_categories": ["Ps", "Pe"], "normalization_test_rows": 20034,
    }
    for key, expected in required.items():
        require(manifest.get(key) == expected, f"unsupported profile field: {key}")
    license_entry = manifest["license"]
    require(license_entry["file"] == "LICENSE.txt", "unexpected license path")
    require(hashlib.sha256((root / "LICENSE.txt").read_bytes()).hexdigest()
            == license_entry["sha256"], "Unicode license hash mismatch")
    data = {}
    for entry in manifest["files"]:
        name = entry["file"]
        require(name not in data and Path(name).name == name, "invalid data filename")
        content = (root / manifest["unicode_version"] / name).read_bytes()
        require(hashlib.sha256(content).hexdigest() == entry["sha256"],
                f"Unicode input hash mismatch: {name}")
        require(entry["url"] == f"https://www.unicode.org/Public/17.0.0/ucd/{name}",
                f"unexpected data provenance: {name}")
        data[name] = content.decode("utf-8")
    require(set(data) == {"DerivedCoreProperties.txt", "PropList.txt", "UnicodeData.txt",
                          "BidiBrackets.txt", "NormalizationTest.txt"},
            "unexpected Unicode data inventory")
    corpus = list(records(data["NormalizationTest.txt"]))
    require(len(corpus) == manifest["normalization_test_rows"],
            "unexpected normalization corpus size")
    for row in corpus:
        require(len(row) == 6 and row[-1] == "", "malformed normalization test")
        for column in row[:5]:
            require(column != "", "empty normalization column")
            for scalar in column.split():
                require(not 0xD800 <= codepoint(scalar) <= 0xDFFF,
                        "surrogate in normalization test")
    core = properties(data["DerivedCoreProperties.txt"])
    props = properties(data["PropList.txt"])
    excluded = core["Default_Ignorable_Code_Point"] | props["Bidi_Control"]
    start = (core["XID_Start"] | {0x5F}) - excluded
    continuation = (core["XID_Continue"] | set(range(0x2080, 0x208A))) - excluded
    require(start <= continuation, "identifier start is not a continuation")
    for values in (start, continuation):
        require(all(not 0xD800 <= value <= 0xDFFF for value in values),
                "surrogate identifier member")
    cats = categories(data["UnicodeData.txt"])
    forbidden = continuation | excluded | set(range(128))
    symbols = cats["Sm"] - forbidden
    pairs = []
    for opener, (closer, kind) in sorted(brackets(data["BidiBrackets.txt"]).items()):
        if (kind == "o" and opener in cats["Ps"] and closer in cats["Pe"]
                and opener not in forbidden and closer not in forbidden):
            pairs.append([opener, closer])
    # NFC is checked by the mature normalizers at API admission, including for
    # single-scalar symbols and both endpoints of each candidate bracket pair.
    identity = manifest["profile"] + ":" + hashlib.sha256(raw_manifest).hexdigest()
    return {"identity": identity, "identifier_start": ranges(start),
            "identifier_continue": ranges(continuation),
            "mathematical_symbols": ranges(symbols), "delimiter_pairs": pairs}


def cpp(profile):
    result = ["// Generated from hash-verified Unicode data; do not edit.",
              f'constexpr char sourceProfileIdentity[] = "{profile["identity"]}";']
    for key, name in (("identifier_start", "identifierStart"),
                      ("identifier_continue", "identifierContinue"),
                      ("mathematical_symbols", "mathematicalSymbols"),
                      ("delimiter_pairs", "sourceDelimiters")):
        kind = "Delimiter" if key == "delimiter_pairs" else "Range"
        result.append(f"constexpr {kind} {name}[] = {{")
        result.extend(f"  {{0x{first:x}, 0x{last:x}}}," for first, last in profile[key])
        result.append("};")
    return "\n".join(result) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    profile = load_profile(args.data)
    content = json.dumps(profile, sort_keys=True, indent=2) + "\n" if args.json else cpp(profile)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
