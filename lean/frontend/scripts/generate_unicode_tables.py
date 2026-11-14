#!/usr/bin/env python3
"""Write or check `Zkc/Frontend/Syntax/UnicodeData.lean`: the Unicode tables that the lexer needs.

The lexer needs the properties XID_Start and XID_Continue (LX6) and enough of the Unicode
normalization data to decide whether a text is in Normalization Form C (LX1): the canonical
combining classes, the characters that never occur in NFC, the canonical decompositions and the
primary compositions. All are derived from the repository's pinned Unicode data in
`common/unicode`, whose files are checked against the hashes of its manifest; the host's Unicode
database is never used. NormalizationTest.txt gives the NFC of every character that some
normalization form changes, so a character is outside NFC exactly when that column differs from
it, and a pair decomposition is a primary composition exactly when its composite is in NFC.

Lake does not run generators, so the output is kept in the repository and `--check`, which the
Lean lane runs, refuses a table that differs from what this script writes.

Usage: generate_unicode_tables.py [--check]
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

PACKAGE = Path(__file__).resolve().parents[1]
UNICODE = PACKAGE.parents[1] / "common/unicode"
TARGET = PACKAGE / "Zkc/Frontend/Syntax/UnicodeData.lean"
LIMIT = 0x110000
SURROGATES = range(0xD800, 0xE000)
HANGUL_FIRST, HANGUL_LAST = 0xAC00, 0xD7A3
FILES = ("DerivedCoreProperties.txt", "UnicodeData.txt", "NormalizationTest.txt")


def pinned():
    """The version and the text of each needed file, after checking its manifest hash."""
    manifest = json.loads((UNICODE / "manifest.json").read_text())
    version = manifest["unicode_version"]
    hashes = {entry["file"]: entry["sha256"] for entry in manifest["files"]}
    texts = {}
    for name in FILES:
        data = (UNICODE / version / name).read_bytes()
        if hashlib.sha256(data).hexdigest() != hashes.get(name):
            raise SystemExit(f"{name} does not match the hash of common/unicode/manifest.json")
        texts[name] = data.decode("utf-8")
    return version, texts


def records(text):
    for line in text.splitlines():
        line = line.split("#", 1)[0].strip()
        if line and not line.startswith("@"):
            yield [field.strip() for field in line.split(";")]


def interval(text):
    first, _, last = text.partition("..")
    return int(first, 16), int(last or first, 16)


def property_sets(text, names):
    result = {name: set() for name in names}
    for row in records(text):
        if row[1] in result:
            first, last = interval(row[0])
            result[row[1]].update(range(first, last + 1))
    return result


def character_data(text):
    """Canonical combining classes and canonical decompositions of UnicodeData.txt."""
    combining, decomposition = {}, {}
    for row in records(text):
        code = int(row[0], 16)
        if int(row[3]):
            # Ranges given as `First`/`Last` rows have class 0 and no decomposition.
            combining[code] = int(row[3])
        if row[5] and not row[5].startswith("<"):
            decomposition[code] = [int(part, 16) for part in row[5].split()]
    return combining, decomposition


def nfc_of_changed(text):
    """Part 1 of NormalizationTest.txt: the NFC of each character that some form changes."""
    part, result = None, {}
    for line in text.splitlines():
        if line.startswith("@Part"):
            part = line.split()[0]
            continue
        line = line.split("#", 1)[0].strip()
        if part == "@Part1" and line:
            source, nfc = line.split(";")[:2]
            result[int(source, 16)] = [int(part, 16) for part in nfc.split()]
    return result


def scalar_values():
    for code in range(LIMIT):
        if code not in SURROGATES:
            yield code


def ranges(members):
    out, start, last = [], None, None
    for code in scalar_values():
        if code in members:
            if start is None:
                start = code
            last = code
        elif start is not None:
            out.append((start, last))
            start = None
    if start is not None:
        out.append((start, last))
    return out


def render_ranges(items):
    return " ".join(f"{a:X}" if a == b else f"{a:X}-{b:X}" for a, b in items)


def generate():
    version, texts = pinned()
    properties = property_sets(texts["DerivedCoreProperties.txt"], ("XID_Start", "XID_Continue"))
    classes, decomposition = character_data(texts["UnicodeData.txt"])
    nfc = nfc_of_changed(texts["NormalizationTest.txt"])

    def full_decomposition(code):
        if code not in decomposition:
            return [code]
        return [part for item in decomposition[code] for part in full_decomposition(item)]

    # `_` is a start character only by the rule LX6 itself.
    xid_start = ranges(properties["XID_Start"] - {0x5F})
    xid_continue = ranges(properties["XID_Continue"])
    combining = []
    for code in scalar_values():
        value = classes.get(code, 0)
        if value:
            if combining and combining[-1][1] == code - 1 and combining[-1][2] == value:
                combining[-1][1] = code
            else:
                combining.append([code, code, value])
    outside = {code for code, form in nfc.items() if form != [code]}
    not_nfc = ranges(outside)
    decompositions, compositions = [], []
    for code in scalar_values():
        if HANGUL_FIRST <= code <= HANGUL_LAST or code not in decomposition:
            continue
        decompositions.append((code, full_decomposition(code)))
        parts = decomposition[code]
        if len(parts) == 2 and code not in outside:
            compositions.append((parts[0], parts[1], code))

    lines = [
        "module",
        "",
        "@[expose] public section",
        "",
        "set_option autoImplicit false",
        "",
        "/-!",
        "# Unicode tables",
        "",
        "Generated by `scripts/generate_unicode_tables.py` from the Unicode "
        f"{version} data pinned in",
        "`common/unicode`. Do not edit by hand.",
        "Code points are hexadecimal; `A-B` is a range.",
        "-/",
        "",
        "namespace Zkc.Frontend.Syntax.UnicodeData",
        "",
        f'def unicodeVersion : String := "{version}"',
        "",
        "/-- XID_Start, without `_`. -/",
        f'def xidStart : String := "{render_ranges(xid_start)}"',
        "",
        "/-- XID_Continue. -/",
        f'def xidContinue : String := "{render_ranges(xid_continue)}"',
        "",
        "/-- Canonical combining classes other than 0, as `A-B:class`. -/",
        'def combiningClasses : String := "'
        + " ".join(f"{a:X}-{b:X}:{v}" for a, b, v in combining)
        + '"',
        "",
        "/-- The characters that never occur in a text in Normalization Form C. -/",
        f'def notInNfc : String := "{render_ranges(not_nfc)}"',
        "",
        "/-- Full canonical decompositions, Hangul syllables excepted: `C>D1.D2…`. -/",
        'def decompositions : String := "'
        + " ".join(f"{c:X}>" + ".".join(f"{d:X}" for d in parts) for c, parts in decompositions)
        + '"',
        "",
        "/-- Primary compositions, Hangul syllables excepted: `A.B>C`. -/",
        'def compositions : String := "'
        + " ".join(f"{a:X}.{b:X}>{c:X}" for a, b, c in compositions)
        + '"',
        "",
        "end Zkc.Frontend.Syntax.UnicodeData",
        "",
    ]
    summary = (f"{len(xid_start)} start ranges, {len(xid_continue)} continue ranges, "
               f"{len(combining)} class ranges, {len(not_nfc)} excluded ranges, "
               f"{len(decompositions)} decompositions, {len(compositions)} compositions")
    return "\n".join(lines), summary


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--check", action="store_true", help="refuse a stale table instead of writing it")
    args = parser.parse_args()
    text, summary = generate()
    relative = TARGET.relative_to(PACKAGE.parents[1])
    if args.check:
        if not TARGET.is_file() or TARGET.read_text(encoding="utf-8") != text:
            sys.exit(f"{relative} is stale; run lean/frontend/scripts/generate_unicode_tables.py")
        print(f"{relative} is current: {summary}")
        return
    TARGET.write_text(text, encoding="utf-8")
    print(f"wrote {relative}: {summary}")


if __name__ == "__main__":
    main()
