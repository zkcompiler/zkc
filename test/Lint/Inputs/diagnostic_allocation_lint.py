#!/usr/bin/env python3
"""Diagnostic-id allocation lint.

registry/diagnostic-allocation.json declares every diagnostic-id range with its
component, source allowlist, and live/reserved ids; docs/spec/versioning.md §3
defines the stability rule. This script holds the registry and source tree to
each other, fail-closed:

  1. every id emitted by source is declared `live`, and the emitting
     file sits under one of its range's declared source prefixes;
  2. every `live` id is emitted by source — a table entry nothing
     emits is table drift, not documentation;
  3. every `live` id appears in an expected diagnostic or test assertion under
     test/ (the negative-test conformance rule, carrier.md §5), unless the
     block carries an explicit coverage exemption with a reason;
  4. `reserved` ids (allocated, unshipped) are emitted nowhere;
  5. an emitted id outside every declared range fails.

Emission sites are recognized by the patterns the tree actually uses:
`[zkc-Eddd]` literals, TerminalClosure's `error(..., "zkc-Eddd")`,
`refuse("Eddd"` (the certificate checker prepends `zkc-` at format
time), ReductionClosure's `instanceError("zkc-Eddd")` helper, and the
reference oracle's `("Eddd",` tuples and
`"Eddd: ..."` messages. Prose mentions (`zkc-Eddd` without an
emitting call, in comments or ODS descriptions) are not emissions.

Exit 0 on agreement; 1 on any violation; 2 when the allocation itself
cannot be established (missing or malformed file) — parse
failure is a failure, never a skip.
"""

import json
import re
import sys
from pathlib import Path
from typing import NoReturn

ROOT = Path(__file__).resolve().parents[3]
ALLOCATION = ROOT / "registry" / "diagnostic-allocation.json"
SCHEMA = "zkc.diagnostic_allocation"

SOURCE_DIRS = ("include", "lib", "reference", "tools")
SOURCE_SUFFIXES = {".cpp", ".h", ".td", ".py"}
TEST_DIR = ROOT / "test"
# The lint's own directory must not satisfy the coverage rule: an id
# named only here is not exercised by a negative test.
TEST_EXCLUDE = TEST_DIR / "Lint"

EMISSION = re.compile(
    r"\[zkc-(E\d{3})\]"  # C++ diagnostic literals
    r"|error\([^\n]*\"zkc-(E\d{3})\""  # TerminalClosure matcher
    r"|Error\(\"zkc-(E\d{3})\""  # ReductionClosure's instanceError helper
    r"|refuse\(\"(E\d{3})\""  # checker ids, zkc- prefixed at format time
    r"|\(\"(E\d{3})\""  # oracle (code, subject) tuples
    r"|f?\"(E\d{3}):"  # oracle message-prefixed raises
)
ID_FORM = re.compile(r"^E(\d{3})$")
RANGE_FORM = re.compile(r"^E(\d{3})-E(\d{3})$")
TEST_ASSERTION = re.compile(
    r"(?:expected-(?:error|warning|remark)"
    # A custom FileCheck prefix, but never one of lit's own directives:
    # naming an id in a RUN line is running a command, not asserting a
    # refusal, and counting it as one lets the real assertion be
    # deleted while this stays green.
    r"|(?:^|\s)(?:CHECK(?:-[A-Z0-9_-]+)?"
    r"|(?!RUN:|REQUIRES:|UNSUPPORTED:|XFAIL:|DEFINE:|REDEFINE:)"
    r"[A-Z][A-Z0-9_-]*):"
    r"|EXPECT_[A-Z_]+|assert\b)"
    r".*?(?<![A-Za-z0-9])E(\d{3})(?!\d)"
)


def die(message) -> NoReturn:
    print("diagnostic-allocation lint: %s" % message, file=sys.stderr)
    sys.exit(2)


def load_table():
    if not ALLOCATION.is_file():
        die("%s does not exist" % ALLOCATION)
    try:
        table = json.loads(ALLOCATION.read_text(encoding="utf-8"))
    except json.JSONDecodeError as err:
        die("%s does not parse: %s" % (ALLOCATION, err))
    if not isinstance(table, dict) or table.get("schema") != SCHEMA:
        die("%s is not a %s document" % (ALLOCATION, SCHEMA))
    return table


def parse_ids(entry, key, lo, hi, seen):
    ids = entry.get(key)
    if not isinstance(ids, list):
        die("range %s: %r is not a list" % (entry.get("range"), key))
    out = []
    for ident in ids:
        m = ID_FORM.match(ident) if isinstance(ident, str) else None
        if not m:
            die("range %s: malformed id %r" % (entry["range"], ident))
        n = int(m.group(1))
        if not lo <= n <= hi:
            die("id %s lies outside its declared range %s"
                % (ident, entry["range"]))
        if ident in seen:
            die("id %s is declared twice" % ident)
        seen.add(ident)
        out.append(ident)
    return out


def validate(table):
    """Return (live -> sources, reserved, coverage_exempt, twin-mirrored)."""
    ranges = table.get("ranges")
    if not isinstance(ranges, list) or not ranges:
        die("the allocation table declares no ranges")
    covered = {}  # numeric id -> range string, for overlap detection
    live = {}
    reserved = set()
    mirrored = set()
    seen = set()
    for entry in ranges:
        if not isinstance(entry, dict):
            die("a range entry is not an object")
        m = RANGE_FORM.match(entry.get("range", ""))
        if not m:
            die("malformed range %r" % entry.get("range"))
        lo, hi = int(m.group(1)), int(m.group(2))
        if lo > hi:
            die("range %s is inverted" % entry["range"])
        if not isinstance(entry.get("component"), str) or not entry["component"]:
            die("range %s has no component" % entry["range"])
        sources = entry.get("sources")
        if not isinstance(sources, list) or not all(
                isinstance(s, str) for s in sources):
            die("range %s: sources is not a list of path prefixes"
                % entry["range"])
        for n in range(lo, hi + 1):
            if n in covered:
                die("ranges %s and %s overlap at E%03d"
                    % (covered[n], entry["range"], n))
            covered[n] = entry["range"]
        range_live = parse_ids(entry, "live", lo, hi, seen)
        for ident in range_live:
            live[ident] = tuple(sources)
        reserved.update(parse_ids(entry, "reserved", lo, hi, seen))
        # The twin facet is the declared parity surface: exactly which of a
        # range's live ids the reference twin also spells. Both drift
        # directions are checked in main() against reference/oracle/.
        twin = entry.get("twin")
        if not isinstance(twin, dict):
            die("range %s has no twin facet" % entry["range"])
        twin_ids = twin.get("mirrored")
        if not isinstance(twin_ids, list) or not all(
                isinstance(i, str) for i in twin_ids):
            die("range %s: twin.mirrored is not a list of ids"
                % entry["range"])
        for ident in twin_ids:
            if ident not in range_live:
                die("range %s: twin-mirrored %s is not one of its live ids"
                    % (entry["range"], ident))
        if set(range_live) - set(twin_ids):
            reason = twin.get("excluded_reason")
            if not isinstance(reason, str) or not reason.strip():
                die("range %s: twin facet excludes live ids without a reason"
                    % entry["range"])
        mirrored.update(twin_ids)
    exempt = table.get("coverage_exempt", {})
    if not isinstance(exempt, dict):
        die("coverage_exempt is not an object")
    for ident, reason in exempt.items():
        if ident not in live:
            die("coverage_exempt names %s, which is not a live id" % ident)
        if not isinstance(reason, str) or not reason.strip():
            die("coverage_exempt for %s carries no reason" % ident)
    return live, reserved, set(exempt), mirrored


def scan_sources():
    """Return id -> set of emitting files (paths relative to the root)."""
    emitted = {}
    for top in SOURCE_DIRS:
        base = ROOT / top
        if not base.is_dir():
            die("source directory %s is missing" % base)
        for path in sorted(base.rglob("*")):
            if not path.is_file() or path.suffix not in SOURCE_SUFFIXES:
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            for match in EMISSION.finditer(text):
                ident = next(g for g in match.groups() if g)
                rel = path.relative_to(ROOT).as_posix()
                emitted.setdefault(ident, set()).add(rel)
    return emitted


def scan_tests():
    """Return ids asserted by tests, excluding prose-only mentions."""
    asserted = set()
    for path in TEST_DIR.rglob("*"):
        if not path.is_file() or path.is_relative_to(TEST_EXCLUDE):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for line in text.splitlines():
            asserted.update("E" + m for m in TEST_ASSERTION.findall(line))
    return asserted


def main():
    live, reserved, exempt, mirrored = validate(load_table())
    emitted = scan_sources()
    asserted = scan_tests()

    problems = []
    for ident in sorted(emitted):
        files = ", ".join(sorted(emitted[ident]))
        if ident in reserved:
            problems.append(
                "%s is reserved (allocated, unshipped) but emitted by %s: "
                "ship it as live or renumber" % (ident, files))
        elif ident not in live:
            problems.append(
                "%s is emitted by %s but not declared live in %s"
                % (ident, files, ALLOCATION.relative_to(ROOT)))
        else:
            for rel in sorted(emitted[ident]):
                if not any(rel.startswith(p) for p in live[ident]):
                    problems.append(
                        "%s is emitted by %s, outside its range's declared "
                        "sources (%s)" % (ident, rel,
                                          ", ".join(live[ident]) or "none"))
    twin_emitted = {ident for ident, files in emitted.items()
                    if any(f.startswith("reference/oracle/") for f in files)}
    for ident in sorted(twin_emitted - mirrored):
        problems.append(
            "%s is emitted by the reference twin but not declared "
            "twin-mirrored: the parity surface moved without its "
            "declaration" % ident)
    for ident in sorted(mirrored - twin_emitted):
        problems.append(
            "%s is declared twin-mirrored but reference/oracle/ does not "
            "emit it: stale parity declaration" % ident)

    for ident in sorted(live):
        if ident not in emitted:
            problems.append(
                "%s is declared live but nothing under %s emits it: "
                "move it to reserved or drop it"
                % (ident, "/".join(SOURCE_DIRS)))
        elif ident not in asserted and ident not in exempt:
            problems.append(
                "%s is live but no file under test/ asserts it "
                "(negative-test conformance rule, carrier.md §5)" % ident)

    if problems:
        for problem in problems:
            print("diagnostic-allocation lint: %s" % problem, file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
