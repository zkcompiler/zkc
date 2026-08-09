#!/usr/bin/env python3
"""Re-mint the derived values a fixture corpus carries, and guard the anchors.

An identity-bearing change (a preimage field, a registry entry, a domain tag)
moves every value downstream of it: artifact ids, claim anchors, request
citations, challenge values, proof bytes, judgment digests. Those values are
*fixture-internal consistency*, not assertions — a human retyping them is a
transcription task with a transcription task's error rate.

This tool re-mints them by asking the authority rather than by guessing. Every
refusal in this repository that compares a computed value against a cited one
prints both; those messages are the derivation channel, and the table below is
the complete list of grammars the tool understands. A failure it cannot parse
is reported, never skipped — silence is how a stale corpus survives a re-mint.

Two rules make the result trustworthy:

  * **Anchors are not auto-minted.** A small enumerated set of values
    (`sentinels.json`) is the tripwire for the one failure the parity suite
    cannot see: both implementations drifting the same way. If the tool moved
    them with everything else they would stop being tripwires, so it refuses
    and reports; a human accepts the move once, deliberately.

  * **Nothing is minted from one leg.** Every anchor is recomputed through the
    native implementation and the reference twin. Disagreement is a hard
    failure that mints nothing — it means the change under way broke parity,
    which is the finding, not an obstacle to re-minting past.

Usage:
    remint.py run [--max-rounds N] [--dry-run]
    remint.py sentinels [--accept]
    remint.py status
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
# The documented preset builds into <repo>/build, which is the default. Any
# other location is named with --build-dir: a tool that assumes one build
# directory is a tool that works in exactly one checkout.
BUILD = REPO / "build"
SENTINELS = Path(__file__).resolve().parent / "sentinels.json"

# Values that are deliberately not real digests: mutation targets a test forges
# and well-known constants. Re-minting one would rewrite the negative test into
# a positive one, so they are never substituted in either direction.
FROZEN = {
    "0" * 64,
    "9" * 64,
    "1" * 64,
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",  # sha256("")
}


def frozen(value: str) -> bool:
    return value in FROZEN or len(set(value)) == 1


def same_kind(stale: str, fresh: str) -> bool:
    """Two literals may be paired only if they are the same sort of thing. A
    digest is fixed-width, so a width change means the two lines are not about
    the same value; a field element is a decimal whose digit count moves freely
    and carries no information."""
    decimal = stale.isdigit() and fresh.isdigit()
    return decimal or len(stale) == len(fresh)


# --------------------------------------------------------------------------
# Derivation channels: how each refusal names the value it computed and the
# value the corpus cited. `stale` and `fresh` are group numbers.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Channel:
    name: str
    pattern: re.Pattern[str]
    stale: int
    fresh: int


CHANNELS: tuple[Channel, ...] = (
    Channel(
        "sealed-view artifact site",
        re.compile(r"sealed ([0-9a-f]{64}), site cites ([0-9a-f]{64})"),
        stale=2, fresh=1),
    Channel(
        "sealed-view owner claim",
        re.compile(r"resolved sha256:([0-9a-f]{64}), site cites sha256:([0-9a-f]{64})"),
        stale=2, fresh=1),
    Channel(
        "binding contract anchor",
        re.compile(r"sealed sha256:([0-9a-f]{64}), binding records sha256:([0-9a-f]{64})"),
        stale=2, fresh=1),
    Channel(
        "stored identity recheck",
        re.compile(r"stored '?([0-9a-f]{64})'?, (?:re)?computed '?([0-9a-f]{64})'?"),
        stale=1, fresh=2),
    Channel(
        "material-identity constraint",
        re.compile(r'constraint does not hold: left "sha256:([0-9a-f]{64})", '
                   r'right "sha256:([0-9a-f]{64})"'),
        stale=1, fresh=2),
)

# The output-anchor refusal (zkc-E326) and the consumed-claim-vector premise
# refusal print whole structures rather than a pair, so they are parsed as
# documents: keys present on both sides whose values differ give the pairs.
STRUCTURED = (
    re.compile(r"expected (\{[^}]*\}), got (\{[^}]*\})"),
)
SUBJECT = re.compile(
    r"selected ([0-9a-f]{64} consumer [^,]*), cited ([0-9a-f]{64} consumer [^\n\"]*)")

# A FileCheck miss prints the expected line and the line it actually found.
# Only lines whose label matches are paired, and only when both carry the same
# count of long literals — a shape mismatch means the test changed, not a value.
FILECHECK = re.compile(
    r"error: [A-Z][A-Z0-9-]*(?:-NEXT|-DAG|-SAME)?: expected string not found[^\n]*\n"
    r"# \| (?://|#)? ?[A-Z][A-Z0-9-]*(?:-NEXT|-DAG|-SAME)?: ([^\n]*)\n"
    r"(?:[^\n]*\n){0,8}?# \| ([^\n]*)\n# \| \^")
# Hex first: every digit is also a hex character, so the decimal alternative
# would otherwise bite off a digest's leading run and leave a tail that pairs
# with nothing.
LITERAL = re.compile(r"[0-9a-f]{16,}|\d{8,}")

# Files whose whole content one implementation owns: regenerated, not patched.
EXEC_VECTORS = ("schnorr", "sumcheck", "chaum-pedersen", "or-sigma", "plonky3-fri")


# --------------------------------------------------------------------------
# Process helpers
# --------------------------------------------------------------------------


def purge_pycache() -> None:
    """A rewrite that keeps a file's size inside one mtime second leaves a
    stale bytecode cache behind, and the twin then answers from the old
    source. Cheap to prevent, expensive to diagnose."""
    for root in (REPO / "reference", REPO / "test"):
        for cache in root.rglob("__pycache__"):
            if ".venv" not in cache.parts:
                shutil.rmtree(cache, ignore_errors=True)


def run(command: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(command, cwd=cwd or REPO, capture_output=True, text=True)


def shell(script: str, cwd: Path | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(script, cwd=cwd or REPO, shell=True,
                          capture_output=True, text=True)


def lit_output(filter_expr: str | None = None) -> str:
    # The same lit the build was configured against, found the way the build
    # finds it: LLVM_EXTERNAL_LIT if the environment names one, then PATH.
    lit = os.environ.get("LLVM_EXTERNAL_LIT") or shutil.which("llvm-lit")
    if not lit:
        raise SystemExit(
            "no llvm-lit: set LLVM_EXTERNAL_LIT to the one this build uses, "
            "or put llvm-lit on PATH")
    command = [lit, "-v", str(BUILD / "test")]
    if filter_expr:
        command += ["--filter", filter_expr]
    return run(command).stdout


# --------------------------------------------------------------------------
# Harvest
# --------------------------------------------------------------------------


@dataclass
class Harvest:
    pairs: set[tuple[str, str]] = field(default_factory=set)
    channels: dict[str, int] = field(default_factory=dict)
    unparsed: list[str] = field(default_factory=list)

    def add(self, channel: str, stale: str, fresh: str) -> None:
        if stale == fresh or frozen(stale) or frozen(fresh):
            return
        self.pairs.add((stale, fresh))
        self.channels[channel] = self.channels.get(channel, 0) + 1


def harvest(output: str) -> Harvest:
    result = Harvest()
    for channel in CHANNELS:
        for match in channel.pattern.finditer(output):
            result.add(channel.name, match.group(channel.stale),
                       match.group(channel.fresh))

    for pattern in STRUCTURED:
        for match in pattern.finditer(output):
            try:
                fresh_doc = json.loads(match.group(1))
                stale_doc = json.loads(match.group(2))
            except json.JSONDecodeError:
                continue
            for key, fresh_value in fresh_doc.items():
                stale_value = stale_doc.get(key)
                if not isinstance(fresh_value, str) or not isinstance(stale_value, str):
                    continue
                if fresh_value != stale_value:
                    result.add("output anchor", stale_value.removeprefix("sha256:"),
                               fresh_value.removeprefix("sha256:"))

    for match in SUBJECT.finditer(output):
        fresh_digests = re.findall(r"[0-9a-f]{64}", match.group(1))
        stale_digests = re.findall(r"[0-9a-f]{64}", match.group(2))
        if len(fresh_digests) == len(stale_digests):
            for fresh, stale in zip(fresh_digests, stale_digests):
                result.add("premise subject", stale, fresh)

    for match in FILECHECK.finditer(output):
        want, got = match.group(1), match.group(2)
        # Same assertion, different values: the text before the first literal
        # has to be identical, or the two lines are not about the same thing.
        want_head = LITERAL.split(want)[0].strip().lstrip("/# ")
        got_head = LITERAL.split(got)[0].strip()
        if not want_head or want_head not in got_head:
            continue
        want_values = LITERAL.findall(want)
        got_values = LITERAL.findall(got)
        if len(want_values) != len(got_values):
            continue
        for stale, fresh in zip(want_values, got_values):
            if same_kind(stale, fresh):
                result.add("filecheck golden", stale, fresh)

    if not result.pairs:
        for line in output.splitlines():
            if line.startswith("FAIL:"):
                result.unparsed.append(failing_name(line))
    return result


# --------------------------------------------------------------------------
# Apply
# --------------------------------------------------------------------------


def failing_name(line: str) -> str:
    """`FAIL: ZKC :: Oir/x.test (3 of 118)` names test/Oir/x.test."""
    return "test/" + line.split("::", 1)[-1].split("(")[0].strip()


def files_containing(value: str) -> list[str]:
    listing = run(["git", "grep", "-l", value]).stdout.split()
    return [path for path in listing if "__pycache__" not in path]


def apply(pairs: set[tuple[str, str]], protected: set[str],
          dry_run: bool) -> tuple[int, set[tuple[str, str]]]:
    touched, blocked = 0, set()
    for stale, fresh in sorted(pairs):
        if not stale or not fresh:            # an empty half silently blanks pins
            continue
        if stale in protected:
            blocked.add((stale, fresh))
            continue
        for name in files_containing(stale):
            path = REPO / name
            try:
                text = path.read_text()
            except (UnicodeDecodeError, FileNotFoundError):
                continue
            if not dry_run:
                path.write_text(text.replace(stale, fresh))
            touched += 1
    return touched, blocked


def regenerate() -> list[str]:
    """Files one implementation owns outright are rewritten from it, not
    patched: a partial edit of a generated document is a corpus that agrees
    with nothing."""
    written = []
    for name in EXEC_VECTORS:
        target = REPO / f"test/Oir/Inputs/{name}-exec-vectors.json"
        result = shell(f"uv run python -m oracle.exec {name}", cwd=REPO / "reference")
        if result.returncode != 0 or not result.stdout.strip():
            print(f"  ! oracle.exec {name} produced nothing; left alone",
                  file=sys.stderr)
            continue
        if target.read_text() != result.stdout:
            target.write_text(result.stdout)
            written.append(target.relative_to(REPO).as_posix())
    return written


# --------------------------------------------------------------------------
# Sentinels
# --------------------------------------------------------------------------


@dataclass
class AnchorResult:
    name: str
    pinned: str
    assurance: str
    native: str | None
    reference: str | None

    @property
    def split(self) -> bool:
        """Only an anchor this tool cross-checks itself can be seen to split;
        the others state where their cross-check lives."""
        return (self.assurance == "cross_checked_here"
                and self.native is not None and self.native != self.reference)

    @property
    def holds(self) -> bool:
        return not self.split and self.native == self.pinned


def compute(steps: list[str], workspace: Path) -> str | None:
    """Run one leg's recipe; the last step's stdout is the value."""
    # Substituted by hand rather than through str.format: these recipes carry
    # regexes, and a `{64}` repetition count is not a placeholder.
    environment = {"{bin}": str(BUILD / "bin"), "{repo}": str(REPO),
                   "{tmp}": str(workspace)}
    out = ""
    for step in steps:
        for placeholder, value in environment.items():
            step = step.replace(placeholder, value)
        result = shell(step)
        if result.returncode != 0:
            return None
        out = result.stdout
    value = out.strip()
    return value or None


def check_sentinels() -> list[AnchorResult]:
    document = json.loads(SENTINELS.read_text())
    results = []
    purge_pycache()
    with tempfile.TemporaryDirectory() as work:
        for anchor in document["anchors"]:
            workspace = Path(work) / anchor["name"]
            workspace.mkdir(parents=True, exist_ok=True)
            reference = anchor.get("reference")
            results.append(AnchorResult(
                anchor["name"], anchor["value"], anchor["assurance"],
                compute(anchor["native"], workspace),
                compute(reference, workspace) if reference else None))
    return results


def report_sentinels(results: list[AnchorResult]) -> int:
    split = [r for r in results if r.split]
    unreadable = [r for r in results if r.native is None]
    moved = [r for r in results
             if r.native is not None and not r.split and not r.holds]
    for anchor in split:
        print(f"SPLIT     {anchor.name}")
        print(f"          native    {anchor.native}")
        print(f"          reference {anchor.reference}")
    for anchor in unreadable:
        print(f"UNREADABLE {anchor.name}: its recipe produced no value")
    for anchor in moved:
        witness = ("both legs" if anchor.assurance == "cross_checked_here"
                   else anchor.assurance.replace("_", " "))
        print(f"MOVED     {anchor.name}")
        print(f"          pinned    {anchor.pinned}")
        print(f"          computed  {anchor.native}  ({witness})")
    held = len(results) - len(split) - len(moved) - len(unreadable)
    print(f"{held}/{len(results)} anchors hold"
          + (f", {len(moved)} moved" if moved else "")
          + (f", {len(unreadable)} unreadable" if unreadable else "")
          + (f", {len(split)} SPLIT ACROSS IMPLEMENTATIONS" if split else ""))
    if split:
        print("\nA split is the finding, not an obstacle: the two implementations "
              "no longer agree, so nothing is minted.", file=sys.stderr)
        return 2
    return 1 if (moved or unreadable) else 0


def accept_sentinels(results: list[AnchorResult]) -> int:
    if any(r.split for r in results):
        print("refusing to accept: the implementations disagree", file=sys.stderr)
        return 2
    if any(r.native is None for r in results):
        print("refusing to accept: an anchor produced no value", file=sys.stderr)
        return 2
    document = json.loads(SENTINELS.read_text())
    index = {r.name: r for r in results}
    moved = 0
    for anchor in document["anchors"]:
        result = index[anchor["name"]]
        if result.holds or result.native is None:
            continue
        for name in anchor.get("asserted_in", []):
            path = REPO / name
            path.write_text(path.read_text().replace(anchor["value"], result.native))
        print(f"accepted  {anchor['name']}: {anchor['value']} -> {result.native}")
        anchor["value"] = result.native
        moved += 1
    SENTINELS.write_text(json.dumps(document, indent=2) + "\n")
    print(f"{moved} anchor(s) accepted")
    return 0


# --------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------


def anchor_context() -> tuple[set[str], dict[str, str], str]:
    """The anchors, the tests that assert them, and the meta test that
    reports them — all three have to be known before a round is read."""
    document = json.loads(SENTINELS.read_text())
    protected = {a["value"].removeprefix("sha256:") for a in document["anchors"]}
    asserting = {name: a["name"]
                 for a in document["anchors"] for name in a.get("asserted_in", [])}
    return protected, asserting, "test/Meta/identity-anchors.test"


def command_run(max_rounds: int, dry_run: bool) -> int:
    protected, asserting, meta_test = anchor_context()
    blocked_total: set[tuple[str, str]] = set()
    applied_total = 0

    for round_number in range(1, max_rounds + 1):
        # Generated files are rewritten from their owner before the corpus is
        # read: while one is stale the tests fail on the file comparison, which
        # says nothing about the values a later assertion would have named.
        written = [] if dry_run else regenerate()
        for name in written:
            print(f"regenerated {name}")

        purge_pycache()
        output = lit_output()
        failing = output.count("\nFAIL:")
        if failing == 0:
            print(f"round {round_number}: suite green")
            break
        found = harvest(output)
        touched, blocked = apply(found.pairs, protected, dry_run)
        blocked_total |= blocked
        applied_total += touched
        summary = ", ".join(f"{name} x{count}"
                            for name, count in sorted(found.channels.items()))
        print(f"round {round_number}: {failing} failing; "
              f"{len(found.pairs)} pair(s) [{summary or 'none'}]; "
              f"{touched} file edit(s)"
              + (f"; {len(written)} regenerated" if written else ""))
        if not touched and not written:
            break

    purge_pycache()
    final = lit_output()
    still_failing = sorted({failing_name(line) for line in final.splitlines()
                            if line.startswith("FAIL:")})

    # A test that asserts an anchor is meant to fail while the anchor is
    # unaccepted; reporting it as unexplained would bury the one line that
    # matters under the ones that do not.
    waiting = {name: asserting[name] for name in still_failing if name in asserting}
    if meta_test in still_failing:
        waiting[meta_test] = "the anchor report itself"
    stuck = [name for name in still_failing if name not in waiting]

    print()
    if blocked_total or waiting:
        print("anchors moved; the tool does not move them for you.")
        for stale, fresh in sorted(blocked_total):
            print(f"  {stale} -> {fresh}")
        for name, anchor in sorted(waiting.items()):
            print(f"  {name}  (asserts {anchor})")
        print("  review with `remint.py sentinels`, then "
              "`remint.py sentinels --accept`")
    if stuck:
        print("\nfailures no channel explains — these need a person:")
        for name in stuck:
            print(f"  {name}")
    print(f"\n{applied_total} edit(s) applied; {len(still_failing)} test(s) "
          f"failing ({len(waiting)} waiting on an anchor, {len(stuck)} unexplained)")
    return 0 if not stuck else 1


def command_status() -> int:
    purge_pycache()
    output = lit_output()
    failing = sorted({failing_name(line) for line in output.splitlines()
                      if line.startswith("FAIL:")})
    if not failing:
        print("suite green")
        return 0
    found = harvest(output)
    print(f"{len(failing)} failing test(s); "
          f"{len(found.pairs)} value(s) the channels can derive")
    for name in failing:
        print(f"  {name}")
    return 1


def main() -> int:
    global BUILD
    parser = argparse.ArgumentParser(
        description="Re-mint derived fixture values; guard the anchors.")
    parser.add_argument("--build-dir", type=Path, default=BUILD,
                        help="the build this judges (default: <repo>/build)")
    sub = parser.add_subparsers(dest="command", required=True)
    run_parser = sub.add_parser("run", help="re-mint derived values to a fixed point")
    run_parser.add_argument("--max-rounds", type=int, default=12)
    run_parser.add_argument("--dry-run", action="store_true")
    sentinel_parser = sub.add_parser("sentinels", help="verify the anchors")
    sentinel_parser.add_argument("--accept", action="store_true")
    sub.add_parser("status", help="what is failing and what is derivable")
    args = parser.parse_args()
    BUILD = args.build_dir.resolve()

    if args.command == "run":
        return command_run(args.max_rounds, args.dry_run)
    if args.command == "status":
        return command_status()
    results = check_sentinels()
    if args.accept:
        return accept_sentinels(results)
    return report_sentinels(results)


if __name__ == "__main__":
    raise SystemExit(main())
