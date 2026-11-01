#!/usr/bin/env python3
"""Check this reference's local Markdown links, heading fragments and reachability.

This checks the inline-link/ATX-heading syntax used by these pages and the
fixture digest tables of fixture guides. It does not fetch external links or
check mathematical truth.
"""

import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[2]


def unfenced(lines):
    """Blank fenced code blocks, keeping one output line per input line."""
    kept = []
    fence = None
    for line in lines:
        match = re.match(r"^\s*(`{3,}|~{3,})", line)
        if match:
            if fence is None:
                fence = match[1][0]
            elif fence == match[1][0]:
                fence = None
            kept.append("")
            continue
        kept.append("" if fence else line)
    return kept


def prose(path):
    return "\n".join(unfenced(path.read_text().splitlines()))


# A fixture guide records the SHA-256 of its retained bytes under this heading,
# in a `| File | SHA-256 |` table with one row per file named relative to the
# guide. check() compares every row with the bytes;
# scripts/regenerate-interface-fixtures.py rewrites the rows it regenerates.
FIXTURE_DIGEST_HEADING = "Current fixture SHA-256"
FIXTURE_DIGEST_ROW = re.compile(r"^\| `([^`]+)` \| `([0-9a-f]{64})` \|$")
FIXTURE_DIGEST_HEADER = re.compile(r"^\| File \| SHA-256 \|$|^\|\s*:?-+:?\s*\|\s*:?-+:?\s*\|$")


def fixture_digest_row(name, digest):
    return f"| `{name}` | `{digest}` |"


def fixture_digest_tables(lines):
    """Return each fixture digest section of a guide as (heading index, rows).

    A row is (line index, file, recorded digest). Any other table row in the
    section except the header and its delimiter is (line index, None, None), so
    readers refuse it rather than skip it. Indices count the given lines.
    """
    tables, current = [], None
    for index, line in enumerate(unfenced(lines)):
        heading = re.match(r"^#{1,6}\s+(.*?)\s*#*$", line)
        if heading:
            current = (index, []) if heading[1] == FIXTURE_DIGEST_HEADING else None
            if current:
                tables.append(current)
        elif current and line.startswith("|") and not FIXTURE_DIGEST_HEADER.match(line):
            row = FIXTURE_DIGEST_ROW.match(line)
            current[1].append((index, row[1], row[2]) if row else (index, None, None))
    return tables


def fixture_digest_errors(page, label, public_path):
    """Compare every fixture digest row of one guide with the file's bytes."""
    errors, checked = [], 0
    directory = page.parent.resolve()
    # Split on "\n" only, as the regeneration script does when it rewrites rows.
    for heading, rows in fixture_digest_tables(page.read_text().split("\n")):
        if not rows:
            errors.append([label, heading + 1, "fixture digest table has no rows"])
        seen = set()
        for index, name, recorded in rows:
            if name is None:
                errors.append([label, index + 1, "malformed fixture digest row"])
                continue
            path = (page.parent / name).resolve()
            if name in seen:
                errors.append([label, name, "duplicate fixture digest row"])
            elif not path.is_relative_to(directory) or not public_path(path):
                errors.append([label, name, "fixture outside the guide's directory"])
            elif not path.is_file():
                errors.append([label, name, "fixture missing"])
            else:
                checked += 1
                if hashlib.sha256(path.read_bytes()).hexdigest() != recorded:
                    errors.append([label, name, "fixture digest differs"])
            seen.add(name)
    return errors, checked


def anchors(path):
    seen = collections.Counter()
    result = set()
    for title in re.findall(r"^#{1,6}\s+(.*?)\s*#*$", prose(path), re.M):
        title = re.sub(r"\[([^]]+)\]\([^)]*\)", r"\1", title)
        title = re.sub(r"<[^>]*>", "", title).lower()
        title = re.sub(r"[^\w\-\s]", "", title).replace(" ", "-")
        slug = title + ("-" + str(seen[title]) if seen[title] else "")
        seen[title] += 1
        result.add(slug)
    return result


# What a rationale record never carries: how a choice was reached, and the
# names of the work that reached it. docs/rationale/README.md states the rules.
RATIONALE_FORBIDDEN = [
    (r"\b20\d\d-\d\d-\d\d\b", "date"),
    (r"/tmp/", "temporary path"),
    (r"\b[0-9a-f]{12,40}\b", "commit or content identifier"),
    (r"\b[SWDC]\d{1,2}(-\d+)?\b|\bGoal \d\b", "work-unit label"),
    (r"\b(handoff|receipt|snapshot)\b", "process record"),
]


def rationale(page, outgoing, incoming, home):
    """Rules of docs/rationale that a program can check."""
    text = prose(page)
    found = []
    if not any(home not in target.parents for target in outgoing):
        found.append("no link to a page that owns the choice")
    if not any(home not in source.parents for source in incoming):
        found.append("no page outside this folder links to this record")
    for pattern, name in RATIONALE_FORBIDDEN:
        match = re.search(pattern, text)
        if match:
            found.append(f"{name}: {match.group(0)}")
    return found


def component_pages():
    """Include component guides without walking build or private dependency trees."""
    ignored = {".git", ".lake", "target", "build", "node_modules", "__pycache__",
               ".cache", ".work", "records"}
    for folder in (".github", "compiler", "crates", "examples", "libraries", "common",
                   "lean/bridges"):
        for directory, children, files in os.walk(ROOT / folder):
            children[:] = sorted(name for name in children if name not in ignored
                                 and not name.startswith(".venv"))
            for name in sorted(files):
                if name.endswith(".md"):
                    yield Path(directory) / name


def check(include_components=False):
    # docs/private holds non-public material checked out inside docs/.
    private = ROOT / "docs" / "private"
    public_root, private_root = ROOT.resolve(), private.resolve()

    def public_path(path):
        target = path.resolve()
        return target.is_relative_to(public_root) and not target.is_relative_to(private_root)

    active = sorted(p for p in (ROOT / "docs").rglob("*.md") if private not in p.parents)
    extra = ["README.md"]
    formal_pages = sorted((ROOT / "lean").glob("*.md"))
    formal_reference = sorted((ROOT / "lean" / "docs").rglob("*.md"))
    formal_pages += formal_reference
    formal_pages += sorted((ROOT / "lean" / "Zkc").rglob("*.md"))
    formal_pages += sorted((ROOT / "lean" / "ZkcExamples").rglob("*.md"))
    formal_pages += sorted((ROOT / "lean" / "integrations").glob("*/*.md"))
    pages = active + formal_pages + [ROOT / p for p in extra]
    if include_components:
        pages = sorted(set(pages) | set(component_pages()))
    errors = [[str(p.relative_to(ROOT)), "outside public repository"]
              for p in pages if not public_path(p)]
    pages = [p for p in pages if public_path(p)]
    active = [p for p in active if public_path(p)]
    formal_reference = [p for p in formal_reference if public_path(p)]
    links = fragments = digests = 0
    outgoing = collections.defaultdict(set)
    incoming = collections.defaultdict(set)
    for page in pages:
        label = str(page.relative_to(ROOT))
        # Link text may wrap across lines, so it is matched without a line bound.
        for target in re.findall(r'(?<!!)\[[^]]*\]\(([^)\s]+)(?:\s+"[^"]*")?\)', prose(page)):
            target = target.strip("<>")
            url = urlsplit(target)
            if url.scheme or target.startswith("//"):
                continue
            links += 1
            path = (page.parent / unquote(url.path)).resolve() if url.path else page
            if not public_path(path):
                errors.append([label, target, "outside public repository"])
                continue
            if not path.exists():
                errors.append([label, target, "missing"])
                continue
            outgoing[page.resolve()].add(path)
            incoming[path].add(page.resolve())
            if url.fragment and path.suffix == ".md":
                fragments += 1
                if unquote(url.fragment) not in anchors(path):
                    errors.append([label, target, "fragment"])
        for n, line in enumerate(page.read_text().splitlines(), 1):
            if line.rstrip() != line:
                errors.append([label, n, "trailing whitespace"])
        found, checked = fixture_digest_errors(page, label, public_path)
        errors += found
        digests += checked
    # Each reference is discoverable from its own index. Links from the other
    # reference do not make an otherwise orphaned page reachable.
    for reference, index_name, owner in (
        (active, "docs/README.md", ROOT / "docs"),
        (formal_reference, "lean/docs/README.md", ROOT / "lean"),
    ):
        index = (ROOT / index_name).resolve()
        reached, frontier = {index}, [index]
        while frontier:
            for target in outgoing[frontier.pop()]:
                if target not in reached and target.is_relative_to(owner.resolve()):
                    reached.add(target)
                    frontier.append(target)
        for page in sorted(p for p in reference if p.resolve() not in reached):
            errors.append([str(page.relative_to(ROOT)), f"unreachable from {index_name}"])
    home = (ROOT / "docs" / "rationale").resolve()
    for page in sorted(home.glob("*.md")):
        if page.name != "README.md":
            for finding in rationale(page, outgoing[page.resolve()],
                                     incoming[page.resolve()], home):
                errors.append([str(page.relative_to(ROOT)), finding])
    return {
        "status": "pass" if not errors else "fail",
        "pages": len(pages), "reference_pages": len(active),
        "formal_reference_pages": len(formal_reference),
        "local_links": links, "fragments": fragments, "fixture_digests": digests, "errors": errors,
        "page_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in pages},
        "scope": ("reference and component guides" if include_components else "reference and root/formal guides")
                 + "; local inline links, ATX heading fragments, native/formal reachability, public boundaries, whitespace, rationale rules and fixture digest tables",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--all", action="store_true", help="also check component and fixture guides")
    args = parser.parse_args()
    result = check(include_components=args.all)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "page_sha256"}, indent=2))
    if result["status"] != "pass":
        raise SystemExit(1)
