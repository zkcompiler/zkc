#!/usr/bin/env python3
"""Check this reference's local Markdown links, heading fragments and reachability.

This checks the inline-link/ATX-heading syntax used by these pages. It does not
fetch external links, check mathematical truth, or rewrite historical documents.
"""

import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parent.parent


def prose(path):
    kept = []
    fence = None
    for line in path.read_text().splitlines():
        match = re.match(r"^\s*(`{3,}|~{3,})", line)
        if match:
            if fence is None:
                fence = match[1][0]
            elif fence == match[1][0]:
                fence = None
            kept.append("")
            continue
        kept.append("" if fence else line)
    return "\n".join(kept)


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


RATIONALE_LIMIT = 80
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
    lines = page.read_text().count("\n")
    if lines > RATIONALE_LIMIT:
        found.append(f"{lines} lines; a record has at most {RATIONALE_LIMIT}")
    if not any(home not in target.parents for target in outgoing):
        found.append("no link to a page that owns the choice")
    if not any(home not in source.parents for source in incoming):
        found.append("no page outside this folder links to this record")
    if not re.search(r"reopen when", text, re.I):
        found.append("no reopening condition")
    for pattern, name in RATIONALE_FORBIDDEN:
        match = re.search(pattern, text)
        if match:
            found.append(f"{name}: {match.group(0)}")
    return found


def component_pages():
    """Include component guides without walking build or private dependency trees."""
    ignored = {".git", ".lake", "target", "build", "node_modules", "__pycache__",
               ".cache", ".work", "records"}
    for folder in (".github", "bench", "compiler", "crates", "examples", "tests",
                   "formal/consumers"):
        for directory, children, files in os.walk(ROOT / folder):
            children[:] = sorted(name for name in children if name not in ignored
                                 and not name.startswith(".venv"))
            for name in sorted(files):
                if name.endswith(".md"):
                    yield Path(directory) / name


def check(include_components=False):
    # docs/private is a separate repository checked out inside docs/.
    private = ROOT / "docs" / "private"
    active = sorted(p for p in (ROOT / "docs").rglob("*.md") if private not in p.parents)
    extra = ["README.md"]
    formal_pages = sorted((ROOT / "formal").glob("*.md"))
    formal_pages += sorted((ROOT / "formal" / "design").rglob("*.md"))
    formal_pages += sorted((ROOT / "formal" / "Zkc").rglob("*.md"))
    formal_pages += sorted((ROOT / "formal" / "Examples").rglob("*.md"))
    formal_pages += sorted((ROOT / "formal" / "integrations" / "arklib").glob("*.md"))
    pages = active + formal_pages + [ROOT / p for p in extra]
    if include_components:
        pages = sorted(set(pages) | set(component_pages()))
    links = fragments = 0
    errors = []
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
    # Every page of the reference is reachable by links from its index, so a
    # page cannot exist outside the reading paths.
    index = (ROOT / "docs" / "README.md").resolve()
    reached, frontier = {index}, [index]
    while frontier:
        for target in outgoing[frontier.pop()]:
            if target not in reached:
                reached.add(target)
                frontier.append(target)
    for page in sorted(p for p in active if p.resolve() not in reached):
        errors.append([str(page.relative_to(ROOT)), "unreachable from docs/README.md"])
    home = (ROOT / "docs" / "rationale").resolve()
    for page in sorted(home.glob("*.md")):
        if page.name != "README.md":
            for finding in rationale(page, outgoing[page.resolve()],
                                     incoming[page.resolve()], home):
                errors.append([str(page.relative_to(ROOT)), finding])
    return {
        "status": "pass" if not errors else "fail",
        "pages": len(pages), "reference_pages": len(active),
        "local_links": links, "fragments": fragments, "errors": errors,
        "page_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in pages},
        "scope": ("reference and component guides" if include_components else "reference and root/formal guides")
                 + "; local inline links, ATX heading fragments, reference reachability, whitespace and rationale rules",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--all", action="store_true", help="also check component, benchmark and fixture guides")
    args = parser.parse_args()
    result = check(include_components=args.all)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "page_sha256"}, indent=2))
    if result["status"] != "pass":
        raise SystemExit(1)
