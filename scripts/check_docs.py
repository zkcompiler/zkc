#!/usr/bin/env python3
"""Check the local links, heading fragments and reachability of this repository's Markdown.

Every inline link to a local path must name a file or directory of the public tree, and a
fragment into a Markdown page must name one of its headings. Every checked page other than
README.md and AGENTS.md must be reachable from README.md or docs/README.md by following local
links. External links are not fetched.

Without --all the check covers README.md, AGENTS.md and docs/. With --all it also covers the
guides beside the sources: .github/, language/, libraries/, examples/ and the guides of the
Lean packages.
"""

import argparse
import collections
import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
PRIVATE = ROOT / "docs" / "private"

ROOT_PAGES = ["README.md", "AGENTS.md"]
START_PAGES = ["README.md", "docs/README.md"]
GUIDE_FOLDERS = [".github", "language", "libraries", "examples"]
LEAN_GUIDES = [
    "lean/compiler/README.md",
    "lean/compiler/Zkc/Core/README.md",
    "lean/compiler/Zkc/Frontend/README.md",
    "lean/formal/README.md",
]

LINK = re.compile(r'(?<!!)\[[^]]*\]\(([^)\s]+)(?:\s+"[^"]*")?\)')
HEADING = re.compile(r"^#{1,6}\s+(.*?)\s*#*$", re.M)


def unfenced(text):
    """Blank fenced code blocks, keeping one output line per input line."""
    kept = []
    fence = None
    for line in text.splitlines():
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
    """The fragments that the ATX headings of a page define, as GitHub derives them."""
    seen = collections.Counter()
    result = set()
    for title in HEADING.findall(unfenced(path.read_text())):
        title = re.sub(r"\[([^]]+)\]\([^)]*\)", r"\1", title)
        title = re.sub(r"<[^>]*>", "", title).lower()
        title = re.sub(r"[^\w\-\s]", "", title).replace(" ", "-")
        result.add(title + ("-" + str(seen[title]) if seen[title] else ""))
        seen[title] += 1
    return result


def public(path):
    target = path.resolve()
    return target.is_relative_to(ROOT) and not target.is_relative_to(PRIVATE.resolve())


def pages(include_guides):
    """The checked pages, and an error for each listed page that does not exist."""
    found = [ROOT / name for name in ROOT_PAGES]
    found += [p for p in (ROOT / "docs").rglob("*.md") if public(p)]
    listed = list(found)
    if include_guides:
        for folder in GUIDE_FOLDERS:
            found += (ROOT / folder).rglob("*.md")
        guides = [ROOT / name for name in LEAN_GUIDES]
        found += guides
        listed += guides
    errors = [[str(p.relative_to(ROOT)), "-", "listed page missing"]
              for p in listed if not p.is_file()]
    return sorted({p.resolve() for p in found if p.is_file()}), errors


def check(include_guides):
    checked, errors = pages(include_guides)
    links = fragments = 0
    outgoing = collections.defaultdict(set)
    for page in checked:
        label = str(page.relative_to(ROOT))
        # Link text may wrap across lines, so it is matched without a line bound.
        for target in LINK.findall(unfenced(page.read_text())):
            target = target.strip("<>")
            url = urlsplit(target)
            if url.scheme or target.startswith("//"):
                continue
            links += 1
            path = (page.parent / unquote(url.path)).resolve() if url.path else page
            if not public(path):
                errors.append([label, target, "outside the public repository"])
                continue
            if not path.exists():
                errors.append([label, target, "missing"])
                continue
            outgoing[page].add(path)
            if url.fragment and path.suffix == ".md":
                fragments += 1
                if unquote(url.fragment) not in anchors(path):
                    errors.append([label, target, "no such heading"])
    reached = {(ROOT / name).resolve() for name in START_PAGES}
    frontier = list(reached)
    while frontier:
        for target in outgoing[frontier.pop()]:
            if target not in reached:
                reached.add(target)
                frontier.append(target)
    roots = {(ROOT / name).resolve() for name in ROOT_PAGES}
    for page in checked:
        if page not in reached and page not in roots:
            errors.append([str(page.relative_to(ROOT)), "-",
                           "unreachable from README.md and docs/README.md"])
    return len(checked), links, fragments, errors


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--all", action="store_true",
                        help="also check the guides beside the sources")
    args = parser.parse_args()
    count, links, fragments, errors = check(args.all)
    for page, target, reason in errors:
        print(f"{page}: {target}: {reason}")
    status = "fail" if errors else "pass"
    print(f"{status}: {count} pages, {links} local links, {fragments} fragments, "
          f"{len(errors)} errors")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
