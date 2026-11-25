"""Exercise goal selection, aggregation and exported challenges through zkc-check."""

from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

SOURCE = """module sibling
use zkc::security::{soundness}
def custom(x: bool) -> bool = primitive("project.custom")
relation IsSet(x: bool): x
relation Other(x: bool): custom(x)
protocol Check roles(P,V)(x: bool @(P,V)):
    guard @V x
spec for Check:
    proves @V primary: IsSet(x)
    proves @V secondary: Other(x)
scheme Checked = Check:
    prover P
    construction interactive
goal first = soundness(Checked, clause = primary)
goal second = soundness(Checked, clause = secondary)
"""


def run(files, selectors, output, code):
    args = [".lake/build/bin/zkc-check", "written-goals", "--library", "../../libraries"]
    for selector in selectors:
        args.extend(["--goal", selector])
    result = subprocess.run([*args, "--output", output, *files], text=True, capture_output=True)
    assert result.returncode == code, (args, result.stdout, result.stderr)
    lines = result.stdout.splitlines()
    # Diagnostics may continue on subsequent lines.
    rows = [line for line in lines if " -> " in line]
    assert [line.split(" -> ", 1)[0] for line in rows] == selectors, lines
    artifacts = {str(f.relative_to(output)): f.read_bytes() for f in output.rglob("*.lean")}
    return rows, artifacts


def check(work):
    src = work / "sibling.zkc"
    src.write_text(SOURCE)
    one, target = run([src], ["first"], work / "one", 0)
    assert len(target) == 2 and any(name.endswith("/Challenge.lean") for name in target)
    assert "sibling::first: issued" in one[0]
    for i, (text, diagnostic) in enumerate([
        (SOURCE, "project.custom"),
        (SOURCE.replace(" = secondary)", " = absent)"), "GL3"),
        (SOURCE.replace("secondary: Other(x)", "secondary: Other(x and x)"), "WK-CLAUSE"),
        (SOURCE.replace("soundness(Checked, clause = secondary)", "soundness(Missing)"), "NL"),
    ]):
        src.write_text(text)
        for j, selectors in enumerate([["second", "first"], ["sibling::first", "second", "first"]]):
            rows, artifacts = run([src], selectors, work / f"mixed-{i}-{j}", 1)
            assert artifacts == target, (i, rows)
            for selector, row in zip(selectors, rows, strict=True):
                if selector == "second":
                    assert "sibling::second: refused" in row and diagnostic in row and src.name in row, row
                else:
                    assert "sibling::first: issued" in row, row

    src.write_text(SOURCE.replace("Other(x: bool): custom(x)", "Other(x: bool): x"))
    _, good = run([src], ["second", "first", "sibling::first"], work / "both", 0)
    assert len(good) == 4 and target.items() <= good.items()
    # A declaration before the root changes its numeric key. The canonical goal still
    # selects the same source and the newly emitted package carries the new key.
    prior = "protocol Prior roles(P,V)(x: bool @(P,V)):\n    guard @V x\n"
    original = src.read_text()
    src.write_text(original.replace("protocol Check", prior + "protocol Check"))
    rows, renumbered = run([src], ["first"], work / "renumbered", 0)
    assert rows[0].split(", root ")[1].split(",")[0] != one[0].split(", root ")[1].split(",")[0]
    assert renumbered.keys() == target.keys() and renumbered != target
    src.write_text(original)

    rows, files = run([src], ["missing", "missing"], work / "missing", 1)
    assert not files and all("WK-GOAL" in row for row in rows)

    src.write_text(original + "\ngoal root = soundness(Checked, clause = primary)\n")
    _, root_files = run([src], ["root"], work / "root", 0)
    stated = next(text for name, text in root_files.items() if name.endswith("/Stated.lean"))
    assert b"abbrev rootKey" in stated and b"abbrev sourceGoalKey" in stated
    src.write_text(original)

    other = work / "other.zkc"
    other.write_text(src.read_text().replace("module sibling", "module other"))
    rows, files = run([src, other], ["first", "sibling::first", "other::first"], work / "ambiguous", 1)
    assert "ambiguous" in rows[0] and len(files) == 4
    assert rows[1].split(": issued ")[1] != rows[2].split(": issued ")[1]

    src.write_text(original + """
protocol Broken roles(P,V)(x: bool @(P,V)):
    guard @V x + 1
spec for Broken:
    proves @V IsSet(x)
scheme Unusable = Broken:
    prover P
    construction interactive
goal broken = soundness(Unusable)
""")
    rows, files = run([src], ["broken", "first"], work / "admission", 1)
    assert "refused" in rows[0] and "issued" in rows[1] and len(files) == 2, rows
    src.write_text(SOURCE.replace("guard @V x", "guard @V custom(x)"))
    rows, files = run([src], ["first", "second"], work / "shared", 1)
    assert not files and all("project.custom" in row for row in rows)
    src.write_text("module broken\nthis is not a declaration\n")
    rows, files = run([src], ["first", "second"], work / "parse", 1)
    assert not files and all(": refused:" in row for row in rows)
    run([src], [], work / "empty", 2)


if __name__ == "__main__":
    with TemporaryDirectory() as folder:
        check(Path(folder))
