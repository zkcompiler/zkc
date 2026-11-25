"""Exercise goal selection, aggregation and exported challenges through zkc-check."""

from pathlib import Path
import resource
import signal
import subprocess
from tempfile import TemporaryDirectory
from textwrap import indent

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


def run(files, selectors, output, code, *, file_limit=None):
    args = [".lake/build/bin/zkc-check", "written-goals", "--library", "../../libraries"]
    for selector in selectors:
        args.extend(["--goal", selector])
    def limit_output():
        signal.signal(signal.SIGXFSZ, signal.SIG_IGN)
        resource.setrlimit(resource.RLIMIT_FSIZE, (file_limit, file_limit))

    result = subprocess.run([*args, "--output", output, *files], text=True, capture_output=True,
                            preexec_fn=limit_output if file_limit is not None else None)
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

    # Distinct long paths can share every complete chunk before their last.
    long_name = "가" * 42
    longer = long_name + "x"
    selectors = ["root", "verifier", "root0", long_name, longer]
    extras = "".join(f"goal {name} = soundness(Checked, clause = primary)\n" for name in selectors)
    src.write_text(original + extras)
    rows, issued = run([src], selectors, work / "names", 0)
    assert len(issued) == 2 * len(selectors)
    for row in rows:
        module = row.split(": issued ")[1].split()[0]
        folder = module.removesuffix(".Challenge").replace(".", "/")
        stated_module = module.removesuffix(".Challenge") + ".Stated"
        assert issued[f"{folder}/Challenge.lean"].startswith(f"import {stated_module}\n".encode())
    _, reversed_names = run([src], list(reversed(selectors)), work / "names-reversed", 0)
    assert issued == reversed_names

    # A real short write in the middle must leave both good targets publishable,
    # repeat the failed result for its alias, and leave no half-written pair.
    large_relation = "x" + " and x" * 24
    src.write_text(original.replace("Other(x: bool): x", f"Other(x: bool): {large_relation}")
                   + "goal last = soundness(Checked, clause = primary)\n")
    _, full = run([src], ["first", "second", "last"], work / "unlimited", 0)
    survivors = {key: data for key, data in full.items() if "__second/" not in key}
    limit = max(map(len, full.values())) - 1
    assert max(map(len, survivors.values())) <= limit and len(survivors) == 4
    rows, partial = run([src], ["first", "second", "sibling::second", "last"],
                        work / "limited", 1, file_limit=limit)
    assert partial == survivors and not (work / "limited" / ".pending").exists()
    assert all("export failed" in row for row in rows[1:3]), rows
    rows, kept = run([src], ["first", "last"], work / "unlimited", 1)
    assert kept == full and all("export failed" in row for row in rows)
    src.write_text(original)

    other = work / "other.zkc"
    other.write_text(src.read_text().replace("module sibling", "module other"))
    rows, files = run([src, other], ["first", "sibling::first", "other::first"], work / "ambiguous", 1)
    assert "ambiguous" in rows[0] and len(files) == 4
    assert rows[1].split(": issued ")[1] != rows[2].split(": issued ")[1]

    # The same path can be formed by a nested module and by a file module.
    # A relative selector must never borrow the other declaration's challenge.
    nested = work / "nested.zkc"
    block = original.split("::{soundness}\n", 1)[1]
    nested.write_text("module a\nuse zkc::security::{soundness}\nmodule b:\n"
                      + indent(block.replace(" = primary)", " = absent)"), "    "))
    leaf = work / "leaf.zkc"
    leaf.write_text(original.replace("module sibling", "module a::b"))
    for order, inputs in enumerate([[nested, leaf], [leaf, nested]]):
        rows, files = run(inputs, ["b::first", "a::b::first", "first"], work / f"shadow-{order}", 1)
        assert not files and all("ambiguous" in row for row in rows), rows
    rows, files = run([nested], ["b::first"], work / "nested-alone", 1)
    assert not files and "GL3" in rows[0]
    run([leaf], ["a::b::first"], work / "leaf-alone", 0)

    # A verifier-visible requirement belongs in both the soundness claim and
    # the witness of satisfiability. The current issuer refuses to omit it.
    src.write_text(original.replace("spec for Check:", "spec for Check:\n    requires false"))
    rows, files = run([src, other], ["sibling::first", "other::first"], work / "hypothesis", 1)
    assert "SX7" in rows[0] and "requires" in rows[0] and "issued" in rows[1] and len(files) == 2
    private_port = original.replace("x: bool @(P,V)):", "x: bool @(P,V), hidden: bool @P):")
    for case, expr, code in [("private", "hidden and x", 0), ("shared", "x", 1)]:
        src.write_text(private_port.replace("spec for Check:", f"spec for Check:\n    requires {expr}"))
        rows, files = run([src], ["first"], work / f"requires-{case}", code)
        if code == 0:
            assert len(files) == 2
        else:
            assert "SX7" in rows[0] and not files
    src.write_text(original)

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
