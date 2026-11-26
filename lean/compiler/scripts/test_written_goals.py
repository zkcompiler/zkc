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
    rows = []
    for line in lines:
        if " -> " in line:
            rows.append(line)
        elif rows:
            rows[-1] += "\n" + line
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
    private_port = original.replace("x: bool @(P,V)):", "x: bool @(P,V), hidden: bool @P, "
                                    "localFlag: bool @V private, spec note: bool):")
    src.write_text(private_port)
    _, bare = run([src], ["first"], work / "no-hypothesis", 0)
    for case, expr, code in [("private", "hidden and x", 0), ("shared", "x", 1),
                             ("verifier", "localFlag", 1), ("spec", "note", 1)]:
        src.write_text(private_port.replace("spec for Check:", f"spec for Check:\n    requires {expr}"))
        rows, files = run([src], ["first"], work / f"requires-{case}", code)
        if code == 0:
            # The private requirement moves the deciding clause one place in the source
            # contract. Every other issued byte, including the challenge, stays the same.
            expected = bare.copy()
            stated = next(name for name in bare if name.endswith("/Stated.lean"))
            before = "  ⟨written'application0, 0, ".encode()
            after = "  ⟨written'application0, 1, ".encode()
            assert bare[stated].count(before) == 1
            expected[stated] = bare[stated].replace(before, after)
            assert files == expected
            src.write_text(private_port.replace("    proves @V secondary:", f"    requires {expr}\n    proves @V secondary:"))
            _, after_primary = run([src], ["first"], work / "requires-after-primary", 0)
            assert after_primary == bare
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
    rows, files = run([work / "absent.zkc"], ["first", "second"], work / "read", 1)
    assert not files and all("absent.zkc" in row and "refused" in row for row in rows)
    run([src], [], work / "empty", 2)


def check_member_ownership(work):
    src = work / "owners.zkc"
    prelude = "module owners\nuse zkc::security::{soundness}\n"
    protocol = """relation Holds(x: bool): x
protocol Check roles(P,V)(x: bool @(P,V)):
    guard @V via<M<1>>(x)
spec for Check:
    proves @V Holds(x)
scheme Checked = Check:
    prover P
    construction interactive
goal tested = soundness(Checked)
"""
    # A common interface supplies a single declaration through both arms of a diamond.
    diamond = """interface Common:
    def pick(x: bool) -> bool
interface A where (Self: Common)
interface B where (Self: Common)
module M: A + B + Common:
    def pick(x): x
def via<H: B>(x: bool) -> bool: H::pick(x)
"""
    shared = prelude + diamond + protocol.replace("via<M<1>>", "via<M>")
    src.write_text(shared)
    _, original = run([src], ["tested"], work / "diamond", 0)
    src.write_text(shared.replace("A + B + Common", "Common + B + A"))
    _, reversed_header = run([src], ["tested"], work / "diamond-reversed", 0)
    assert len(original) == 2 and original == reversed_header

    # A selected instance can fail while an independent goal still issues.
    generic = """interface I<n: nat>:
    def pick(x: bool) -> bool
module M<n: nat>: I<n> + I<0>:
    def pick(x): x
def via<H: I<0>>(x: bool) -> bool: H::pick(x)
"""
    clean = """protocol Clean roles(P,V)(x: bool @(P,V)):
    guard @V x
spec for Clean:
    proves @V Holds(x)
scheme CleanScheme = Clean:
    prover P
    construction interactive
goal good = soundness(CleanScheme)
"""
    shared = prelude + generic + protocol + clean
    src.write_text(shared)
    _, good = run([src], ["good"], work / "owner-good", 0)
    rows, kept = run([src], ["tested", "good"], work / "owner-local", 1)
    assert "SP8" in rows[0] and ": issued " in rows[1] and len(good) == 2 and kept == good

    # A parameterless module is a shared compilation root even when only good is requested.
    src.write_text(shared.replace("module M<n: nat>: I<n>", "module M: I<1>")
                   .replace("via<M<1>>", "via<M>"))
    for selectors in [["good"], ["tested", "good"]]:
        rows, files = run([src], selectors, work / f"owner-default-{len(selectors)}", 1)
        assert not files and all("SP8" in row for row in rows), rows


def check_selected_module(work):
    src = work / "selected.zkc"
    source = """module selected
use zkc::security::{soundness}
interface Carrier:
    def required(x: bool) -> bool
module M<n: nat>: Carrier:
    pub nat Width = n
    pub def helper(x: bool) -> bool: x
section <spec e: nat>:
    relation Holds(x: bool): if e == 0 then x else M<1>::helper(x)
    protocol Check roles(P,V)(x: bool @(P,V)):
        guard @V x
    spec for Check:
        proves @V Holds(x)
scheme Checked = Check:
    prover P
    construction interactive
goal good = soundness(Checked, spec e = 0)
goal bad = soundness(Checked, spec e = 1)
"""
    repaired = source.replace("    pub nat Width", "    def required(x): x\n    pub nat Width")
    src.write_text(repaired)
    _, healthy = run([src], ["good"], work / "selected-healthy", 0)
    for index, (text, rule) in enumerate([
        (source, "SP8"),
        (repaired.replace("def required(x): x", "def required(x): (x,x)"), "TY5"),
        (repaired.replace("def required(x): x", "def required(x): (x,x)")
         .replace("section <spec", "def pass<H: Carrier>(x: bool) -> bool: x\nsection <spec")
         .replace("M<1>::helper(x)", "pass<M<1>>(x)"), "TY5"),
        (source.replace("spec e = 1)", "spec e = M<1>::Width)")
               .replace("if e == 0 then x else M<1>::helper(x)", "x"), "SP8"),
        (source.replace("spec e = 1)", "spec e = 1) <= M<1>::Width")
               .replace("if e == 0 then x else M<1>::helper(x)", "x"), "SP8"),
    ]):
        src.write_text(text)
        for order, names in enumerate([["bad", "good"], ["good", "bad"]]):
            rows, files = run([src], names, work / f"selected-{index}-{order}", 1)
            assert rule in rows[names.index("bad")] and files == healthy, rows

    # Every goal that uses this deployed guard or charge needs the source module.
    for label, text in [
        ("guard", source.replace("guard @V x", "guard @V M<1>::helper(x)")),
        ("charge", source.replace("section <spec", 'type F = primitive("bls12-381.fr")\nsection <spec')
         .replace("guard @V x", "r <- draw F from V to P\n        guard @V x")
         .replace("proves @V Holds(x)", "proves @V Holds(x)\n        charge sites.r <= M<1>::Width / 2")),
    ]:
        src.write_text(text)
        rows, files = run([src], ["good", "bad"], work / f"selected-{label}", 1)
        assert all("SP8" in row for row in rows) and not files, rows


def check_transitive_owners(work):
    """A written goal needs the sources that determined its types, operations and law eligibility."""
    src = work / "transitive.zkc"
    selected = """relation Holds(x: bool): x
protocol Check roles(P,V)(x: bool @(P,V)):
    guard @V EXPRESSION
spec for Check:
    proves @V Holds(x)
scheme Checked = Check:
    prover P
    construction interactive
goal tested = soundness(Checked)
"""
    base = """module transitive
use zkc::security::{soundness}
interface Carrier:
    def required(x: bool) -> bool
module M<n: nat>: Carrier:
    pub def flag(x: bool) -> bool: x
"""
    view = """protocol Source roles(P,V)(x: bool @(P,V)):
    guard @V M<1>::flag(x)
def dependency<T>(x: bool) -> bool: x
"""
    cases = [
        ("intrinsic", '    pub def size<T>(xs: [T]) -> nat = primitive("seq.length")\n',
         "M<1>::size([x]) == 1", "SP8"),
        ("bound", "    pub interface Mark\nmodule N<n: nat>: M<n>::Mark:\n"
         "    pub def check(x: bool) -> bool: x\n", "N<1>::check(x)", "SP8"),
        ("child", "interface Parent:\n    module Child: Carrier\nmodule N<n: nat>: Parent:\n"
         "    module Child = M<n>\n    pub def check(x: bool) -> bool: x\n", "N<1>::check(x)", "SP8"),
        ("default", "interface Parent:\n    def apply<H: Carrier>(x: bool) -> bool\n"
         "module N<n: nat>: Parent:\n    def apply(x): x\n    pub def check(x: bool) -> bool: x\n",
         "N<1>::check(x)", "TY5"),
        ("view-cold", view, "dependency<Source::Run>(x)", "SP8"),
        ("view-warm", view + "def first(v: Source::Run) -> bool: true\n",
         "dependency<Source::Run>(x)", "SP8"),
        ("other-view-warm", view + "def first(v: Source::Run) -> bool: true\n",
         "dependency<Source::Received<V>>(x)", "SP8"),
        ("inputs-only", view + "def first(v: Source::Inputs<V>) -> bool: true\n",
         "dependency<Source::Inputs<V>>(x)", None),
    ]
    good = base.replace("    pub def flag", "    def required(x): x\n    pub def flag")
    for label, declarations, expression, rule in cases:
        # A missing declaration prevents a module-valued child's signature from forming.
        # A bad body lets a module become the default argument and fails its subsequent check.
        bad = good.replace("def required(x): x", "def required(x): (x,x)") if label == "default" else base
        for variant, text, expected in [("bad", bad, rule), ("good", good, None)]:
            src.write_text(text + declarations + selected.replace("EXPRESSION", expression))
            rows, files = run([src], ["tested"], work / f"transitive-{label}-{variant}", int(bool(expected)))
            if expected:
                assert expected in rows[0] and not files, (label, rows)
            else:
                assert "issued" in rows[0] and len(files) == 2, (label, rows)

    # Checking whether a law applies consumes the source of the condition on either outcome.
    law = """    pub nat Height = 0
interface Parent:
    type T
module N<n: nat>: Parent:
    type T = bool
    pub def check(x: bool) -> bool: x
    law reflexive(x: bool) where (M<n>::Height == VALUE): x == x
"""
    for value in [0, 1]:
        for valid in [False, True]:
            text = good if valid else base
            src.write_text(text + law.replace("VALUE", str(value)) + selected.replace("EXPRESSION", "N<1>::check(x)"))
            rows, files = run([src], ["tested"], work / f"predicate-{value}-{valid}", int(not valid))
            if valid:
                assert "issued" in rows[0] and len(files) == 2, rows
            else:
                assert "SP8" in rows[0] and not files, rows


def check_enclosing_scheme(work):
    src = work / "scheme.zkc"
    src.write_text("""module library
use zkc::security::{soundness}
interface Carrier:
    def required(x: bool) -> bool
protocol Check roles(P,V)(x: bool @(P,V)):
    guard @V x
relation Holds(x: bool): x
spec for Check:
    proves @V Holds(x)
module Box: Carrier:
    def required(x): x
    pub scheme Checked = Check:
        prover P
        construction interactive
goal tested = soundness(Box::Checked)
""")
    closed = src.read_text()
    rows, artifacts = run([src], ["tested"], work / "scheme-closed", 0)
    assert len(artifacts) == 2 and "issued" in rows[0]
    for label, text, rule in [
        ("missing", closed.replace("    def required(x): x\n", ""), "SP8"),
        ("open", closed.replace("module Box:", "module Box<n: nat>:"), "SP6"),
    ]:
        src.write_text(text)
        rows, artifacts = run([src], ["tested"], work / f"scheme-{label}", 1)
        assert rule in rows[0] and not artifacts, rows


def check_waiting_owner(work):
    src = work / "waiting.zkc"
    source = """module waiting
interface Width:
    nat Size
module Stub<n: nat>: Width = primitive("project.stub")
def use_width<H: Width>(x: bool) -> bool: if H::Size == 1 then x else false
interface Carrier:
    def required(x: bool) -> bool
module M<n: nat>: Carrier:
    def required(x): use_width<Stub<n>>(x)
    pub def flag(x: bool) -> bool: x
def selected(x: bool) -> bool: M<1>::flag(x)
def healthy(x: bool) -> bool: x
"""
    for waiting in [True, False]:
        src.write_text(source if waiting else source.replace(' = primitive("project.stub")', ':\n    nat Size = 1'))
        lines = subprocess.run([".lake/build/bin/zkc-check", "types", "--library", "../../libraries", src],
                               capture_output=True, text=True, check=True).stdout.splitlines()
        prefix = "package selected: waiting for the member" if waiting else "package selected: admitted"
        assert any(line.startswith(prefix) for line in lines), lines
        assert any(line.startswith("package healthy: admitted") for line in lines), lines
        assert f"{int(waiting)} waiting" in next(line for line in lines if line.startswith("packages:")), lines


def check_instance_summary(work):
    source = work / "signature.zkc"
    source.write_text("""module signature
interface Carrier:
    type T
    def required(x: bool) -> bool
module M<n: nat>: Carrier:
    type T = bool
def project(x: M<1>::T) -> bool: x
""")
    checker = ".lake/build/bin/zkc-check"
    inventory = subprocess.run([checker, "instances", "--contents", source], capture_output=True,
                               text=True, check=True).stdout
    assert "from signature and default checks" in inventory and "project" in inventory, inventory
    checked = subprocess.run([checker, "types", source], capture_output=True, text=True)
    assert checked.returncode == 1 and "SP8" in checked.stdout, checked


if __name__ == "__main__":
    with TemporaryDirectory() as folder:
        check(Path(folder))
        check_member_ownership(Path(folder))
        check_selected_module(Path(folder))
        check_transitive_owners(Path(folder))
        check_waiting_owner(Path(folder))
        check_enclosing_scheme(Path(folder))
        check_instance_summary(Path(folder))
