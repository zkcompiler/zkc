"""Positive and mutation controls for the retained theorem ledger and document checks."""

from pathlib import Path
import tempfile

from . import ledger
from .declarations import Records
from support.packages import PACKAGES, module_path


def record(name, *, kind="theorem", axioms=("propext",), premises=(), detail=None, hashes=("1", "2"),
           module=None):
    value = {"name": name, "module": module or name.rsplit(".", 1)[0], "kind": kind,
             "statement": {"structural": hashes[0], "explicit": hashes[1]},
             "axioms": list(axioms), "doc": None, "tags": [], "package": "sample"}
    if premises:
        value["premises"] = list(premises)
    if detail is not None:
        value["detail"] = detail
    return value


def run_ledger_controls(rows, expect):
    # The ledger: a renamed headline, a changed statement and a theorem that
    # depends on sorryAx each fail; the unchanged ledger passes.
    claims = {"schema": ledger.LEDGER_SCHEMA, "proved": [
        {"subject": "Sample", "result": "A result", "owners": [["Spec", "docs/spec.md"]],
         "theorems": ["Sample.headline"]}]}
    current = Records({"sample": {"format": "zkc.declarations/0"}}, [record("Sample.headline")])
    lock = ledger.write_lock(claims, {}, current)
    findings, _, _ = ledger.check(claims, lock, current)
    expect("ledger-current", findings == [], findings)
    renamed = Records({"sample": {"format": "zkc.declarations/0"}}, [record("Sample.headline_renamed")])
    findings, _, _ = ledger.check(claims, lock, renamed)
    expect("ledger-renamed-headline", any(f.startswith("stale theorem name") for f in findings), findings)
    changed = Records({"sample": {}}, [record("Sample.headline", hashes=("1", "3"))])
    findings, _, _ = ledger.check(claims, lock, changed)
    expect("ledger-changed-statement", any(f.startswith("statement changed") for f in findings), findings)
    sorry = Records({"sample": {}}, [record("Sample.headline", axioms=("sorryAx",))])
    findings, _, _ = ledger.check(claims, lock, sorry)
    expect("ledger-sorry-unresolved", any(f.startswith("unresolved") for f in findings), findings)
    table = ledger.render_proved(claims)
    document = f"text\n{ledger.begin('what-is-proved')}\n{table}{ledger.end('what-is-proved')}\n"
    expect("region-current", ledger.region(document, "what-is-proved") == table)
    stale = document.replace("A result", "An older result")
    expect("region-stale", ledger.region(stale, "what-is-proved") != table)
    # A qualified name cited in prose must still name a declaration.
    with tempfile.TemporaryDirectory(prefix="zkc-records-documents-") as temporary:
        root = Path(temporary)
        (root / "docs").mkdir()
        (root / "docs/status.md").write_text("Cites `Zkc.Sample.present` and `Zkc.Sample.renamed`.\n")
        for package, (_, roots) in PACKAGES.items():
            path = module_path(roots[0] + '.Fixture', root / 'lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('namespace Zkc.Sample\nend Zkc.Sample\n' if package == 'ir'
                            else 'namespace Fixture\nend Fixture\n')
        cited = Records({"ir": {}}, [dict(record("Zkc.Sample.present"), package="ir")])
        findings, checked, _ = ledger.check_documents(cited, root)
        expect("document-stale-name", checked == 2 and len(findings) == 1 and "Zkc.Sample.renamed" in findings[0],
               findings)
    return rows



def run():
    rows = []

    def expect(name, passed, detail=None):
        rows.append({"name": name, "status": "pass" if passed else "fail", "detail": detail})

    run_ledger_controls(rows, expect)
    return rows
