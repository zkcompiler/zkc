"""The formalization drift driver.

Every formalization receipt in the signature records a declaration's printed
type and its axiom profile at a pinned revision. Both are obtainable from a
proof assistant without proving anything, and both are strings, so a later
reading can be compared against the recorded one instead of re-judged. That is
the whole mechanism: a receipt that cannot detect that its subject moved is a
bookmark, not a link.

This file is the driver. It reads the signature and emits, per receipt, the
commands that reproduce what was recorded. Running them needs a Lean toolchain
and a checkout, which is deliberately outside this repository's build: a proof
assistant does not belong in a compiler's build path, and a formal result is
never a runtime input (`docs/spec/soundness.md` §5.4).

Without a checkout it still does useful work, and that is what the test suite
exercises: every receipt must be well formed, must name a repository and a
revision it can be checked against, and must agree with itself about whether an
axiom was admitted.
"""

import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
PIN = json.loads(
    (REPO / "registry" / "upstreams.json").read_text()
)["upstreams"]["arklib"]["revision"]
ARKLIB = "https://github.com/Verified-zkEVM/ArkLib"

problems = []
checkable = []
checkable_receipts = []
unpinned = []


def receipts(signature):
    for declaration_id, annotation in sorted(signature["annotations"].items()):
        for index, receipt in enumerate(annotation.get("formalization", [])):
            yield declaration_id, index, receipt


signature = json.load(open(sys.argv[1]))

for declaration_id, index, receipt in receipts(signature):
    where = f"{declaration_id}[{index}]"
    name = receipt.get("declaration", "")
    if not name:
        problems.append(f"{where}: names no declaration")
        continue

    # An empty axiom list is the claim that none were admitted. The three
    # states and the profile are two spellings of one fact and may not
    # disagree; the loader refuses that, and this file refuses it again from
    # the outside, because a receipt is read by people who do not run the
    # loader.
    admits_hole = "sorryAx" in receipt.get("axioms", [])
    mechanized = receipt.get("state") == "mechanized"
    if mechanized == admits_hole:
        problems.append(
            f"{where}: recorded as {receipt.get('state')} but its axiom profile "
            f"{'admits' if admits_hole else 'does not admit'} a hole"
        )

    if not receipt.get("covers"):
        problems.append(f"{where}: says nothing about what it covers")

    # A receipt that records no type cannot be compared against a later
    # reading. That is allowed -- a citation to a non-Lean mechanization has no
    # printed type to record -- but it is not checkable, and saying so is the
    # point.
    if receipt.get("repository") == ARKLIB:
        if receipt.get("revision") != PIN:
            problems.append(
                f"{where}: pinned at {receipt.get('revision') or '(none)'}, "
                f"but registry/upstreams.json records {PIN}"
            )
        elif not receipt.get("statement"):
            unpinned.append(f"{where}: {name} — no recorded type to compare")
        else:
            checkable.append((where, name))
            checkable_receipts.append((where, receipt))
    else:
        unpinned.append(
            f"{where}: {name} — {receipt.get('repository') or 'no repository'}, "
            "outside the pinned checkout"
        )

if problems:
    raise SystemExit("receipt defects:\n  " + "\n  ".join(problems))

print(f"formalization receipts: {len(checkable)} checkable, {len(unpinned)} not")
for line in unpinned:
    print(f"  not checkable: {line}")

if not checkable:
    raise SystemExit(0)

if "--checkout" not in sys.argv:
    print(f"\nto check against {ARKLIB} at {PIN}, in a Lean environment:")
    for where, name in checkable:
        print(f"  -- {where}")
        print(f"  #check @{name}")
        print(f"  #print axioms {name}")
    raise SystemExit(0)


# --checkout <path>: run the commands instead of printing them.
#
# This needs a Lean toolchain and a built checkout, which is why it is not the
# default and never runs in the compiler's build. What it does is the whole
# reason the receipt records a type and an axiom profile: both are strings a
# later reading reproduces, so drift is a diff rather than a re-judgement.
import re
import subprocess
import tempfile

checkout = Path(sys.argv[sys.argv.index("--checkout") + 1]).resolve()
head = subprocess.run(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                      capture_output=True, text=True).stdout.strip()
if head != PIN:
    raise SystemExit(f"checkout is at {head or '(unknown)'}, not the pin {PIN}")

imports = sorted({
    "ArkLib." + ".".join(name.split(".")[:-1])
    for _, name in checkable
})
# A declaration's module is not derivable from its name -- the sumcheck reading
# of 2026-07-26 found exactly that -- so every module that declares one of the
# cited names is imported and Lean resolves the name itself.
modules = []
for path in sorted((checkout / "ArkLib").rglob("*.lean")):
    text = path.read_text(encoding="utf-8", errors="replace")
    for _, name in checkable:
        if re.search(rf"\b{re.escape(name.split('.')[-1])}\b", text):
            module = str(path.relative_to(checkout)).removesuffix(".lean")
            modules.append(module.replace("/", "."))
            break

modules = sorted(set(modules))
# An import of an unbuilt module fails the whole file, so every discovered
# module is built first. The cost is paid once per checkout.
build = subprocess.run(["lake", "build", *modules], cwd=checkout,
                       capture_output=True, text=True)
if build.returncode != 0:
    raise SystemExit("lake build failed:\n" + (build.stderr or build.stdout)[-2000:])

source = "\n".join(f"import {m}" for m in modules) + "\n\n"
for _, name in checkable:
    source += f"#check @{name}\n#print axioms {name}\n"


# Recorded statements are the printed type, whitespace-collapsed and
# transliterated into the printable-ASCII encoding domain (a registry string
# cannot carry the raw glyphs). This table is the one place that mapping
# lives; the recorded form must reproduce from the checkout through it.
ASCII_GLYPHS = {
    "∀": "forall", "→": "->", "ℕ": "Nat", "≥": ">=", "≤": "<=", "×": "x",
    "Σ": "Sigma", "σ": "sigma", "ι": "iota", "ₛ": "_s", "ₘ": "_m",
    "∈": "in", "↪": "embeds-into", "₁": "_1", "₂": "_2", "⟶": "->",
    "↑": "lift ", "ε": "eps", "𝔽": "F", "·": "*", "⊕": "oplus",
    "∑": "sum", "∏": "prod", "λ": "fun", "⦃": "{{", "⦄": "}}",
}


def normalize_statement(text: str) -> str:
    # Whitespace first (newlines are layout, not glyphs), then the mapping.
    text = re.sub(r"\s+", " ", text).strip()
    mapped = []
    for character in text:
        if 0x20 <= ord(character) <= 0x7E:
            mapped.append(character)
        elif character in ASCII_GLYPHS:
            mapped.append(ASCII_GLYPHS[character])
        else:
            mapped.append("#u" + format(ord(character), "04x") + "#")
    return "".join(mapped)


def printed_statements(text: str) -> dict:
    """Parse the `@Name : <type>` blocks out of the probe output."""
    statements = {}
    starts = [(m.start(), m.group(1))
              for m in re.finditer(r"^@?([\w.]+) : ", text, re.M)]
    for position, (offset, name) in enumerate(starts):
        end = (starts[position + 1][0]
               if position + 1 < len(starts) else len(text))
        block = re.split(r"\n'", text[offset:end])[0]
        block = re.sub(r"^@", "", block)
        statements[name] = normalize_statement("@" + block)
    return statements

drift = []
with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=checkout,
                                 delete=False) as handle:
    handle.write(source)
    probe = Path(handle.name)
try:
    run = subprocess.run(["lake", "env", "lean", probe.name], cwd=checkout,
                         capture_output=True, text=True)
finally:
    probe.unlink(missing_ok=True)

output = run.stdout + run.stderr
fatal = [line for line in output.splitlines()
         if "error" in line and "unknownIdentifier" not in line
         and "unknownConstant" not in line]
if fatal:
    raise SystemExit("the reading did not run:\n  " + "\n  ".join(fatal[:8]))
printed = printed_statements(output)
print(f"\nread against {ARKLIB} at {PIN}:")
for (where, name), receipt in zip(checkable, [r for _, r in checkable_receipts]):
    resolved = re.search(rf"^'{re.escape(name)}' depends on axioms: \[(.*)\]$",
                         output, re.M)
    if not resolved:
        drift.append(f"{where}: {name} does not resolve at the pin")
        print(f"  {where}: {name} -- DOES NOT RESOLVE")
        continue
    read = {axiom.strip() for axiom in resolved.group(1).split(",") if axiom.strip()}
    recorded = set(receipt.get("axioms", []))
    # Compared as a set: Lean prints them in elaboration order, which is not a
    # property of the declaration.
    if read != recorded:
        drift.append(f"{where}: axioms {sorted(read)}, recorded {sorted(recorded)}")
        print(f"  {where}: {name} -- AXIOMS DIFFER")
        print(f"      read     {sorted(read)}")
        print(f"      recorded {sorted(recorded)}")
        continue
    # The statement is compared too, in the normalized form above: a receipt
    # whose recorded type is not what the checkout prints is citing
    # something else. An empty recorded statement is skipped — receipts for
    # repositories outside the pin record none.
    recorded_statement = receipt.get("statement", "")
    if recorded_statement:
        printed_statement = printed.get(name)
        if printed_statement is None:
            drift.append(f"{where}: no printed type parsed for {name}")
            print(f"  {where}: {name} -- NO PRINTED TYPE PARSED")
            continue
        if recorded_statement != printed_statement:
            drift.append(f"{where}: recorded statement differs from the "
                         f"printed type")
            print(f"  {where}: {name} -- STATEMENT DIFFERS")
            print(f"      printed  {printed_statement[:120]}...")
            print(f"      recorded {recorded_statement[:120]}...")
            continue
    print(f"  {where}: {name} -- axioms and statement agree {sorted(read)}")

if drift:
    raise SystemExit("formalization drift:\n  " + "\n  ".join(drift))
print(f"\n{len(checkable)} receipt(s) agree with the pinned checkout")
