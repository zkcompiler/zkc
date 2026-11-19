"""Check the source exporter, its issued theorem, and independently falsifiable controls."""

import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[3]
COMPILER = ROOT / "lean/compiler/.lake/build/bin/zkc-knowledge"
SOURCE = ROOT / "examples/schnorr.zkc"
ENTRY = ROOT / "examples/schnorr_example.zkc"
CHAUM_PEDERSEN = ROOT / "examples/chaum_pedersen.zkc"
CONTROL = Path(__file__).with_name("WrittenKnowledgeControls.lean.in")
CONSUMER = Path(__file__).with_name("AdmittedConsumer.lean.in")
AUDIT = Path(__file__).with_name("AuditWritten.lean")


def run(command, *, failure=None, cwd=None):
    result = subprocess.run(command, text=True, capture_output=True, cwd=cwd)
    output = result.stdout + result.stderr
    if failure is None:
        if result.returncode or "declaration uses `sorry`" in output or "sorryAx" in output:
            raise RuntimeError(f"{command}\n{result.stdout}{result.stderr}")
    elif result.returncode == 0 or failure not in output:
        raise RuntimeError(f"expected {failure!r} from {command}\n{result.stdout}{result.stderr}")
    return output


def check_axioms(theorem, report):
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if f"'{theorem}' does not depend on any axioms" in report:
        return
    found = re.search(rf"'{re.escape(theorem)}' depends on axioms: \[([^\]]*)\]", report)
    if not found:
        raise RuntimeError(f"missing kernel axiom report for {theorem}")
    used = {name.strip() for name in found[1].split(",") if name.strip()}
    if used - allowed:
        raise RuntimeError(f"unexpected axioms for {theorem}: {sorted(used - allowed)}")


def replace_once(text, original, replacement):
    if text.count(original) != 1:
        raise ValueError(f"expected exactly one source occurrence of {original!r}")
    return text.replace(original, replacement)


def check(work):
    names = ["Baseline", "Renamed", "Zero", "OtherRelation", "OtherVerifier", "Simulator", "Swapped",
             "SameLog", "Reordered", "MissingGuard", "ScalarGuard", "NativeOnly", "ProjectedGuards", "RunLength"]
    formal = ROOT / "lean/formal"
    (work / "lean-toolchain").write_text((formal / "lean-toolchain").read_text())
    (work / "lakefile.toml").write_text(
        'name = "written_controls"\n'
        '[[require]]\nname = "zkc_formal"\n' + f'path = {json.dumps(str(formal))}\n'
        '[[lean_lib]]\nname = "Variants"\n' + f'roots = {json.dumps(names)}\n'
    )
    entry = work / ENTRY.name
    entry.write_text(ENTRY.read_text())
    original = SOURCE.read_text()
    input_file = work / SOURCE.name

    def generate(source, proof=True, failure=None, *, same_log=False, namespace=None, scheme=None):
        selected_entry = work / CHAUM_PEDERSEN.name if same_log else entry
        selected_input = selected_entry if same_log else input_file
        selected_input.write_text(source)
        flags = [] if proof else ["--target-only"]
        if namespace:
            flags.extend(["--namespace", namespace])
        return run([COMPILER, *flags, selected_entry, ROOT, scheme or ("SameLogProof" if same_log else "Proof")],
                   failure=failure)

    def module(name, source, proof=False, *, same_log=False):
        generated = generate(source, proof, same_log=same_log, namespace=name)
        path = work / f"{name}.lean"
        path.write_text(generated)
        return generated

    base = module("Baseline", original, proof=True)
    for name in ["DLog", "response_difference", "commitment", "challenge", "response"]:
        if f'("{name}",' not in base:
            raise RuntimeError(f"missing source provenance for {name}")

    renamed = replace_once(original, "    response <- send", "    #[site(response)]\n    local_response <- send")
    renamed = replace_once(renamed, "@V base * response ==", "@V base * local_response ==")
    module("Renamed", renamed)

    clause = "knowledge DLog(base, point) by response_difference"
    swapped = replace_once(original, clause, "knowledge DLog(point, base) by response_difference")
    swapped = replace_once(swapped, "    guard gap != 0", "    guard point == base * 0\n    guard gap != 0")
    module("Swapped", swapped)
    zero = replace_once(original, "spec for Schnorr:", """pub def zero_result<G: PrimeOrderGroup>(
    base: G, point: G, runs: Schnorr<G>::Runs<2>
) -> G::Scalar:
    return 0

spec for Schnorr:""")
    zero = replace_once(zero, clause, "knowledge DLog(base, point) by zero_result")
    zero_text = module("Zero", zero)
    if '("zero_result",' not in zero_text:
        raise RuntimeError("the clause did not select its replacement extractor")

    module("OtherRelation", replace_once(original, "    point == base * scalar", "    point != base * scalar"))
    other_verifier = replace_once(original, "guard @V base * response == commitment + point * challenge",
                                  "guard @V base * response == base * response")
    module("OtherVerifier", other_verifier)
    module("Simulator", replace_once(original, "inputs.base * response - inputs.point * coins.challenge",
                                    "inputs.point * response - inputs.base * coins.challenge"))

    same_log = CHAUM_PEDERSEN.read_text()
    same_log_module = module("SameLog", same_log, proof=True, same_log=True)
    second_guard = "        guard @V h * z == b + v * c\n"
    first_guard = "        guard @V g * z == a + u * c\n"
    reordered = replace_once(same_log, first_guard + second_guard, second_guard + first_guard)
    module("Reordered", reordered, proof=True, same_log=True)
    missing = replace_once(same_log, second_guard, "")
    module("MissingGuard", missing, same_log=True)
    scalar_guard = replace_once(same_log, second_guard, second_guard + "        guard @V z == c\n")
    module("ScalarGuard", scalar_guard, proof=True, same_log=True)

    projected = replace_once(same_log, first_guard, "        guard @P x == x\n        guard @(P, V) c == c\n" + first_guard)
    projected = replace_once(projected, "        #[site(commitment)]\n", "")
    projected = replace_once(projected, "    construction derived", "    prover P\n    construction derived")
    projected = replace_once(projected, "        proves SameLog", "        proves @V SameLog")
    proof = module("ProjectedGuards", projected, proof=True, same_log=True)
    if '("site1",' not in proof:
        raise RuntimeError("the generated Run lost its unnamed commitment")
    sized = replace_once(same_log, "        difference =", "        n = length(runs)\n        difference =")
    module("RunLength", sized, same_log=True)

    native_only = replace_once(original, "return (runs[0].response - runs[1].response) / gap",
                               "return runs[0].response + runs[1].response")
    native_target = module("NativeOnly", native_only)
    if "def compiledObligation" not in native_target or "def extractor {" in native_target:
        raise RuntimeError("native-only target must use the ordinary function meaning")
    generate(native_only, failure="WK-PROOF")

    controls = work / "Checks.lean"
    imports = [f"public import {name}" for name in [*names, "Zkc.Formal.Written.FiniteModel"]]
    def consumer(name):
        return replace_once(CONSUMER.read_text(), "CERTIFICATE_NAMESPACE", name)

    controls.write_text("\n".join(["module", "", *imports, "", CONTROL.read_text(),
                                   consumer("Baseline"), consumer("SameLog")]))
    report = run(["lake", "-q", "lean", controls], cwd=work)
    for theorem in ["Baseline.certified_core_admitted", "SameLog.certified_core_admitted",
                    "Reordered.certified_core_admitted", "ScalarGuard.certified_core_admitted",
                    "WrittenControls.missing_compiled_guard", "WrittenControls.compiled_wrong_extractor",
                    "WrittenControls.compiled_wrong_relation",
                    "WrittenControls.missing_guard_admitted", "WrittenControls.permitted_counterexample",
                    "WrittenControls.wrong_extractor", "WrittenControls.wrong_relation",
                    "WrittenControls.wrong_verifier"]:
        check_axioms(theorem, report)
    print(run(["lake", "env", "lean", "--run", AUDIT], cwd=work), end="", flush=True)
    print("Checked both admitted certificates, permitted forks, and four source counterexamples.", flush=True)

    failed = work / "Rejected.lean"
    for name, issued in [("Baseline", base), ("SameLog", same_log_module)]:
        weakened = issued.split("theorem certified_core_admitted {", 1)[0]
        weakened = replace_once(weakened, "public import Zkc.Formal.Written.GroupReplay",
                                "public import Zkc.Formal.Written.GroupReplay\npublic import Zkc.Formal.Written.FiniteModel")
        weakened += f"theorem certified_core_admitted : True := trivial\nend «{name}»\n"
        failed.write_text(weakened + consumer(name))
        run(["lake", "-q", "lean", failed], failure="Function expected", cwd=work)
    # Keep all three emitted programs fixed and corrupt only the auxiliary calculation.
    # Check the correspondence on its own, before attempting the security theorem.
    prefix = base.split("theorem certified (", 1)[0]
    damaged = replace_once(prefix, "return (← divide ops (ops.sub left.suffix right.suffix) local0)",
                           "return ops.zero")
    failed.write_text(damaged + "\nend Baseline\n")
    run(["lake", "-q", "lean", failed], failure="WK-PROOF", cwd=work)
    for changed, is_same_log in [(zero, False), (other_verifier, False), (missing, True)]:
        generated = generate(changed, same_log=is_same_log)
        correspondences = generated.split("theorem certified (", 1)[0]
        failed.write_text(correspondences + "\nend WrittenKnowledge\n")
        run(["lake", "-q", "lean", failed], cwd=work)
        failed.write_text(generated)
        diagnostic = run(["lake", "-q", "lean", failed], failure="WK-PROOF", cwd=work)
        if str(work / CHAUM_PEDERSEN.name if is_same_log else input_file) not in diagnostic:
            raise RuntimeError("residual proof failure did not identify the source module")
    for source, diagnostic in [
        (replace_once(original, "Schnorr<G>::Runs<2>", "Schnorr<G>::Runs<3>"), "WK-VIEW"),
        (replace_once(original, "    nonce @P <- sample G::Scalar",
                      "    secret_coin @V <- sample G::Scalar\n    nonce @P <- sample G::Scalar"), "WK-VIEW"),
        (replace_once(original, "pub def response_difference", "pub spec def response_difference"), "WK-TYPE"),
        (replace_once(original, "spec for Schnorr:", "spec for response_difference:\n    requires false\n\nspec for Schnorr:"), "WK-CLAUSE"),
        (replace_once(original, "runs[0].challenge", "runs[2].challenge"), "TY7"),
        (replace_once(original, clause, clause + "\n    " + clause), "WK-CLAUSE"),
        (replace_once(original, "    response <- send", "    #[site(challenge)]\n    response <- send"), "EV3"),
    ]:
        generate(source, proof=False, failure=diagnostic)
    def reject_in_both(source, diagnostic, **selection):
        for proof_mode in (False, True):
            generate(source, proof_mode, failure=diagnostic, **selection)

    specialized = replace_once(same_log, "{Fr, G1}", "{Fr, G1, G2}\nuse chaum_pedersen::ChaumPedersen<G2> as Alternate")
    specialized = replace_once(specialized, "runs: ChaumPedersen::Runs", "runs: Alternate::Runs")
    line, column = next((i, text.index("Alternate::Runs<2>") + 1)
                        for i, text in enumerate(specialized.splitlines(), 1) if "Alternate::Runs<2>" in text)
    type_span = f"{line}:{column}-{line}:{column + len('Alternate::Runs<2>')}"
    reject_in_both(specialized, f"{type_span}: WK-VIEW: different protocol specialization", same_log=True)
    generate(replace_once(specialized, "ChaumPedersen<G2> as Alternate", "ChaumPedersen<G1> as Alternate"), same_log=True)
    for source, diagnostic in [
        (replace_once(same_log, "    protocol ChaumPedersen", "    spec protocol ChaumPedersen"), "WK-ROOT"),
        (replace_once(same_log, "    construction derived", "    prover V\n    construction derived"), "SC3"),
        (replace_once(same_log, "    construction derived", "    prover P\n    prover P\n    construction derived"), "SC3"),
        (replace_once(same_log, "    construction derived", "    ideal V\n    construction derived"), "WK-VIEW"),
        (replace_once(same_log, "    construction derived", "    offline P\n    construction derived"), "WK-VIEW"),
        (replace_once(same_log, "construction derived(HashChain<Keccak256, Fr>)", "construction interactive"), "SC3"),
        (replace_once(same_log, "        proves SameLog", "        proves @P SameLog"), "SX6"),
        (replace_once(same_log, "        knowledge SameLog", "    spec for ChaumPedersen:\n        knowledge SameLog"), "WK-CLAUSE"),
        (replace_once(same_log, "runs[0].c", "runs[0].1"), "TY7"),
        (replace_once(same_log, "runs[0].c", "runs[0][1]"), "NL6"),
        (replace_once(same_log, "runs[0].c", "runs.0.c"), "TY7"),
        (replace_once(same_log, "        r @P <- sample G::Scalar", "        r @P <- sample G::Scalar\n        #[site(second)]\n        r @P <- sample G::Scalar"), "NL2"),
        (replace_once(projected, "        c <- draw", "        #[site(site1)]\n        c <- draw"), "WK-VIEW"),
    ]:
        reject_in_both(source, diagnostic, same_log=True)
    reject_in_both(original, "WK-PORT", scheme="Signature")
    reject_in_both(original, "WK-NAMESPACE", namespace="Broken.name")
    entry.write_text(ENTRY.read_text() + "\nspec for Schnorr:\n    requires false\n")
    reject_in_both(original, "WK-CLAUSE")
    library_scheme = replace_once(original, "module schnorr\n", "module schnorr\nuse zkc::curves::bls12_381::{G1}\n")
    library_scheme += "\nscheme Proof = Schnorr<G1>:\n    construction interactive\n    prover P\n"
    entry.write_text(ENTRY.read_text())
    generate(library_scheme)
    entry.write_text("module schnorr_example\nuse schnorr::{Schnorr}\n")
    reject_in_both(library_scheme, "WK-ROOT")
    print("Rejected false certificates, incompatible views, duplicate clauses and duplicate sites.", flush=True)


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="zkc-written-") as directory:
        check(Path(directory))
