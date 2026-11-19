"""Check the source exporter, its issued theorem, and independently falsifiable controls."""

import json
import os
from pathlib import Path
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


def run(command, *, failure=None, cwd=None, env=None):
    result = subprocess.run(command, text=True, capture_output=True, cwd=cwd, env=env)
    output = result.stdout + result.stderr
    if failure is None:
        if result.returncode or "declaration uses `sorry`" in output or "sorryAx" in output:
            raise RuntimeError(f"{command}\n{result.stdout}{result.stderr}")
    elif result.returncode == 0 or failure not in output:
        raise RuntimeError(f"expected {failure!r} from {command}\n{result.stdout}{result.stderr}")
    return output


def replace_once(text, original, replacement):
    if text.count(original) != 1:
        raise ValueError(f"expected exactly one source occurrence of {original!r}")
    return text.replace(original, replacement)


def source_consumer(name, fixture):
    """Independent expectations for the two fixed source files and their three public roots."""
    if fixture == "Baseline":
        fields = ["s.src_base", "s.src_point"]
        history, history_ty = "Bool", "pointTy"
        addresses = "⟨2⟩ ⟨3⟩ ⟨6⟩"
    elif fixture in ("SameLog", "RolesReversed"):
        fields = ["s.src_g", "s.src_h", "s.src_u", "s.src_v"]
        history = "Bool × Bool × Unit"
        history_ty = "(.tuple (.cons pointTy (.cons pointTy .nil)))"
        addresses = "⟨4⟩ ⟨6⟩ ⟨9⟩"
    else:
        raise ValueError(f"unknown source fixture {fixture!r}")

    def inputs(last):
        result = f"(.cons {last} .nil)"
        for field in reversed(fields):
            result = f"(.cons {field} {result})"
        return result

    values = {
        "CERTIFICATE_NAMESPACE": name,
        "SOURCE_HISTORY_TY": history_ty,
        "SOURCE_HISTORY": history,
        "SOURCE_ADDRESSES": addresses,
        "SOURCE_PROVER": "1" if fixture == "RolesReversed" else "0",
        "SOURCE_VERIFIER": "0" if fixture == "RolesReversed" else "1",
        "SOURCE_INPUTS": inputs("()"),
        "SOURCE_RELATION": inputs("w"),
        "SOURCE_EXTRACTOR": inputs("[(a,l.challenge,l.suffix,()),(a,r.challenge,r.suffix,())]"),
    }
    consumer = CONSUMER.read_text()
    for key, value in values.items():
        consumer = consumer.replace(key, value)
    return consumer


def check(work):
    names = ["Baseline", "SharedReplay", "Factored", "FactoredCompanion", "ReversedGap", "CalledSameLog", "Renamed", "Zero", "OtherRelation", "OtherVerifier", "Simulator", "Swapped",
             "SameLog", "RolesReversed", "Reordered", "MissingGuard", "ScalarGuard", "NativeOnly", "ProjectedGuards", "RunLength", "Context", "Named", "NamedArguments", "ReversedNumerator", "PrivateControl"]
    formal = ROOT / "lean/formal"
    (work / "lean-toolchain").write_text((formal / "lean-toolchain").read_text())
    (work / "lakefile.toml").write_text(
        'name = "written_controls"\n'
        f'packagesDir = {json.dumps(str(formal / ".lake/packages"))}\n'
        '[[require]]\nname = "zkc_formal"\n' + f'path = {json.dumps(str(formal))}\n'
        '[[lean_lib]]\nname = "Variants"\n' + f'roots = {json.dumps([*names, "AuditLocal", "AuditVendor", "Checks", "OddFork"])}\n'
    )
    # Reuse the formal package's resolved and built pins in this generated client.
    run(["lake", "-q", "update"], cwd=work, env={**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"})
    entry = work / ENTRY.name
    entry.write_text(ENTRY.read_text())
    original = SOURCE.read_text()
    input_file = work / SOURCE.name

    def generate(source, proof=True, failure=None, *, same_log=False, namespace=None, scheme=None, goal=None, clause=None):
        selected_entry = work / CHAUM_PEDERSEN.name if same_log else entry
        selected_input = selected_entry if same_log else input_file
        selected_input.write_text(source)
        flags = [] if proof else ["--target-only"]
        if namespace:
            flags.extend(["--namespace", namespace])
        if goal:
            flags.extend(["--goal", goal])
        if clause:
            flags.extend(["--clause", clause])
        subject = [] if goal else [scheme or ("SameLogProof" if same_log else "Proof")]
        return run([COMPILER, *flags, selected_entry, ROOT, *subject], failure=failure)

    def module(name, source, proof=False, *, same_log=False):
        generated = generate(source, proof, same_log=same_log, namespace=name)
        path = work / f"{name}.lean"
        path.write_text(generated)
        return generated

    base = module("Baseline", original, proof=True)
    for name in ["DLog", "response_difference", "commitment", "challenge", "response"]:
        if f'("{name}",' not in base:
            raise RuntimeError(f"missing source provenance for {name}")

    helpers = """def subtract_scalars<F: Field>(x: F, y: F) -> F:
    x - y

def gap_of<F: Field>(left: F, right: F) -> F:
    subtract_scalars<F>(left, right)

"""
    factored = replace_once(original, "pub def response_difference", helpers + "pub def response_difference")
    factored = replace_once(factored, "runs[0].challenge - runs[1].challenge",
                            "gap_of<G::Scalar>(runs[0].challenge, runs[1].challenge)")
    (work / "Factored.lean").write_text(generate(factored, proof=False, namespace="Factored", goal="fork"))
    generate(factored, goal="fork", failure="WK-PROOF")
    (work / "FactoredCompanion.lean").write_text(Path(__file__).with_name("FactoredCompanion.lean.in").read_text())
    module("ReversedGap", replace_once(factored, "    x - y", "    y - x"))

    # Each verifier instruction uses the preceding SSA result twice. Compile the
    # actual returning-fork theorem through a chain long enough to expose inlining.
    previous = "base"
    doubled = []
    for index in range(12):
        result = f"doubled_{index}"
        doubled.append(f"    {result} @V = {previous} + {previous}")
        previous = result
    guard = "    guard @V base * response == commitment + point * challenge"
    module("SharedReplay", replace_once(original, guard, "\n".join([*doubled, guard])), proof=True)

    # A prover-only choice and a sampled loop are present in the admitted source.
    # Neither changes the verifier's run or its deciding role for the selected fork.
    private_control = replace_once(original, "    nonce @P <- sample", """    if scalar == 0:
        guard @P scalar == scalar
    for i in 0..2:
        salt @P <- sample G::Scalar
    nonce @P <- sample""")
    private_control = replace_once(private_control, "    proves DLog",
                                "    proves @P local_check: scalar == scalar\n    proves DLog")
    module("PrivateControl", private_control, proof=True)
    generate(replace_once(private_control, "proves @P local_check", "proves @V local_check"), failure="SX6")
    generate(replace_once(private_control, "proves @P local_check: scalar == scalar",
                          "proves local_check: base == base"), failure="SX6")
    generate(replace_once(original, "    nonce @P <- sample", """    for i in 0..2:
        guard @V base == base
    nonce @P <- sample"""), proof=False, failure="unsupported verifier control flow")

    # The library declaration remains the data projection through a renamed import.
    handles = replace_once(original, "module schnorr", """module schnorr
use zkc::oracle::data as contents
use zkc::oracle::{Kind}""") + """
protocol Probe<K: Kind> roles(P, V)(h: Oracle<K> @P -> V):
    guard @P true
spec for Probe:
    proves @V contents(h) == contents(h)
"""
    generate(handles, proof=False)
    generate(replace_once(handles, "proves @V contents", "proves @P contents"), proof=False, failure="SX6")

    renamed = replace_once(original, "    response <- send", "    #[site(response)]\n    local_response <- send")
    renamed = replace_once(renamed, "@V base * response ==", "@V base * local_response ==")
    module("Renamed", renamed)

    clause = "knowledge DLog(base, point) by response_difference"
    named_args = replace_once(original, clause, "knowledge DLog(point = point, base = base) by response_difference")
    module("NamedArguments", named_args, proof=True)
    for args in ("base = base, base = point", "point = point, missing = base"):
        generate(replace_once(original, clause, f"knowledge DLog({args}) by response_difference"), failure="FN6")
    generate(replace_once(original, clause, clause + '\n    knowledge DLog(base = base, base = point) by external("other")'), failure="FN6")
    swapped = replace_once(original, clause, "knowledge DLog(point, base) by response_difference")
    swapped = replace_once(swapped, "    guard gap != 0", "    guard point == base * 0\n    guard gap != 0")
    module("Swapped", swapped)
    zero = replace_once(original, "spec for Schnorr:", """pub def zero_result<G: PrimeOrderGroup>(
    base: G, point: G, runs: Schnorr<G>::Runs<2>
) -> G::Scalar:
    return 0

spec for Schnorr:""")
    zero = replace_once(zero, clause, "knowledge DLog(base, point) by zero_result")
    reversed_numerator = replace_once(original, "runs[0].response - runs[1].response",
                                      "runs[1].response - runs[0].response")
    module("ReversedNumerator", reversed_numerator)
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
    called = replace_once(same_log, "section <G: PrimeOrderGroup>:", """enum Flag:
    Active(bool)
    Inactive

def same_boolean(value: bool) -> bool:
    mut result = false
    flag = Flag::Active(value)
    match flag:
        case Flag::Active(b):
            for _ in 0..2:
                result := b
        case Flag::Inactive:
            result := false
    return result

section <G: PrimeOrderGroup>:""")
    called = replace_once(called, "    relation SameLog", """    def scaled(base: G, x: G::Scalar) -> G:
        base * x

    def same_point(left: G, right: G) -> bool:
        same_boolean(left == right)

    relation SameLog""")
    called = replace_once(called, "u == g * x and v == h * x",
                          "same_point(u, scaled(g, x)) and same_point(v, scaled(h, x))")
    called = replace_once(called, "guard @V g * z == a", "guard @V scaled(g, z) == a")
    module("CalledSameLog", called, same_log=True)
    roles_reversed = replace_once(same_log, "roles(P, V)", "roles(V, P)")
    roles_reversed = replace_once(roles_reversed, "    construction derived", "    prover P\n    construction derived")
    module("RolesReversed", roles_reversed, proof=True, same_log=True)
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

    (work / "Context.lean").write_text(generate(original, namespace="Context", scheme="Signature"))
    first = "knowledge first: DLog(base, point) by zero_result"
    second = "knowledge second: ((DLog(base, point))) by response_difference"
    labelled = replace_once(zero, clause.replace("response_difference", "zero_result"), first + "\n    " + second)
    goals = "\ngoal chosen = special_soundness(Proof, stage = written, clause = second)\n"
    entry.write_text(ENTRY.read_text() + goals)
    (work / "Named.lean").write_text(generate(labelled, namespace="Named", goal="chosen"))
    selected_first = generate(labelled, proof=False, clause="first")
    if '("zero_result",' not in selected_first:
        raise RuntimeError("first label failed to select the distinct extractor")
    generate(labelled, proof=False, failure="WK-CLAUSE")
    generate(labelled, proof=False, clause="absent", failure="WK-CLAUSE")
    for old, new in [("stage = written", "stage = derived"), ("special_soundness(Proof", "knowledge_soundness(Proof")]:
        entry.write_text(ENTRY.read_text() + goals.replace(old, new))
        generate(labelled, proof=False, goal="chosen", failure="WK-GOAL")
    entry.write_text(ENTRY.read_text())

    entry.write_text(ENTRY.read_text() + """
module secondary:
    scheme Proof = Schnorr<G1>:
        construction interactive
        prover P
    goal fork = special_soundness(Proof, stage = written)
""")
    for selector in ("scheme", "goal"):
        short = "Proof" if selector == "scheme" else "fork"
        outer = f"schnorr_example::{short}"
        inner = f"schnorr_example::secondary::{short}"
        ambiguous = generate(original, proof=False, failure=f"ambiguous {short}", **{selector: short})
        if outer not in ambiguous or inner not in ambiguous:
            raise RuntimeError(f"missing qualified choices for {short}")
        for query, expected in [(outer, outer), (inner, inner), (f"secondary::{short}", inner)]:
            rendered = generate(original, proof=False, **{selector: query})
            field = f'selectedSchemePath : String := "{expected}"' if selector == "scheme" else (
                f'selectedGoalPath : Option String := (some "{expected}")')
            if field not in rendered:
                raise RuntimeError(f"{query} selected the wrong declaration")
            scheme_path = expected.rsplit("::", 1)[0] + "::Proof"
            if selector == "goal" and f'selectedSchemePath : String := "{scheme_path}"' not in rendered:
                raise RuntimeError(f"{query} selected a scheme from another namespace")
    entry.write_text(ENTRY.read_text())

    controls = work / "Checks.lean"
    imports = [f"public import {name}" for name in [*names, "Zkc.Formal.Written.FiniteModel"]]

    controls.write_text("\n".join(["module", "", *imports, "", CONTROL.read_text(),
                                   *(source_consumer(name, fixture) for name, fixture in
                                     [("Baseline", "Baseline"), ("Factored", "Baseline"), ("SameLog", "SameLog"), ("Context", "Baseline"),
                                      ("Named", "Baseline"), ("NamedArguments", "Baseline"), ("RolesReversed", "RolesReversed")]),
                                   """
open Zkc.Formal.Written.FiniteModel in
example (s : Context.PublicStatement model) :
    model.Val (.seq (.fin 256) none) × model.Val (.seq (.fin 256) none) :=
  (s.src_message, s.src_domain)
open Zkc.Formal.Written.FiniteModel in
example : ¬ (Context.PublicStatement.mk (M := model) true false [256] []).Valid := by
  intro h
  exact (Nat.lt_irrefl 256) (h.2.2.1.1 256 (by simp))
example : Named.selectedScheme = "Proof" ∧ Named.selectedGoal = some "chosen" ∧
    Named.selectedStage = "written" ∧ Named.selectedClause = some "second" ∧
    Named.uncoveredClauses.any (fun x => x.1 == "knowledge" && x.2.1 == some "first") := by decide
"""]))
    (work / "OddFork.lean").write_text(Path(__file__).with_name("OddFork.lean.in").read_text())
    (work / "AuditVendor.lean").write_text("module\npublic import Baseline\n"
        "namespace AuditVendor\nprivate axiom extra : False\n"
        "public theorem exported : False := extra\nend AuditVendor\n")
    (work / "AuditLocal.lean").write_text("module\npublic import AuditVendor\n"
        "public theorem AuditLocal.fromExternal : False := AuditVendor.exported\n")
    run(["lake", "-q", "build", "+AuditLocal", "+Checks", "+OddFork", "+SharedReplay"], cwd=work)
    print(run(["lake", "-q", "lean", AUDIT], cwd=work), end="", flush=True)
    print("Checked admitted group certificates, the helper companion, permitted forks and source counterexamples.", flush=True)

    failed = work / "Rejected.lean"
    for name, issued in [("Baseline", base), ("SameLog", same_log_module)]:
        weakened = issued.split("theorem certified_core_admitted {", 1)[0]
        weakened = replace_once(weakened, "public import Zkc.Formal.Written.GroupReplay",
                                "public import Zkc.Formal.Written.GroupReplay\npublic import Zkc.Formal.Written.FiniteModel")
        weakened += f"theorem certified_source_admitted : True := trivial\nend «{name}»\n"
        failed.write_text(weakened + source_consumer(name, name))
        run(["lake", "-q", "lean", failed], failure="Function expected", cwd=work)
    reindexed = Path(__file__).with_name("ReindexedConsumer.lean.in").read_text()
    failed.write_text(reindexed)
    run(["lake", "-q", "lean", failed], cwd=work)
    failed.write_text(reindexed + source_consumer("Reindexed", "Baseline"))
    run(["lake", "-q", "lean", failed], failure="mismatch", cwd=work)
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
        (replace_once(original, "zero_knowledge honest: by simulate using coins",
                      "zero_knowledge honest: by DLog using coins"), "SX6"),
        (replace_once(original, clause, clause + '\n    knowledge DLog(base) by external("other")'), "SX3"),
        (replace_once(original, "pub def response_difference", "pub spec def response_difference"), "SX6"),
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
        (replace_once(same_log, "        knowledge SameLog", "    spec for ChaumPedersen:\n        knowledge SameLog"), "SX5"),
        (replace_once(same_log, "runs[0].c", "runs[0].1"), "TY7"),
        (replace_once(same_log, "runs[0].c", "runs[0][1]"), "NL6"),
        (replace_once(same_log, "runs[0].c", "runs.0.c"), "TY7"),
        (replace_once(same_log, "        r @P <- sample G::Scalar", "        r @P <- sample G::Scalar\n        #[site(second)]\n        r @P <- sample G::Scalar"), "NL2"),
        (replace_once(projected, "        c <- draw", "        #[site(site1)]\n        c <- draw"), "WK-VIEW"),
    ]:
        reject_in_both(source, diagnostic, same_log=True)
    reject_in_both(original, "WK-NAMESPACE", namespace="Broken.name")
    entry.write_text(ENTRY.read_text() + "\nspec for Schnorr:\n    requires false\n")
    reject_in_both(original, "SX5")
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
