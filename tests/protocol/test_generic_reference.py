"""Original generic source versus the independently implemented Lean consumer.

This exercises formation and local/whole-source structural correspondence,
including typed local reification, not execution equivalence. Run with native
compiler, Lean consumer and repository.
"""

import copy
import json
from pathlib import Path
import random

from journal import Journal
from toolchain import Toolchain, records


# The Lean reference these generic sources are checked against.
def main():
    CHECKER = "interactive-protocol"

    tools = Toolchain()
    compiler = tools.compiler
    checker = tools.checker(CHECKER)
    repository = Path(__file__).resolve().parents[2]

    root = Path(repository)
    counts = {"formation": 0, "local": 0, "whole": 0, "refusal": 0}


    journal = Journal(records(), timeout=30)

    def native(command, source):
        return journal.json([compiler, command, "-"], source)


    directory = journal.directory
    source_path = Path(directory) / "source.json"
    candidate_path = Path(directory) / "candidate.json"

    def check(source, candidate=None, config=None, function=None, error=None):
        source_path.write_text(json.dumps(source))
        command = [checker, "--generic-declarations", str(source_path)]
        if candidate is not None:
            candidate_path.write_text(json.dumps(candidate))
            command = [checker, "--check-local", str(source_path), config,
                       str(candidate_path), function]
        result = journal.attempt(command)
        response = json.loads(result.stdout)
        if error:
            assert result.returncode == 1 and response == ["refused", error], (error, response)
            counts["refusal"] += 1
        else:
            claim = "generic-local-formation" if candidate is None else "generic-local-correspondence"
            assert result.returncode == 0 and response == ["checked", claim, "not-whole-source-admission"], response
            counts["formation" if candidate is None else "local"] += 1

    def fixture(name):
        text = (root / "tests/fixtures" / name).read_text()
        return native("protocol-source", text), native("protocol-compile", text)

    def whole(source, candidate, error=None):
        source_path.write_text(json.dumps(source))
        candidate_path.write_text(json.dumps(candidate))
        result = journal.attempt([checker, "--check-generic", source_path, candidate_path])
        response = json.loads(result.stdout)
        if error:
            assert result.returncode == 1 and response == ["refused", error], (error, response)
            counts["refusal"] += 1
        else:
            assert result.returncode == 0 and response[:2] == ["checked", "generic-structural-correspondence"], response
            assert response[-1] == "no-elaboration-adequacy-proof"
            counts["whole"] += 1
        return response

    source, candidate = fixture("generic-operations.pir")
    check(source)
    mapping = whole(source, candidate)
    assert {p[1] for p in mapping[2]} == {"P", "V"}
    assert len(mapping[3]) == 5
    assert {p[2] for p in mapping[3]} == {"left", "right", "shared", "scale", "both"}
    # The actual occurrence map is unique even when several implementations
    # would be valid for an unconstrained source configuration.
    assert next(p for p in mapping[3] if p[2] == "right")[4] == next(p for p in mapping[3] if p[2] == "shared")[4]
    left = next(f for f in candidate[3] if f[5][0] == "Fold" and len(f[4]) == 4)
    right = next(f for f in candidate[3] if f[5][0] == "Fold" and len(f[4]) == 2)
    for f in candidate[3]:
        config = {"Scale": "Curve", "Both": "Boolean", "Fold": "Right"}[f[5][0]]
        if f is left:
            config = "Left"
        check(source, candidate, config, f[1])
    check(source, candidate, "Shared", right[1])
    check(source, candidate, "Unused", right[1], "generic-open-instance")
    check(source, candidate, "Left", right[1], "local-selection-correspondence")

    def source_mutation(mutate, error):
        changed = copy.deepcopy(source)
        mutate(changed)
        check(changed, error=error)

    source_mutation(lambda s: s[1][0].__setitem__(3, []), "generic-requirement-not-provided")
    source_mutation(lambda s: s[1][1][4][1].__setitem__(1, "field:G"), "generic-type-sort")
    source_mutation(lambda s: s[2][1][3][0].__setitem__(1, "bls12-381.g1"), "generic-configuration-sort")
    source_mutation(lambda s: s[2][3].__setitem__(3, [["F", "bls12-381.fr"]]), "generic-configuration-rebinding")
    source_mutation(lambda s: s[2][0].__setitem__(2, "Shared"), "generic-configuration-cycle")
    source_mutation(lambda s: s[2][1][4][0].__setitem__(1, "arkworks/curve.scale"), "binding-implementation")
    source_mutation(lambda s: s[1][0][6][0].__setitem__(4, ["extra"]), "kernel-attributes")
    source_mutation(lambda s: s[1][0][2][0].__setitem__(1, "HiddenSort"), "generic-declared-sort")

    # An unused declaration still has to respect affine resource use.
    alias = ["generic_function", "Reuse", [["F", "Field"]], [["Field", ["F"]]],
             [["rng", "rng:F"]], [], [
                 ["op", "a", "random.draw", ["F"], [], ["rng"], ["x", "next"]],
                 ["op", "b", "random.draw", ["F"], [], ["rng"], ["y", "last"]], ["return", []]]]
    source_mutation(lambda s: s[1].append(alias), "generic-affine-reuse")

    partial = copy.deepcopy(source)
    partial[1].append(["generic_function", "Encoding", [["E", "Codec"], ["D", "Codec"], ["F", "Field"]],
                       [["=", ["E", "D"]], ["Encodes.field", ["E", "F"]]], [], [], [["return", []]]])
    partial[2].append(["configure", "EncodingChoice", "Encoding", [["D", "zkcv.bool/1"], ["F", "bls12-381.fr"]], []])
    check(partial, error="binding-requirement")
    partial[2][-1][3][0][1] = "zkcv.field.bls12-381.fr/1"
    check(partial)

    # Full supported equality scopes previously caused repeated linear scans
    # through every established proof fact. Keep the maximum-size case covered.
    for size in (64, 128):
        large = ["zkc.library/1", [["generic_function", "Large",
                 [[f"F{i}", "Field"] for i in range(size)],
                 [["=", [f"F{i}", f"F{i + 1}"]] for i in range(size - 1)],
                 [], [], [["return", []]]]], [], ["zkc.protocol/1", [], [], [], [], []]]
        check(large)
    large[1][0][2].append(["TooMany", "Field"])
    check(large, error="generic-parameters")

    def candidate_mutation(mutate, error):
        changed = copy.deepcopy(candidate)
        function = next(f for f in changed[3] if f[1] == left[1])
        mutate(changed, function)
        check(source, changed, "Left", function[1], error)

    candidate_mutation(lambda c, f: f[5].__setitem__(0, "Another"), "local-origin-correspondence")
    candidate_mutation(lambda c, f: f[5][1][0].__setitem__(1, "bls12-381.g1"), "local-origin-correspondence")
    candidate_mutation(lambda c, f: f[4][1].__setitem__(1, "changed"), "local-operation-correspondence")
    # Physical formation runs before source correspondence. These corruptions
    # are already ill-typed; assert its exact earlier refusal, not a later check.
    candidate_mutation(lambda c, f: f[4].pop(0), "unbound:" + left[4][0][5][0])
    candidate_mutation(lambda c, f: f[4][0].__setitem__(3, ["extra"]), "interactive-kernel-parameters")
    candidate_mutation(lambda c, f: f[4][-1].__setitem__(1, [f[4][1][5][0]]), "function-return-types")
    candidate_mutation(lambda c, f: f[4][1][4].__setitem__(1, f[2][0][0]), "binding-operation-signature")
    candidate_mutation(lambda c, f: f[2][0].__setitem__(1, "table:bls12-381.fr@arkworks.mle-msb/1"),
                       "binding-operation-signature")

    def extra_conversion(c, f):
        extra = copy.deepcopy(f[4][0])
        extra[1], extra[5] = "extra", ["unused_conversion"]
        f[4].insert(1, extra)

    candidate_mutation(extra_conversion, "local-operation-correspondence")

    # Alpha-renaming and generated symbols have no compiler-specific authority.
    renamed = copy.deepcopy(candidate)
    fn = next(f for f in renamed[3] if f[1] == left[1])
    fn[1] = "independently_named_function"
    names = {p[0]: "arg_" + str(i) for i, p in enumerate(fn[2])}
    for p in fn[2]:
        p[0] = names[p[0]]
    for instruction in fn[4]:
        if instruction[0] == "return":
            instruction[1] = [names[n] for n in instruction[1]]
        else:
            instruction[4] = [names[n] for n in instruction[4]]
            outputs = instruction[5]
            for n in outputs:
                names[n] = "result_" + str(len(names))
            instruction[5] = [names[n] for n in outputs]
    check(source, renamed, "Left", fn[1])

    for name in ["generic-openings.pir", "generic-stops.pir"]:
        original, compiled = fixture(name)
        check(original)
        whole(original, compiled)
        # Read the original configuration-to-definition selection, not a hash.
        for f in compiled[3]:
            config = next(c[1] for c in original[2] if c[2] == f[5][0])
            check(original, compiled, config, f[1])

    fixed_text = (root / "tests/fixtures/bound-operations.pir").read_text()
    fixed = ["zkc.library/1", [], [], native("protocol-source", fixed_text)]
    whole(fixed, native("protocol-compile", json.dumps(fixed)))

    for index in (1048576, 1048577):
        indexed = copy.deepcopy(source)
        indexed[1].append(["generic_function", "At", [["G", "Group"]], [["ScalarAction", ["G"]]],
                           [["points", "groups:G"]], ["group:G"], [
                               ["op", "at", "curve.at", ["G"], [str(index)], ["points"], ["point"]],
                               ["return", ["point"]]]])
        check(indexed, error="kernel-attributes" if index > 1048576 else None)

    # Generic locals remain composable under shared protocol calls and loops.
    nested = copy.deepcopy(source)
    field, table = "field:bls12-381.fr", "table:bls12-381.fr"
    child = ["protocol", "Step", ["P", "V"], [], [["a", "P", table], ["r", "V", field]],
             [["P", table], ["V", field]], [], [
                 ["message", "challenge", "field_challenge", "V", "P", "r", "received"],
                 ["local", "fold", "P", "Right", ["a", "received"], ["out"]], ["return", ["out", "r"]]]]
    parent = ["protocol", "Repeated", ["P", "V"], [], [["a", "P", table], ["r", "V", field]],
              [["P", table], ["V", field]], [["step", "Step", []]], [
                  ["loop", "rounds", ["constant", "3"], [["t", "a"], ["c", "r"]], [], [
                      ["call", "child", "step", ["t", "c"], ["next", "again"]], ["yield", ["next", "again"]]],
                   ["final", "last"]], ["return", ["final", "last"]]]]
    nested[3][3:] = [[child, parent], [
        ["instance", "child", "Step", [], [], [["P", "P"], ["V", "V"]]],
        ["instance", "parent", "Repeated", [], [["step", "child"]], [["P", "P"], ["V", "V"]]]],
        [["entry", "main", "parent"]]]
    compiled = native("protocol-compile", json.dumps(nested))
    whole(nested, compiled)
    broken = copy.deepcopy(compiled)
    role = next(p for p in broken[4] if p[2] == "parent")
    role[7][0][2] = "2"
    whole(nested, broken, "participant-loop-correspondence")
    broken = copy.deepcopy(compiled)
    role = next(p for p in broken[4] if p[2] == "child" and p[3] == "V")
    role[7][0][3] = "V"
    whole(nested, broken, "participant-instruction-correspondence")
    broken = copy.deepcopy(compiled)
    role = next(p for p in broken[4] if p[2] == "child" and p[3] == "V")
    role[5][0][1] = "group:bls12-381.g1@arkworks.g1/1"
    whole(nested, broken, "participant-signature-correspondence")

    # Deterministic generated source exercises literal elaboration at and far
    # above the modulus. Python only generates input; Lean checks source meaning.
    modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513
    rng = random.Random(418920)
    for value in [0, 1, modulus - 1, modulus, modulus + 1, 10**1023] + [rng.randrange(10**180) for _ in range(20)]:
        literal = f"""module {{
              fn Literal<F: domain Field>() -> (F::Element) requires (Field(F)) {{
                [constant] let result = field::constant::<F>() attributes (\"{value}\"); return (result);
              }}
              configure Number = Literal(F = bls12-381.fr);
              protocol P {{ roles (A); inputs (); outputs (A "bls12-381.fr"::Element);
                local [call] A: let value = Number(); return (value); }}
              instance p: P {{ roles (A = A); }} entry main = p;
            }}"""
        original, compiled = native("protocol-source", literal), native("protocol-compile", literal)
        f = compiled[3][0]
        check(original, compiled, "Number", f[1])
        whole(original, compiled)
        f[4][0][3][0] = str((value + 1) % modulus)
        check(original, compiled, "Number", f[1], "local-attributes-correspondence")

    print(json.dumps(counts, sort_keys=True))



def test_generic_reference():
    main()


if __name__ == "__main__":
    main()
