"""Compare every installed MSB table-family binding across all three consumers.

Asymmetric logical inputs distinguish MSB storage from an unconverted native
buffer. Table-free operations are deliberately included: their MSB names were
previously admitted by C++/Lean but omitted by both Rust signature catalogs.

It lives here rather than inside the test that states it, because it was once
imported from that test by a second one, and a test that imports another test
makes the second one's result depend on the first one's shape.
"""

import json


def check_bindings(journal, compiler, runtime, lean):
    output = journal.directory
    output.mkdir(parents=True, exist_ok=True)
    field = "bls12-381.fr"
    table = ["table", ["1", "2", "4", "8"]]
    other = ["table", ["3", "5", "7", "11"]]
    scalar = ["field", "3"]
    point = ["point", ["2", "3"]]
    round_value = ["round", ["1", "2", "4"]]
    cases = [
        ("poly.product_sum", [table, other], "field"),
        ("poly.product_round", [table, other], "round"),
        ("poly.boundary", [round_value], "field"),
        ("poly.round_evaluate", [round_value, scalar], "field"),
        ("poly.fold", [table, scalar], "table"),
        ("poly.evaluate", [table, point], "field"),
        ("poly.empty_point", [], "point"),
        ("poly.append_point", [point, scalar], "point"),
        ("vector.from_table", [table], "vector"),
        ("vector.to_table", [["vector", ["1", "2", "4", "8"]]], "table"),
    ]
    results = []

    def save(name, value):
        path = output / (name + ".json")
        path.write_text(json.dumps(value) + "\n")
        return path

    def run(name, *command):
        answer = journal.json(list(command))
        (output / (name + ".stdout")).write_text(json.dumps(answer) + "\n")
        return answer

    for contract, inputs, result_kind in cases:
        ports = [[f"x{i}", value[0] + ":" + field] for i, value in enumerate(inputs)]
        names = [port[0] for port in ports]
        outputs = [result_kind + ":" + field]
        source = ["zkc.protocol/1", [["kernel", contract, [field], ""]],
                  [["function", "Calculate", ports, outputs,
                    [["op", "compute", "kernel", [], names, ["result"]], ["return", ["result"]]], ["Calculate", []]]],
                  [["protocol", "Main", ["P"], [], [[n, "P", t] for n, t in ports],
                    [["P", outputs[0]]], [], [["local", "calculate", "P", "Calculate", names, ["result"]], ["return", ["result"]]]]],
                  [["instance", "root", "Main", [], [], [["P", "P"]]]], [["entry", "main", "root"]]]
        src = save(contract + ".source", source)
        config = save(contract + ".inputs", ["zkc.run/2", "main", "physical-bindings", [],
                      [["P", [], [[name, value] for name, value in zip(names, inputs)], []]], []])
        outcomes = []
        for backend in ("arkworks", "arkworks-msb"):
            name = contract + "." + backend
            selection = save(name + ".selection", [["kernel", backend + "/" + contract]])
            candidate = run(name + ".compile", compiler, "protocol-compile", src, "--implementations=" + str(selection))
            physical = save(name + ".physical", candidate)
            report = run(name + ".native", runtime, "run-protocol", src, physical, config, lean)
            assert report["outcome"][0] == "returned", report
            outcomes.append(report["outcome"])
            if contract == "vector.to_table":
                malformed = json.loads(config.read_text())
                malformed[4][0][2][0][1] = ["vector", ["1", "2", "4"]]
                bad = save(name + ".non-power-of-two", malformed)
                refused = run(name + ".reject-shape", runtime, "run-protocol", src, physical, bad, lean)
                assert refused["outcome"][0] != "returned" and "invalid-table-length" in str(refused), refused
        assert outcomes[0] == outcomes[1], (contract, outcomes)
        results.append({"contract": contract, "same_logical_outcome": True})
    save("results", results)
    return results
