"""Participant-owned finalization against the independent joint source path.

The source contains transparent control after its last cut. Only lexical final
polling can complete a root; completing a local or child return cannot. Expected
residue is stated directly, as well as compared with native participant frames.
"""
import json
import subprocess

import pytest

UNIT = "resource_unit:Slot.A"
FIELD = "field:bls12-381.fr"


def write(directory, name, value):
    path = directory / name
    path.write_text(json.dumps(value))
    return path


def good(command):
    result = subprocess.run([str(x) for x in command], text=True,
                            capture_output=True, timeout=120)
    assert result.returncode == 0, (command, result.stdout, result.stderr)
    return json.loads(result.stdout)


def source(returner="P", stopper="V", keep=True, nested=False, ending="drain"):
    operations = [["create", "resource_unit.create", ["Slot.A"], ""],
                  ["constant", "field.constant", ["bls12-381.fr"], ""],
                  ["equal", "field.equal", ["bls12-381.fr"], ""]]
    make = [["op", "make", "create", [], [], ["x"]], ["return", ["x"]]]
    if nested:
        arm = [["op", "make", "create", [], [], ["inner"]], ["yield", ["inner"]]]
        make = [["op", "zero", "constant", ["0"], [], ["z"]],
                ["op", "equal", "equal", [], ["z", "z"], ["yes"]],
                ["if", "choose", "yes", [], arm, [["op", "other", "create", [], [], ["other"]],
                                      ["yield", ["other"]]], ["x"]], ["return", ["x"]]]
    functions = [["function", "Make", [], [UNIT], make, ["Make", []]],
                 ["function", "Refuse", [], [], [["stop", "halt", "", "reject"]], ["Refuse", []]],
                 ["function", "Nop", [], [], [["return", []]], ["Nop", []]],
                 ["function", "Zero", [], [FIELD], [
                     ["op", "zero", "constant", ["0"], [], ["z"]],
                     ["return", ["z"]]], ["Zero", []]]]
    protocols = [["protocol", "Spin", ["S"], [], [], [], [], [
        ["loop", "spin", ["constant", "100001"], [], [], [["yield", []]], []],
        ["return", []]]]]
    instances = [["instance", "spin", "Spin", [], [], [["S", stopper]]]]
    dependencies = [["spin", "Spin", []]]
    bindings = [["spin", "spin"]]
    body = [["local", "make", "R", "Make", [], ["x"]]]
    if nested:
        protocols.append(["protocol", "Maker", ["R"], [], [], [["R", UNIT]], [],
                          [["local", "make", "R", "Make", [], ["x"]], ["return", ["x"]]]])
        instances.append(["instance", "maker", "Maker", [], [], [["R", returner]]])
        dependencies.append(["maker", "Maker", []])
        bindings.append(["maker", "maker"])
        body = [["call", "make", "maker", [], ["x"]]]
    # Both roles own a unit before the stop; the stopped one's must always retire.
    body.append(["local", "other", "S", "Make", [], ["other"]])
    if ending == "message":
        body.append(["local", "zero", "R", "Zero", [], ["z"]])
    if ending in ("drain", "later-local", "message"):
        body.append(["call", "spin", "spin", [], []])
    if ending == "local-stop":
        body.append(["local", "refuse", "S", "Refuse", [], []])
    elif ending == "later-local":
        body.append(["local", "later", "S", "Nop", [], []])
    elif ending == "message":
        body.append(["message", "later", "scalar", "R", "S", "z", "received"])
    if ending == "source-stop":
        body.append(["stop", "halt", "S", "reject"])
    else:
        body.append(["return", ["x"] if keep else []])
    protocols.append(["protocol", "Root", ["R", "S"], [], [],
                      [["R", UNIT]] if keep else [], dependencies, body])
    instances.append(["instance", "root", "Root", [], bindings,
                      [["R", returner], ["S", stopper]]])
    return ["zkc.protocol/1", operations, functions, protocols, instances,
            [["entry", "main", "root"]]]


def execute(toolchain, directory, program, roles):
    path = write(directory, "source.json", program)
    checker = toolchain.checker("interactive-protocol")
    # The reference command receives only source and its own logical inputs.
    reference = good([checker, "--reference", path, write(directory, "reference.json",
        ["zkc.reference-inputs/1", "main", "session", [[r, []] for r in roles], [], [], []])])
    candidate = write(directory, "physical.json", good([toolchain.compiler, "protocol-compile", path]))
    native = good([toolchain.runtime, "run-protocol", path, candidate, write(directory, "native.json",
        ["zkc.run/2", "main", "session", [], [[r, [], [], []] for r in roles], []]), checker])
    return reference, native


def no_cut_source(count, returner, worker):
    program = source(returner, worker, ending="returned")
    spin = program[3][0]
    spin[6] = [["grandchild", "Grandchild", []]]
    spin[7][0][2][1] = str(count)
    # Twelve resumable effects per iteration, but nine source charges. Empty
    # loops exercise real control work without exhausting native's call budget.
    spin[7][0][5] = [["loop", f"empty{i}", ["constant", "0"], [], [],
                      [["yield", []]], []] for i in range(7)] + [["yield", []]]
    spin[7].insert(0, ["call", "nested", "grandchild", [], []])
    program[3].insert(0, ["protocol", "Grandchild", ["S"], [], [], [], [], [["return", []]]])
    program[4][0][4] = [["grandchild", "grandchild"]]
    program[4].insert(0, ["instance", "grandchild", "Grandchild", [], [], [["S", worker]]])
    root = program[3][-1]
    root[5].append(["S", UNIT])
    root[7][-1:] = [["call", "spin", "spin", [], []], ["return", ["x", "other"]]]
    return program


@pytest.mark.parametrize("returner,worker", [("P", "V"), ("V", "P")])
@pytest.mark.parametrize("count", [90000, 100001])
def test_administrative_resumes_do_not_preempt_work_limits(toolchain, directory, returner, worker, count):
    reference, native = execute(toolchain, directory, no_cut_source(count, returner, worker), [returner, worker])
    opened = good([toolchain.checker("interactive-protocol"), "--generic-role", directory / "source.json",
                   write(directory, "open.json", ["zkc.reference-inputs/1", "main", "session",
                         [[worker, []]], [], [], []]), worker])
    for name, result in [("joint-result.json", reference), ("native-result.json", native),
                         ("open-result.json", opened)]:
        write(directory, name, result)
    if count == 90000:
        assert reference[3][0] == opened[3][0] == native["outcome"][0] == "returned"
        expected = sorted([returner, worker])
        assert native["usage"][worker]["iterations"] == count
        assert [r[1] for r in opened[5] if r[-1] == "resource_unit"] == [worker]
    else:
        assert reference[3][0:2] == opened[3][0:2] == ["exhausted", "local-iteration-limit"]
        assert reference[3][2][5:7] == opened[3][2][5:7] == ["spin", worker]
        assert reference[3][2][4][-1] == opened[3][2][4][-1] == ["iteration", "spin", "100000"]
        assert native["outcome"] == ["stopped", worker, None, "Limit"]
        assert native["usage"][worker]["iterations"] == 100000
        assert native["usage"][worker]["calls"] < 100000
        assert [r for r in opened[5] if r[-1] == "resource_unit"] == []
        expected = [returner] if returner < worker else []
        assert native["cancelled_roles"] == ([] if returner < worker else [returner])
    assert sorted(r[1] for r in reference[5] if r[-1] == "resource_unit") == expected
    assert all(native["usage"][role]["live_resource_units"] == int(role in expected)
               for role in [returner, worker])


@pytest.mark.parametrize("count", [499996, 499997])
def test_the_schedule_budget_stops_the_execution(toolchain, directory, count):
    """The joint schedule walks a protocol loop holding no local, message or
    stop without running a role, charging two of its 1,000,000 units per
    iteration. One iteration short of the budget, the spinning role's own
    iteration limit is reached first. At the budget the schedule is exhausted:
    an `exhausted` stop of the execution (docs/spec/core/execution.md), which
    native reports as a limit stop of the joint schedule, cancelling both roles.
    """
    program = source(ending="drain")
    program[3][0][7][0][2][1] = str(count)
    reference, native = execute(toolchain, directory, program, ["P", "V"])
    if count == 499996:
        assert reference[3][0:2] == ["exhausted", "local-iteration-limit"]
        assert native["outcome"] == ["stopped", "V", None, "Limit"]
        expected = ["P"]
    else:
        assert reference[3][0:2] == ["exhausted", "source-schedule-work-limit"]
        assert reference[3][2][6] == "joint"
        assert native["outcome"] == ["stopped", "joint", None, "Limit"]
        assert native["cancelled_roles"] == ["P", "V"]
        expected = []
    assert [r[1] for r in reference[5] if r[-1] == "resource_unit"] == expected
    assert all(native["usage"][role]["live_resource_units"] == int(role in expected)
               for role in ["P", "V"])


@pytest.mark.parametrize("returner,stopper", [("P", "V"), ("V", "P")])
@pytest.mark.parametrize("keep", [False, True])
@pytest.mark.parametrize("nested", [False, True])
def test_final_drain_preserves_only_already_returned_units(toolchain, directory, returner, stopper, keep, nested):
    reference, native = execute(toolchain, directory, source(returner, stopper, keep, nested), [returner, stopper])
    assert reference[3][0:2] == ["exhausted", "local-iteration-limit"], reference[3]
    assert reference[3][2][6] == stopper
    assert native["outcome"][0:2] == ["stopped", stopper]
    expected = int(keep and returner < stopper)
    units = [r for r in reference[5] if r[-1] == "resource_unit"]
    assert [r[1] for r in units] == [returner] * expected
    assert native["usage"][returner]["live_resource_units"] == expected
    assert native["usage"][stopper]["live_resource_units"] == 0
    assert native["cancelled_roles"] == ([returner] if stopper < returner else [])


@pytest.mark.parametrize("returner,stopper", [("P", "V"), ("V", "P")])
@pytest.mark.parametrize("ending", ["source-stop", "local-stop", "later-local", "message"])
def test_cuts_do_not_prematurely_complete_participants(toolchain, directory, returner, stopper, ending):
    reference, native = execute(toolchain, directory,
                                source(returner, stopper, True, True, ending), [returner, stopper])
    assert reference[3][0] == ("reject" if ending.endswith("stop") else "exhausted"), reference[3]
    assert native["outcome"][0:2] == ["stopped", stopper]
    assert [r for r in reference[5] if r[-1] == "resource_unit"] == []
    assert all(v["live_resource_units"] == 0 for v in native["usage"].values())
    assert native["cancelled_roles"] == [returner]
    if ending == "message":
        assert [event[0] for event in reference[4] if event[0] in ("send", "receive")] == ["send"]


@pytest.mark.parametrize("keep", [False, True])
@pytest.mark.parametrize("nested", [False, True])
def test_successful_roots_dispose_only_unreturned_units(toolchain, directory, keep, nested):
    reference, native = execute(toolchain, directory, source(keep=keep, nested=nested, ending="returned"), ["P", "V"])
    assert reference[3][0] == native["outcome"][0] == "returned"
    assert [r[1] for r in reference[5] if r[-1] == "resource_unit"] == ["P"] * int(keep)
    assert native["usage"]["P"]["live_resource_units"] == int(keep)
    assert native["usage"]["V"]["live_resource_units"] == 0


def test_iteration_allowance_belongs_to_each_participant(toolchain, directory):
    program = source(ending="returned")
    program[3][0][7][0][2][1] = "60000"
    program[3].insert(1, ["protocol", "SpinR", ["R"], [], [], [], [], program[3][0][7]])
    program[4].append(["instance", "spinR", "SpinR", [], [], [["R", "P"]]])
    root = program[3][-1]
    root[6].append(["spinR", "SpinR", []])
    program[4][-2][4].append(["spinR", "spinR"])
    root[7][-1:-1] = [["call", "spinP", "spinR", [], []], ["call", "spinV", "spin", [], []]]
    reference, native = execute(toolchain, directory, program, ["P", "V"])
    assert reference[3][0] == native["outcome"][0] == "returned"
    assert [r[1] for r in reference[5] if r[-1] == "resource_unit"] == ["P"]
    assert all(v["iterations"] == 60000 for v in native["usage"].values())


def test_child_disposal_preserves_outer_and_concurrent_role_units(toolchain, directory):
    program = source(ending="returned")
    program[3].insert(1, ["protocol", "Child", ["R", "S"], [], [["input", "R", UNIT]],
                         [["S", UNIT]], [], [
                             ["local", "pause", "R", "Nop", [], []],
                             ["local", "make", "S", "Make", [], ["made"]],
                             ["return", ["made"]]]])
    program[4].insert(1, ["instance", "child", "Child", [], [], [["R", "P"], ["S", "V"]]])
    root = program[3][-1]
    root[5] = [["S", UNIT], ["R", UNIT]]
    root[6].append(["child", "Child", []])
    program[4][-1][4].append(["child", "child"])
    root[7][-1:] = [["local", "spare", "R", "Make", [], ["spare"]],
                    ["call", "child", "child", ["spare"], ["child_unit"]],
                    ["return", ["child_unit", "x"]]]
    reference, native = execute(toolchain, directory, program, ["P", "V"])
    assert reference[3][0] == native["outcome"][0] == "returned"
    assert sorted(r[1] for r in reference[5] if r[-1] == "resource_unit") == ["P", "V"]
    assert all(v["live_resource_units"] == 1 for v in native["usage"].values())

    owners = {r[0]: r[1] for r in reference[5]}
    assert [owners[v[1][0]] for v in reference[3][1]] == ["V", "P"]


def test_message_completion_does_not_duplicate_receive(toolchain, directory):
    program = source(ending="message")
    program[3][0][7][0][2][1] = "0"
    reference, native = execute(toolchain, directory, program, ["P", "V"])
    assert reference[3][0] == native["outcome"][0] == "returned"
    assert [event[0] for event in reference[4] if event[0] in ("send", "receive")] == ["send", "receive"]
    assert native["wire"]["messages"] == 1
    assert [r[1] for r in reference[5] if r[-1] == "resource_unit"] == ["P"]


def ingress_source(work, body_work, parameters=1):
    program = source(ending="returned")
    root = program[3][-1]
    binding = program[4][-1]
    program[3], program[4] = [root], [binding]
    names = [f"rounds{i}" for i in range(parameters)]
    root[3] = names
    root[4] = [["pn", "R", "index"], ["vn", "S", "index"]]
    root[6], binding[4] = [], []
    binding[3] = [[name, ["ingress", "1", [["P", "Select", ["pn"]],
                                          ["V", "Select", ["vn"]]]]] for name in names]
    program[1].append(["index", "index.constant", [], ""])
    program[2].append(["function", "Select", [["n", "index"]], ["index"], [
        ["op", "zero", "index", ["0"], [], ["zero"]],
        ["op", "upper", "index", [str(work)], [], ["upper"]],
        ["for", "work", "i", "zero", "upper", [], [], [["yield", []]], []],
        ["op", "temporary", "create", [], [], ["temporary"]],
        ["return", ["n"]]], ["Select", []]])
    root[7].insert(-1, ["loop", "after", ["constant", str(body_work)], [], [], [["yield", []]], []])
    return program


@pytest.mark.parametrize("work,body_work,parameters,returns", [
    (30000, 80000, 1, False),  # body cannot reset completed ingress work
    (60000, 0, 1, True),      # the peer cannot consume this role's allowance
    (25000, 50001, 2, False), # selectors of one role share the allowance
])
def test_ingress_iterations_follow_the_participant_into_execution(
        toolchain, directory, work, body_work, parameters, returns):
    program = ingress_source(work, body_work, parameters)
    path = write(directory, "source.json", program)
    checker = toolchain.checker("interactive-protocol")
    inputs = [[role, [[name, ["index", "0"]]]] for role, name in [("P", "pn"), ("V", "vn")]]
    reference = good([checker, "--reference", path, write(directory, "reference.json",
        ["zkc.reference-inputs/1", "main", "session", inputs, [], [], []])])
    candidate = write(directory, "physical.json", good([toolchain.compiler, "protocol-compile", path]))
    native = good([toolchain.runtime, "run-protocol", path, candidate, write(directory, "native.json",
        ["zkc.run/2", "main", "session", [],
         [[role, [], [[name, ["wire", "5a4b4356011f0000000000000000"]]], []]
          for role, name in [("P", "pn"), ("V", "vn")]], []]), checker])
    if returns:
        assert reference[3][0] == native["outcome"][0] == "returned"
        assert [r[1] for r in reference[5] if r[-1] == "resource_unit"] == ["P"]
        assert all(v["iterations"] == work * parameters for v in native["usage"].values())
    else:
        assert reference[3][0:2] == ["exhausted", "local-iteration-limit"], reference[3]
        assert reference[3][2][5:7] == ["after", "P"], reference[3]
        assert native["outcome"][0:2] == ["stopped", "P"]
        assert native["usage"]["P"]["iterations"] == 100000
        assert [r for r in reference[5] if r[-1] == "resource_unit"] == []
        assert all(v["live_resource_units"] == 0 for v in native["usage"].values())
    # Selector-created units are disposed by the local frame in every case.
    selectors = [e for e in reference[4] if e[0] == "request" and e[1][2] == "resource_unit.create"
                 and e[1][1][4][0][1].startswith("ingress.")]
    assert len(selectors) == 2 * parameters


@pytest.mark.parametrize("extra,detail", [
    (5, "unused-primitive-replies"), (6, "unused-replies"),
])
def test_unused_fixture_replies_do_not_reopen_completed_roots(toolchain, directory, extra, detail):
    program = source(ending="returned")
    reference, native = execute(toolchain, directory, program, ["P", "V"])
    assert native["usage"]["P"]["live_resource_units"] == 1
    inputs = ["zkc.reference-inputs/1", "main", "session", [["P", []], ["V", []]], [], [], []]
    inputs[extra] = [["unrequested", ["ok", []] if extra == 5 else ["bool", "true"]]]
    failed = good([toolchain.checker("interactive-protocol"), "--reference", directory / "source.json",
                   write(directory, "extra.json", inputs)])
    assert failed[3][0:2] == ["refused", detail]
    assert failed[4:6] == reference[4:6]  # completed effects and returned units survive


def test_ingress_stop_precedes_earlier_parameter_disagreement(toolchain, directory):
    program = ingress_source(0, 0, parameters=2)
    program[4][0][3][0][1][1] = "3"  # first counts 2 and 1 disagree, but both fit
    path = write(directory, "source.json", program)
    checker = toolchain.checker("interactive-protocol")
    supplied = [("P", "pn", 2), ("V", "vn", 1)]
    reference = good([checker, "--reference", path, write(directory, "reference.json",
        ["zkc.reference-inputs/1", "main", "session",
         [[r, [[n, ["index", str(v)]]]] for r, n, v in supplied], [], [], []])])
    candidate = write(directory, "physical.json", good([toolchain.compiler, "protocol-compile", path]))
    native = good([toolchain.runtime, "run-protocol", path, candidate, write(directory, "native.json",
        ["zkc.run/2", "main", "session", [],
         [[r, [], [[n, ["wire", "5a4b4356011f" + v.to_bytes(8, "little").hex()]]], []]
          for r, n, v in supplied], []]), checker])
    assert reference[3][0:2] == ["refused", "interactive-family-bound"]
    assert reference[3][2][5:7] == ["ingress.rounds1", "P"]
    assert native["outcome"][0:3] == ["stopped", "P", "ingress.rounds1"]
    assert native["cancelled_roles"] == ["V"]
    assert reference[5] == []
    assert all(v["live_resource_units"] == 0 for v in native["usage"].values())
