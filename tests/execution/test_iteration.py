"""Compare complete controller prefixes in independently implemented evaluators."""

import subprocess


def test_iteration_reference(toolchain, directory):
    outputs = []
    for kind, name in (("native", "examples/iteration_reference"),
                       ("lean", "iteration-reference")):
        output = subprocess.run([str(toolchain.tool(kind, name))], check=True,
                                capture_output=True, text=True).stdout
        (directory / f"{kind}.txt").write_text(output)
        outputs.append(output.splitlines())
    assert len(outputs[0]) == 1326
    assert outputs[0] == outputs[1]
    # A shared collapse of pending into exhaustion or loss of stopped effects
    # must fail independently of cross-implementation agreement.
    assert "2|2|0|false|pending|2|0,1" in outputs[0]
    assert "2|3|0|false|returned:2|3|0,1,2" in outputs[0]
    assert "5|8|3|true|reject|4|3" in outputs[0]
    # Independent expected records check carried values, accumulated effects,
    # explicit closure, and every fatal reason, including a body's exhaustion.
    for mode in ("whole", "split"):
        assert f"resume|3|4|1|1|{mode}|pending:1|9|3,2" in outputs[0]
        assert f"resume|3|4|2|3|{mode}|returned:10|10|3,2,1,0" in outputs[0]
    for mode in ("close-whole", "close-split"):
        assert f"resume|3|4|1|1|{mode}|exhausted|9|3,2" in outputs[0]
        assert f"resume|3|4|2|3|{mode}|returned:10|10|3,2,1,0" in outputs[0]
    for reason in ("reject", "abort", "exhausted", "incomplete", "refused"):
        for mode in ("prefix", "close"):
            assert f"stop|{reason}|3|{mode}|{reason}|2|0,1" in outputs[0]
        assert f"stop|{reason}|1|prefix|pending|1|0" in outputs[0]
        assert f"stop|{reason}|1|close|exhausted|1|0" in outputs[0]
