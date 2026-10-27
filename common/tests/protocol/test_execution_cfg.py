"""Canonical execution CFGs retain native behavior through the current VM."""


def test_scoped_execution_cfg(toolchain, directory, journal):
    artifacts = directory / "execution"
    journal.run([
        toolchain.tool("compiler", "test/zkc-execution_emission-test"), artifacts,
    ], keep="compiler.txt")
    for name in ("conditional-return", "unconditional-return",
                 "conditional-stop", "unconditional-stop"):
        text = (artifacts / f"{name}.mlir").read_text()
        assert "runtime.exit_scope" in text
        assert "runtime.accept_transfer" in text
        assert "exec.match" in text
        assert "exec.test" in text
        assert "local.for" not in text and "local.if" not in text
    journal.run([toolchain.driver("execution_cfg"), artifacts], keep="native.txt")
