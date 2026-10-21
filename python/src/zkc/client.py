"""A process adapter, with the Rust CLI owning compilation and execution.

Arguments and results use the inspected Entry's JSON schema. Mathematical wire
values and candidate proof bytes are passed unchanged to their native owners.
"""

from __future__ import annotations

import json
import math
import os
import signal
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

_MAX_BYTES = 64 * 1024 * 1024
_COMMAND_SUCCESS = {"run": "executed", "prove": "produced", "verify": "accepted", "inspect": "inspected"}
_SUCCESS = set(_COMMAND_SUCCESS.values())
Input = Mapping[str, Any] | str | Path


class ToolError(RuntimeError):
    """The executable failed to provide a complete machine report."""


class ExecutionError(RuntimeError):
    """An Entry failed; its complete native report remains available."""

    def __init__(self, execution: Execution):
        self.execution = execution
        super().__init__(str(execution.report.get("code", execution.report["status"])))


@dataclass(frozen=True)
class Execution:
    """A source return or proof, plus the native diagnostic report.

    A successful source ``Rejected`` variant is ordinary ``value`` data. Direct
    ``verify`` rejection has ``ok == False`` and retains the verifier report.
    """

    report: Mapping[str, Any]
    value: Any = None
    proof: bytes | None = None

    @property
    def ok(self) -> bool:
        return self.report["status"] in _SUCCESS

    def require_success(self) -> Execution:
        if not self.ok:
            raise ExecutionError(self)
        return self


def _read(path: Path) -> bytes:
    with path.open("rb") as stream:
        data = stream.read(_MAX_BYTES + 1)
    if len(data) > _MAX_BYTES:
        raise ToolError("zkc response exceeds the adapter byte limit")
    return data


def _json(path: Path, value: Any) -> None:
    data = json.dumps(value, ensure_ascii=False, allow_nan=False).encode("utf-8")
    if len(data) > _MAX_BYTES:
        raise ValueError("zkc input exceeds the adapter byte limit")
    path.write_bytes(data)


def _input(directory: Path, name: str, value: Input) -> Path:
    # Keep caller documents in place: the common Host resolves file references
    # relative to that document, with its ordinary confinement and quota checks.
    if isinstance(value, (str, Path)):
        return Path(value).absolute()
    path = directory / name
    _json(path, value)
    return path


def _stop(process: subprocess.Popen) -> None:
    # Only our new process group is cancelled; compiler children share it.
    if os.name == "posix":
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    else:
        process.terminate()
    try:
        process.wait(timeout=1)
    except subprocess.TimeoutExpired:
        if os.name != "posix":
            process.kill()
    finally:
        if os.name == "posix":
            # The group may outlive its leader, including a child ignoring TERM.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        process.wait()


def _wait(process: subprocess.Popen, paths: Sequence[Path], timeout: float) -> int:
    deadline = time.monotonic() + timeout
    while True:
        if any(path.stat().st_size > _MAX_BYTES for path in paths):
            raise ToolError("zkc output exceeds the adapter byte limit")
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(process.args, timeout)
        try:
            result = process.wait(timeout=min(0.05, remaining))
            if any(path.stat().st_size > _MAX_BYTES for path in paths):
                raise ToolError("zkc output exceeds the adapter byte limit")
            return result
        except subprocess.TimeoutExpired:
            continue


class Client:
    """Select a source project or an independently pinned compiled package.

    Each call starts the installed CLI and therefore performs its normal native
    admission. Use the Rust SDK to retain an admitted Host across many calls.
    ``options`` are explicit CLI options, passed without a shell. Services,
    setup authority and limits keep the same meaning as on the command line.
    """

    def __init__(
        self,
        project: str | Path | None = None,
        *,
        executable: str | Path = "zkc",
        compiler: str | Path | None = None,
        package: str | Path | None = None,
        sha256: str | None = None,
        timeout: float = 300,
    ):
        if package is not None:
            if project is not None or compiler is not None or sha256 is None:
                raise ValueError("package mode requires a pin and excludes source options")
            if len(sha256) != 64 or any(c not in "0123456789abcdef" for c in sha256):
                raise ValueError("sha256 must be 64 lowercase hexadecimal digits")
            self._selection = [f"--package={Path(package).resolve()}", f"--sha256={sha256}"]
        else:
            if sha256 is not None:
                raise ValueError("sha256 requires a package")
            self._selection = [] if project is None else [f"--project={Path(project).resolve()}"]
            if compiler is not None:
                self._selection.append(f"--compiler={compiler}")
        if not math.isfinite(timeout) or timeout <= 0:
            raise ValueError("timeout must be finite and positive")
        self.executable = str(executable)
        self.timeout = timeout

    def _invoke(
        self, command: str, entry: str | None, flags: Sequence[str], directory: Path
    ) -> dict[str, Any]:
        argv = [self.executable, "--json", command]
        if entry is not None:
            argv.append(entry)
        argv.extend(self._selection)
        argv.extend(flags)
        stdout = directory / "report.json"
        stderr = directory / "diagnostics.txt"
        try:
            with stdout.open("wb") as output, stderr.open("wb") as diagnostics:
                process = subprocess.Popen(
                    argv, stdin=subprocess.DEVNULL, stdout=output, stderr=diagnostics,
                    start_new_session=os.name == "posix",
                )
                try:
                    returncode = _wait(process, (stdout, stderr), self.timeout)
                except BaseException:
                    _stop(process)
                    raise
        except (OSError, subprocess.TimeoutExpired) as error:
            raise ToolError(f"zkc invocation failed: {type(error).__name__}") from error
        try:
            report = json.loads(_read(stdout))
        except (ValueError, OSError) as error:
            raise ToolError("zkc did not return a complete JSON report") from error
        if not isinstance(report, dict) or not isinstance(report.get("status"), str):
            raise ToolError("invalid zkc machine report")
        if report["status"] in _SUCCESS and report["status"] != _COMMAND_SUCCESS[command]:
            raise ToolError("zkc report belongs to a different command")
        successful = report["status"] == _COMMAND_SUCCESS[command]
        if (returncode == 0) != successful:
            raise ToolError("zkc exit status disagrees with its machine report")
        return report

    def inspect(self, entry: str | None = None) -> Execution:
        with tempfile.TemporaryDirectory(prefix="zkc-python-") as temporary:
            report = self._invoke("inspect", entry, [], Path(temporary))
            interface = report.get("interface")
            if report["status"] == "inspected" and not isinstance(interface, dict):
                raise ToolError("zkc did not return its inspected interface")
            return Execution(report, interface)

    def run(
        self,
        arguments: Input,
        *,
        entry: str | None = None,
        options: Sequence[str] = (),
    ) -> Execution:
        with tempfile.TemporaryDirectory(prefix="zkc-python-") as temporary:
            directory = Path(temporary)
            inputs = _input(directory, "arguments.json", arguments)
            outputs = directory / "result.json"
            report = self._invoke(
                "run", entry, [*options, f"--input={inputs}", f"--results={outputs}"], directory
            )
            value = None
            if report["status"] == "executed":
                try:
                    envelope = json.loads(_read(outputs))
                    if not isinstance(envelope, dict) or envelope.get("format") != "zkc.entry-outputs/0" or "value" not in envelope:
                        raise ValueError("unexpected source result")
                    value = envelope["value"]
                except (KeyError, ValueError, OSError) as error:
                    raise ToolError("zkc did not publish its complete source result") from error
            return Execution(report, value)

    def prove(
        self,
        public: Input,
        witness: Input,
        *,
        entry: str | None = None,
        options: Sequence[str] = (),
    ) -> Execution:
        with tempfile.TemporaryDirectory(prefix="zkc-python-") as temporary:
            directory = Path(temporary)
            public_file = _input(directory, "public.json", public)
            witness_file = _input(directory, "witness.json", witness)
            proof_file = directory / "candidate.zkproof"
            report = self._invoke("prove", entry, [
                *options, f"--public={public_file}", f"--witness={witness_file}",
                f"--output={proof_file}",
            ], directory)
            try:
                proof = _read(proof_file) if report["status"] == "produced" else None
            except OSError as error:
                raise ToolError("zkc did not publish its complete proof") from error
            return Execution(report, proof=proof)

    def verify(
        self,
        public: Input,
        proof: bytes,
        *,
        entry: str | None = None,
        options: Sequence[str] = (),
    ) -> Execution:
        if len(proof) > _MAX_BYTES:
            raise ValueError("proof exceeds the adapter byte limit")
        with tempfile.TemporaryDirectory(prefix="zkc-python-") as temporary:
            directory = Path(temporary)
            public_file = _input(directory, "public.json", public)
            proof_file = directory / "candidate.zkproof"
            proof_file.write_bytes(proof)
            report = self._invoke("verify", entry, [
                *options, f"--public={public_file}", f"--proof={proof_file}",
            ], directory)
            return Execution(report)
