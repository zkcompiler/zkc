"""Structural source formation through closed native Finite and the actual Host."""

from pathlib import Path
import json

import pytest

from test_language_views import compile_view, run_view
from entry import joint_package


SOURCE = (
    Path(__file__).resolve().parents[3]
    / "compiler/test/fixtures/layout/structural-descriptors.zkc"
)


@pytest.mark.parametrize("flags", [(), ("--no-simplify",), ("--no-finite-bulk",)])
def test_selected_structural_guards_and_unrelated_descriptors(
    toolchain, journal, directory, flags
):
    package, pin = compile_view(
        toolchain, journal, directory, SOURCE.read_text(), flags
    )
    values = {
        "xs": ["2", "3"],
        "ys": ["4", "5"],
        "unrelated": [],
        "lo": "0",
        "hi": "2",
        "initial": "7",
    }
    assert (
        run_view(toolchain, journal, directory, package, pin, "selected", values)
        == "17"
    )
    values["hi"] = "0"
    assert (
        run_view(toolchain, journal, directory, package, pin, "empty-result", values)
        == "7"
    )
    values["ys"] = []
    run_view(
        toolchain,
        journal,
        directory,
        package,
        pin,
        "invalid-sibling-at-empty-result",
        values,
        refuses="entry-host-run-failed",
    )


@pytest.mark.parametrize("flags", [(), ("--no-simplify",), ("--no-finite-bulk",)])
def test_selected_row_guard_survives_empty_result(toolchain, journal, directory, flags):
    source = (
        SOURCE.read_text()
        .replace("protocol Demo ", "protocol Vectors ")
        .replace("protocol Rows ", "protocol Demo ")
    )
    package, pin = compile_view(toolchain, journal, directory, source, flags)
    values = {
        "matrix": {"rows": "1", "columns": "0", "entries": []},
        "i": "0",
        "xs": [],
        "lo": "0",
        "hi": "0",
        "initial": "7",
    }
    assert (
        run_view(toolchain, journal, directory, package, pin, "empty-row", values)
        == "7"
    )
    values["i"] = "1"
    run_view(
        toolchain,
        journal,
        directory,
        package,
        pin,
        "invalid-row-at-empty-result",
        values,
        refuses="entry-host-run-failed",
    )


@pytest.mark.parametrize("flags", [(), ("--no-simplify",), ("--no-finite-bulk",)])
def test_zero_fold_context_guard_and_absent_step(toolchain, journal, directory, flags):
    source = (
        SOURCE.read_text()
        .replace("protocol Demo ", "protocol Vectors ")
        .replace("protocol Zero ", "protocol Demo ")
    )
    package, pin = compile_view(toolchain, journal, directory, source, flags)
    original = joint_package(json.loads(package.read_text()))["original"]
    assert original.count('"data.domain_zip"') == 1
    values = {"xs": ["2"], "ys": ["3"], "lo": "0", "hi": "0", "initial": "7"}
    assert run_view(toolchain, journal, directory, package, pin, "zero", values) == "7"
    values["ys"] = []
    run_view(
        toolchain,
        journal,
        directory,
        package,
        pin,
        "invalid-zero-context",
        values,
        refuses="entry-host-run-failed",
    )


@pytest.mark.parametrize("arity", [1, 2, 3, 5])
def test_heterogeneous_product_source_to_host(toolchain, journal, directory, arity):
    contracts = ["Finite<F>" if i % 2 == 0 else "Finite<(F, F)>" for i in range(arity)]
    values = ["items" if i % 2 == 0 else "pairs" for i in range(arity)]
    product = ", ".join(values) + ("," if arity == 1 else "")
    source = (
        SOURCE.read_text().split("module Build:", 1)[0]
        + f"""
view def pack(items: Finite<F>, pairs: Finite<(F, F)>) -> ds::Product<{", ".join(contracts)}>:
    return ({product})
pub protocol Demo roles(P)(xs: Vector<F> @P, ys: Vector<F> @P, initial: F @P) -> F @P:
    selected = pack(pairs=zip(elements(xs), elements(ys)), items=elements(ys))
    result <- ordered(selected.0, initial, fn(state, item) => state + item)
    return result
"""
    )
    package, pin = compile_view(toolchain, journal, directory, source, ())
    arguments = {"xs": ["2", "3"], "ys": ["4", "5"], "initial": "7"}
    assert (
        run_view(
            toolchain, journal, directory, package, pin, "heterogeneous", arguments
        )
        == "16"
    )
    arguments["xs"] = []
    run_view(
        toolchain,
        journal,
        directory,
        package,
        pin,
        "heterogeneous-guard",
        arguments,
        refuses="entry-host-run-failed",
    )
