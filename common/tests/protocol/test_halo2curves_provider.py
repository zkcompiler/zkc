"""Ordinary source, exact provider ports, and Native canonical BN254 results."""

import pytest


@pytest.mark.parametrize("family,modes", [
    ("g1", ["canonical", "resident", "mixed"]),
    ("g2", ["g2-canonical", "g2-resident"]),
    ("bulk", ["bulk-canonical", "bulk-resident"]),
])
def test_compiled_halo2curves_provider(toolchain, directory, journal, family, modes):
    canonical = None
    for mode in modes:
        artifact = directory / f"{mode}.json"
        program = journal.json([
            toolchain.tool("compiler", "test/zkc-halo2curves_provider-test"), "--emit", mode,
        ], keep=artifact)
        assert program[0] == "zkc.program/0"
        bindings = program[1]
        halo = [row for row in bindings if row[3].startswith("halo2curves-axiom/")]
        assert halo
        assert all(row[3] == f"halo2curves-axiom/resident/{row[1]}" for row in halo)
        assert all(row[1] != "pairing.apply" for row in halo)
        conversions = [row for row in bindings if row[1] == "representation.convert"]
        if mode.endswith("resident"):
            assert not conversions
        else:
            assert conversions
        for row in conversions:
            assert row[3] == "native/representation.convert"
            assert len(row[2]) == 1 and len(row[4]) == 2
            source, target = row[4]
            assert source.split("@")[0] == target.split("@")[0] == row[2][0]
            assert ("@halo2curves-axiom/" in source) != ("@halo2curves-axiom/" in target)
        if mode == "mixed":
            assert any(row[1:4] == ["curve.neg", ["bn254.g1"], "arkworks/curve.neg"]
                       for row in bindings)
        report = journal.json([
            toolchain.driver("resident_representations"), artifact, f"halo2curves/{mode}",
        ], keep=f"native-{mode}.json")
        assert report["returned"] == 4
        if canonical is None:
            canonical = report["canonical"]
        else:
            assert report["canonical"] == canonical, family
