"""Generated oracle read primitives retain actual-domain stops on the native VM."""


def test_oracle_query_domain_and_prefix(toolchain, directory, journal):
    artifacts = directory / "queries"
    journal.run([
        toolchain.tool("compiler", "test/zkc-oracle_table_read-test"), artifacts,
    ], keep="compiler.txt")
    journal.run([toolchain.driver("oracle_queries"), artifacts], keep="native.txt")


def test_oracle_anchor_identity_and_lookup(toolchain, directory, journal):
    artifacts = directory / "anchors"
    journal.run([
        toolchain.tool("compiler", "test/zkc-oracle_anchor_storage-test"), artifacts,
    ], keep="compiler.txt")
    journal.run([toolchain.driver("oracle_anchors"), artifacts], keep="native.txt")


def test_oracle_virtual_position_and_answer_functions(toolchain, directory, journal):
    artifacts = directory / "virtual-functions"
    journal.run([
        toolchain.tool("compiler", "test/zkc-oracle_virtual_functions-test"), artifacts,
    ], keep="compiler.txt")
    journal.run([
        toolchain.driver("oracle_virtual_functions"), artifacts,
    ], keep="native.txt")


def test_oracle_query_continuations(toolchain, directory, journal):
    artifacts = directory / "controller"
    journal.run([
        toolchain.tool("compiler", "test/zkc-oracle_query_controller-test"), artifacts,
    ], keep="compiler.txt", timeout=600)
    journal.run([
        toolchain.driver("oracle_query_controller"), artifacts,
    ], keep="native.txt")


def test_oracle_common_realization(toolchain, directory, journal):
    artifacts = directory / "common"
    # Each independently compiled module has the same bounded timeout. The
    # growing client inventory must not share one module's time allowance.
    for fixture in (
        "common-recurrence", "common-holders", "common-input", "common-shape",
        "common-contents", "common-views", "common-entries", "common-return",
        "common-empty", "common-clauses",
    ):
        journal.run([
            toolchain.tool("compiler", "test/zkc-oracle_common_realization-test"),
            artifacts, "compile", fixture,
        ], keep=f"compiler-{fixture}.txt", timeout=600)
    journal.run([toolchain.driver("oracle_common"), artifacts], keep="native.txt")


def test_oracle_merkle_layout_and_authentication(toolchain, directory, journal):
    artifacts = directory / "merkle"
    journal.run([
        toolchain.tool("compiler", "test/zkc-oracle_merkle-test"), artifacts,
    ], keep="compiler.txt", timeout=600)
    journal.run([toolchain.driver("oracle_merkle"), artifacts], keep="native.txt")


def test_oracle_commitment_roots(toolchain, directory, journal):
    artifacts = directory / "roots"
    # Bound each source client independently as the query inventory grows.
    for fixture in (
        "send-dynamic", "send-fixed", "input-dynamic", "input-fixed",
        "query-recurrence", "query-zero-trailing", "query-zero-only",
        "query-multiple", "query-mixed-kind", "query-mixed-scheme",
        "selection order is canonical", "query policies never silently fall back",
    ):
        journal.run([
            toolchain.tool("compiler", "test/zkc-oracle_commitment_roots-test"),
            artifacts, fixture,
        ], keep=f"compiler-{fixture.replace(' ', '-')}.txt", timeout=600)
    journal.run([
        toolchain.driver("oracle_commitment_roots"), artifacts,
    ], keep="native.txt")


def test_oracle_query_batches(toolchain, directory, journal):
    artifacts = directory / "batches"
    for mode in (
        "paired", "individual", "reversed", "invalid-first", "invalid-later", "guard",
        "guarded-position",
    ):
        journal.run([
            toolchain.tool("compiler", "test/zkc-oracle_commitment_roots-test"),
            artifacts, f"batch-{mode}",
        ], keep=f"compiler-{mode}.txt", timeout=600)
    journal.run([
        toolchain.driver("oracle_commitment_roots"), artifacts, "batches",
    ], keep="native.txt")
