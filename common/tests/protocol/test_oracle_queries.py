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
