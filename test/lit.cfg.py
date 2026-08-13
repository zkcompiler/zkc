import os
import shutil

import lit.formats
from lit.llvm import llvm_config

config.name = "ZKC"
# LLVM 23 rejects the deprecated external-shell mode.  The internal shell is
# the portable lit contract and is exercised by the repository's full suite.
config.test_format = lit.formats.ShTest(False)
config.suffixes = [".mlir", ".test"]
config.excludes = ["Inputs", "lib"]
config.test_source_root = os.path.dirname(__file__)
config.test_exec_root = os.path.join(config.zkc_obj_root, "test")

llvm_config.use_default_substitutions()
llvm_config.with_environment("PATH", config.llvm_tools_dir, append_path=True)
for env_name in ("CARGO_TARGET_DIR", "UV_CACHE_DIR", "XDG_CACHE_HOME"):
    if env_name in os.environ:
        llvm_config.with_environment(env_name, os.environ[env_name])
llvm_config.add_tool_substitutions(
    ["zkc-opt", "zkc-test-opt", "zkc-registry-lint", "zkc-family",
     "zkc-project",
     "zkc-translate", "zkc-run", "zkc-seal", "zkc-artifact", "zkc-derive"],
    [config.zkc_tools_dir],
)

# Differential tests run the Python reference models (the conformance
# oracle) through uv; they are skipped where uv is unavailable.
if shutil.which("uv"):
    config.available_features.add("uv")
# Cargo-backed upstream integration tests are optional. The Rust harness uses
# the host's stable toolchain and carries a locked dependency graph.
if shutil.which("cargo"):
    config.available_features.add("cargo")
config.substitutions.append(
    ("%zkc-replay-manifest",
     os.path.join(config.zkc_src_root, "evaluation", "upstream",
                  "plonky3-replay", "Cargo.toml"))
)
# The verifier emitter and its runtime crate (emit/): a cargo workspace,
# driven by the same optional-cargo gate as the replay harness.
config.substitutions.append(
    ("%zkc-emit-manifest",
     os.path.join(config.zkc_src_root, "emit", "Cargo.toml"))
)
config.substitutions.append(
    ("%zkc-emit-bindings", os.path.join(config.zkc_src_root, "emit", "bindings"))
)
config.substitutions.append(
    ("%zkc-rt-dir", os.path.join(config.zkc_src_root, "emit", "zkc-rt"))
)
config.substitutions.append(
    ("%zkc-replay-fixture",
     os.path.join(config.zkc_src_root, "evaluation", "upstream",
                  "plonky3-replay", "fixtures", "fib_babybear.json"))
)
config.substitutions.append(
    ("%zkc-duplex-fixture",
     os.path.join(config.zkc_src_root, "evaluation", "upstream",
                  "plonky3-replay", "fixtures", "duplex_babybear.json"))
)
config.substitutions.append(
    ("%uv", "uv --project " + os.path.join(config.zkc_src_root, "reference") + " run --no-sync")
)
# The re-mint tool reads the build it is judging; lit knows where that is, so
# it says, rather than the tool assuming one layout.
config.substitutions.append(
    ("%zkc-remint",
     os.path.join(config.zkc_src_root, "tools", "remint", "remint.py")
     + " --build-dir=" + config.zkc_obj_root)
)
config.substitutions.append(
    ("%zkc-registry-dir", os.path.join(config.zkc_src_root, "registry"))
)
# The full seal configuration, spelled once: the same
# flag string recurs on every sealing RUN line, and a drifted copy
# would test a different battery than the tools ship.
_registry = os.path.join(config.zkc_src_root, "registry")
config.substitutions.append(
    ("%pir-seal-full",
     "-pir-seal='protocol-vocabulary=" + os.path.join(_registry, "protocol-vocabulary.json")
     + " construction-profile-registry=" + os.path.join(_registry, "construction-profiles.json") + "'")
)
config.substitutions.append(
    ("%pir-recheck-full",
     "-pir-recheck='protocol-vocabulary=" + os.path.join(_registry, "protocol-vocabulary.json")
     + " construction-profile-registry=" + os.path.join(_registry, "construction-profiles.json") + "'")
)
config.substitutions.append(
    ("%pir-project-full",
     "-pir-project='protocol-vocabulary=" + os.path.join(_registry, "protocol-vocabulary.json")
     + " construction-profile-registry=" + os.path.join(_registry, "construction-profiles.json") + "'")
)
config.substitutions.append(
    ("%pir-project-prover-full",
     "-pir-project='endpoint-kind=prover_skeleton protocol-vocabulary="
     + os.path.join(_registry, "protocol-vocabulary.json")
     + " construction-profile-registry=" + os.path.join(_registry, "construction-profiles.json") + "'")
)
config.substitutions.append(
    ("%pir-link-authorities",
     "protocol-vocabulary=" + os.path.join(_registry, "protocol-vocabulary.json")
     + " construction-profile-registry=" + os.path.join(_registry, "construction-profiles.json"))
)
config.substitutions.append(
    ("%zkc-seal-full",
     "--protocol-vocabulary " + os.path.join(_registry, "protocol-vocabulary.json")
     + " --construction-profile-registry " + os.path.join(_registry, "construction-profiles.json"))
)
