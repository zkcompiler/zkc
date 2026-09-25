# Source boundaries exclude generated/private state and unrelated optional inputs.
{ lib }:
name: paths:
lib.cleanSourceWith {
  name = "zkc-${name}-source";
  src = lib.cleanSource ../.;
  filter =
    path: type:
    let
      relative = lib.removePrefix "${toString ../.}/" path;
    in
    lib.any (
      selected:
      relative == selected
      || lib.hasPrefix "${selected}/" relative
      || (type == "directory" && lib.hasPrefix "${relative}/" selected)
    ) paths
    # Optional integration edits do not invalidate the main Lean build.
    && !(name == "formal" && lib.hasPrefix "formal/integrations" relative)
    && !(
      builtins.elem name [
        "formal"
        "arklib"
        "compiler"
        "rust"
        "llzk"
      ]
      && lib.hasSuffix ".md" path
    )
    && !(lib.hasPrefix "result-" (baseNameOf path))
    && !(lib.hasPrefix ".venv" (baseNameOf path))
    && !(builtins.elem (baseNameOf path) [
      ".lake"
      ".venv"
      ".cache"
      ".ruff_cache"
      ".pytest_cache"
      "__pycache__"
      "build"
      "target"
      "result"
      "private"
      "node_modules"
      ".work"
    ]);
}
