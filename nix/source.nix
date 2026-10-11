# Filter declared inputs without importing mutable checkout state.
{ lib }:
{
  name,
  paths,
  exclude ? [ ],
  markdown ? false,
}:
lib.cleanSourceWith {
  name = "zkc-${name}-source";
  src = lib.cleanSource ../.;
  filter =
    path: type:
    let
      relative = lib.removePrefix "${toString ../.}/" path;
      under = selected: relative == selected || lib.hasPrefix "${selected}/" relative;
    in
    lib.any (
      selected: under selected || (type == "directory" && lib.hasPrefix "${relative}/" selected)
    ) paths
    && !(lib.any under exclude)
    && (markdown || !(lib.hasSuffix ".md" path))
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
