# Explicit entry point for ephemeral CI cache inputs. --impure permits reading
# the checkout path during evaluation; builds still use ordinary Nix sandboxing.
{
  root,
  seed ? null,
}:
let
  flake = builtins.getFlake ("git+file://" + root);
in
import (flake.outPath + "/nix") {
  inputs = flake.inputs;
  system = "x86_64-linux";
  compilerCache = if seed == null then { } else { seed = builtins.storePath seed; };
}
