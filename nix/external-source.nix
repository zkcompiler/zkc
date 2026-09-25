{ callPackage }:
url: rev:
let
  pins = builtins.fromJSON (builtins.readFile ./external-sources.json);
  pin = pins.${rev};
  fetchSource = callPackage ./git-source.nix { };
in
assert pin.url == url;
fetchSource {
  inherit url rev;
  inherit (pin) hash format;
}
