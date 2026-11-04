# Force source reconstruction without deleting the persistent CI store or
# requiring bit-for-bit equality of packages that retain test timing records.
{ packages, runId }:
assert runId != "";
let
  fresh = package: package.overrideAttrs { ZKC_CI_FRESH_RUN = runId; };
  lean = fresh packages.lean;
  security = fresh (packages.security.override { inherit lean; });
  arklib = fresh (packages.arklib.override { inherit security; });
in
{
  inherit lean security arklib;
}
