# CI seeds are immutable Nix inputs. Compilation remains inside the sandbox;
# no writable host cache or extra sandbox paths are needed.
{
  pkgs,
  stdenv,
  seed ? null,
  enabled ? false,
}:
let
  inherit (pkgs) lib;
  compiler = stdenv.cc.cc;
  links =
    (pkgs.ccache.links {
      unwrappedCC = compiler;
      extraConfig = "";
    }).overrideAttrs
      (old: {
        # cc-wrapper uses the compiler's version and language capabilities to
        # select C++ headers and flags, not ccache's version/capabilities.
        inherit (compiler) version;
        passthru = old.passthru // {
          inherit (compiler) langCC;
        };
      });
  cachedStdenv = pkgs.overrideCC stdenv (stdenv.cc.override { cc = links; });
in
{
  stdenv = if enabled then cachedStdenv else stdenv;
  wrap =
    name: package:
    if !enabled then
      package
    else
      # Clang 23.1.3 classifies -frandom-seed as an ignored option. Nix changes
      # that seed with $out; including it would invalidate every cached object.
      # Re-audit this exception when changing Clang. Do not apply it to GCC.
      assert compiler.isClang && compiler.version == "23.1.3";
      package.overrideAttrs (old: {
        outputs = (old.outputs or [ "out" ]) ++ [ "compilationCache" ];
        nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [
          pkgs.ccache
          pkgs.zstd
        ];
        # Product and full-check source filters have different store names.
        # Normalize only the ephemeral unpack directory so they can share
        # identical object files; the source contents remain Nix inputs.
        postUnpack = (old.postUnpack or "") + ''
          chmod u+w "$(dirname "$sourceRoot")"
          mv "$sourceRoot" source
          sourceRoot=source
        '';
        preConfigure = ''
          export CCACHE_DIR="$TMPDIR/zkc-ccache"
          export CCACHE_CONFIGPATH="$TMPDIR/zkc-ccache.conf"
          export CCACHE_BASEDIR="$NIX_BUILD_TOP"
          export CCACHE_COMPILERCHECK=content
          export CCACHE_DEPEND=true
          export CCACHE_MAXSIZE=128M
          export CCACHE_NAMESPACE=${lib.escapeShellArg "${stdenv.cc}-${name}"}
          export CCACHE_SLOPPINESS=random_seed
          touch "$CCACHE_CONFIGPATH"
          mkdir -p "$CCACHE_DIR"
          ${lib.optionalString (seed != null) ''
            if [ -f ${seed}/${name}/cache.tar.zst ]; then
              tar --zstd -xf ${seed}/${name}/cache.tar.zst -C "$CCACHE_DIR"
              chmod -R u+w "$CCACHE_DIR"
            fi
          ''}
          ccache --zero-stats
        ''
        + (old.preConfigure or "");
        postInstall = (old.postInstall or "") + ''
          mkdir -p "$compilationCache"
          ccache --cleanup
          ccache --show-stats
          ccache --print-stats --format json > "$compilationCache/stats.json"
          tar --zstd -cf "$compilationCache/cache.tar.zst" -C "$CCACHE_DIR" .
        '';
      });
}
