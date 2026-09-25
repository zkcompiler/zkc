{ fetchgit }:
{
  url,
  rev,
  hash,
  format,
}:
assert format == "canonical-git-v1";
fetchgit {
  inherit url rev hash;
  leaveDotGit = true;
  deepClone = false;
  fetchSubmodules = false;
  # Lake and fixture provenance checks need the real commit object. Upstream
  # fetchgit's retained pack can vary with the server's compression choices.
  postFetch = ''
    bash ${./normalize-git-source.sh} "$out" "$rev"
  '';
}
