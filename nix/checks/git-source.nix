{ runCommand, git }:
runCommand "zkc-git-source-check" { nativeBuildInputs = [ git ]; } ''
  git init --quiet first
  printf 'unchanged source\n' > first/source.txt
  git -C first add source.txt
  GIT_AUTHOR_DATE='2000-01-01T00:00:00Z' GIT_COMMITTER_DATE='2000-01-01T00:00:00Z' \
    git -C first -c user.name=zkc -c user.email=zkc@example.invalid commit --quiet -m fixture
  printf 'second revision\n' > first/later.txt
  ln -s source.txt first/link
  git -C first add later.txt link
  GIT_AUTHOR_DATE='2000-01-02T00:00:00Z' GIT_COMMITTER_DATE='2000-01-02T00:00:00Z' \
    git -C first -c user.name=zkc -c user.email=zkc@example.invalid commit --quiet -m later
  revision=$(git -C first rev-parse HEAD)
  tree=$(git -C first rev-parse 'HEAD^{tree}')
  cp -R first second
  git -C second repack -a -d
  git -C second config pack.writeReverseIndex false
  # A loose-object checkout and a packed checkout must have the same encoding.
  for source in first second; do
    GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=pack.writeReverseIndex GIT_CONFIG_VALUE_0=false \
      bash ${../normalize-git-source.sh} "$source" "$revision"
    test "$(git -C "$source" rev-parse HEAD)" = "$revision"
    test "$(git -C "$source" rev-parse 'HEAD^{tree}')" = "$tree"
    test "$(git -C "$source" rev-list --count HEAD)" = 1
    git -C "$source" fsck --strict --no-reflogs
  done
  diff -r first second
  bash ${../normalize-git-source.sh} first "$revision"
  diff -r first second
  git -C first reset --mixed HEAD
  test -z "$(git -C first status --porcelain)"
  if bash ${../normalize-git-source.sh} first 0000000000000000000000000000000000000000; then
    echo 'normalizer accepted the wrong source revision' >&2
    exit 1
  fi
  mkdir -p "$out"
  printf '%s\n' 'source identity, pack independence, idempotence and revision refusal passed' > "$out/result"
''
