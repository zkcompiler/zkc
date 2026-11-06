#!/bin/sh
# Both the direct and sealed compiler must receive one complete limits argument.
# Keep executable bytes fixed while each invocation reads its own project data.
set -eu
module=
limits=
count=0
for argument do
    case "$argument" in
        --module=example=*) module=${argument#--module=example=} ;;
        --evm-limits=*)
            limits=${argument#--evm-limits=}
            count=$((count + 1))
            ;;
    esac
done
[ -n "$module" ] && [ "$count" = 1 ] || exit 8
directory=${module%/*}
[ "$limits" = "$(cat "$directory/expected-limits")" ] || exit 9
cat "$directory/response.json"
