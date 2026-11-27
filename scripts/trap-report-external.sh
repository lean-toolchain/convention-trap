#!/bin/sh
# Analyze another Lake repository without modifying it (design/README.md "임시 워크스페이스").
# usage: scripts/trap-report-external.sh <target-repo-path> <TargetLib> [trap-report args...]
# exit: 3 unsupported toolchain, 4 target build failure, otherwise trap-report's exit code.
set -u
TARGET=$(cd "$1" && pwd) || exit 2
LIB=$2; shift 2
TOOL=$(cd "$(dirname "$0")/.." && pwd)
want=$(cat "$TOOL/lean-toolchain"); have=$(cat "$TARGET/lean-toolchain")
if [ "$want" != "$have" ]; then
  echo "unsupported toolchain $have (supported: $want)" >&2; exit 3
fi
WS=$(mktemp -d)
cp "$TARGET/lean-toolchain" "$WS/"
cat > "$WS/lakefile.toml" <<TOML
name = "trapws"
[[require]]
name = "$LIB"
path = "$TARGET"
[[require]]
name = "convention-trap"
path = "$TOOL"
TOML
cd "$WS" || exit 2
lake exe cache get >/dev/null 2>&1 || true
lake build "$LIB" || exit 4
mods=$(cd "$TARGET" && find . -name '*.lean' -not -path './.lake/*' -not -name 'lakefile.lean' \
  | sed 's|^\./||; s|\.lean$||; s|/|.|g' | grep "^$LIB" | paste -sd, -)
"$TOOL/scripts/trap-report" --modules "$mods" --out-dir "$TARGET/trap-report" "$@"
