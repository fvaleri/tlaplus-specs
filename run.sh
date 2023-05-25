#!/usr/bin/env bash
set -Eeuo pipefail

readonly TLC_VERSION="1.8.0"
readonly TLC_HOME="$HOME/.local/lib"
readonly TLC_DEFAULT_OPTS="-modelcheck -workers auto -metadir /tmp/tlc -noGenerateSpecTE"
readonly TLC_JAVA_OPTS="-Xmx12g -XX:+UseParallelGC"
readonly TLC_SPEC="${1:-}"

for x in curl java; do
  if ! command -v "$x" &>/dev/null; then
    error "Missing required utility: $x"
  fi
done

if [[ -z $TLC_SPEC ]]; then
  echo "Usage: $0 /path/to/MySpec" && exit 1
fi

if [[ ! -f $TLC_HOME/tla2tools.jar ]]; then
  mkdir -p "$TLC_HOME"
  curl https://github.com/tlaplus/tlaplus/releases/download/v"$TLC_VERSION"/tla2tools.jar \
    -Lo "$TLC_HOME"/tla2tools.jar
fi

if [[ -z ${TLC_OPTS:-} ]]; then
  TLC_OPTS="$TLC_DEFAULT_OPTS"
fi

if [[ -z ${JAVA_OPTS:-} ]]; then
  JAVA_OPTS="$TLC_JAVA_OPTS"
fi

rm -rf /tmp/tlc*

# shellcheck disable=SC2086
exec java $JAVA_OPTS -cp $TLC_HOME/tla2tools.jar tlc2.TLC $TLC_OPTS $TLC_SPEC
