#!/bin/sh
# Compiles the modules in dependency order and checks the compiled objects with coqchk.
# Usage: ./build.sh [path-to-rocq-bin]
set -e
cd "$(dirname "$0")"
BIN="${1:-$(dirname "$(command -v coqc)")}"
PATH="$BIN:$PATH"
for f in Vectors Actions Sums LightCone Survival Resources Judges Independence Population Physical Rational Necessity Summary; do
  "$BIN/coqc" -Q . BeNice "$f.v"
done
"$BIN/coqchk" -silent -o -Q . BeNice BeNice.Summary
