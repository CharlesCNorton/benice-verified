#!/bin/sh
# Compiles the development and checks the compiled proof object with coqchk.
# Usage: ./build.sh [path-to-rocq-bin]
set -e
cd "$(dirname "$0")"
BIN="${1:-$(dirname "$(command -v coqc)")}"
PATH="$BIN:$PATH"
"$BIN/coqc" benice_verified.v
"$BIN/coqchk" -silent -o -Q . "" benice_verified
