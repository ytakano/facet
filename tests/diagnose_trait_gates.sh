#!/bin/sh
set -eu

root_dir=$(cd "$(dirname "$0")/.." && pwd)
cd "$root_dir"

file=tests/valid/function/generic_direct_call_explicit.facet
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

if dune exec ocaml/main.exe -- --diagnose-trait-gates "$file" >"$tmp" 2>&1; then
  if grep -Eq '^trait-no-receiver-body-summary: (ok|fail)$' "$tmp"; then
    printf 'ok   --diagnose-trait-gates %s\n' "$file"
  else
    printf 'FAIL --diagnose-trait-gates %s: missing diagnostic line\n' "$file"
    cat "$tmp"
    exit 1
  fi
else
  printf 'FAIL --diagnose-trait-gates %s: command failed\n' "$file"
  cat "$tmp"
  exit 1
fi

