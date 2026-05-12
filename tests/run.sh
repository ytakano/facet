#!/usr/bin/env bash
set -euo pipefail

root_dir=$(cd "$(dirname "$0")/.." && pwd)
cd "$root_dir"

status=0

run_case() {
  local kind=$1
  local file=$2
  local tmp
  tmp=$(mktemp)

  if dune exec ocaml/main.exe -- "$file" >"$tmp" 2>&1; then
    if [[ "$kind" == "valid" ]]; then
      printf 'ok   %s\n' "$file"
    else
      printf 'FAIL %s: expected rejection\n' "$file"
      cat "$tmp"
      status=1
    fi
  else
    if [[ "$kind" == "invalid" ]]; then
      printf 'ok   %s\n' "$file"
    else
      printf 'FAIL %s: expected success\n' "$file"
      cat "$tmp"
      status=1
    fi
  fi

  rm -f "$tmp"
}

while IFS= read -r file; do
  [[ -n "$file" ]] || continue
  case "$file" in
    tests/valid/*) run_case valid "$file" ;;
    tests/invalid/*) run_case invalid "$file" ;;
  esac
done < <(find tests/valid tests/invalid -type f -name '*.facet' | sort)

exit "$status"
