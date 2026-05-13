#!/usr/bin/env bash
set -euo pipefail

root_dir=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root_dir"

status=0

run_case() {
  local file=$1
  local expected=$2
  local tmp
  tmp=$(mktemp)

  if dune exec ocaml/main.exe -- --emit-fir "$tmp" "$file" >/dev/null 2>&1; then
    if grep -Fq "$expected" "$tmp"; then
      printf 'ok   %s\n' "$file"
    else
      printf 'FAIL %s: expected FIR to contain %s\n' "$file" "$expected"
      cat "$tmp"
      status=1
    fi
  else
    printf 'FAIL %s: --emit-fir failed\n' "$file"
    status=1
  fi

  rm -f "$tmp"
}

run_case tests/valid/replace/replace_through_nested_ref.facet "replace old#0 as unrestricted isize = **rr#0 as unrestricted isize"
run_case tests/valid/replace/replace_through_immut_bound_nested_mut_ref.facet "replace old#0 as unrestricted isize = **rr#0 as unrestricted isize"
run_case tests/valid/assign/assign_through_nested_ref.facet "= **rr#0 as unrestricted isize with 42"
run_case tests/valid/reborrow/reborrow_mut_from_immut_bound_nested_mut_ref.facet "= &mut **rr#0 as unrestricted isize"
run_case tests/fir/function_value_call.facet "call %t0#0 as unrestricted isize = f#0 as unrestricted fn(unrestricted isize) -> unrestricted isize"

exit "$status"
