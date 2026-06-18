#!/bin/sh
set -eu

root_dir=$(cd "$(dirname "$0")/.." && pwd)
cd "$root_dir"

target_files=$(mktemp)
expected_fail=$(mktemp)
actual_fail=$(mktemp)
trap "rm -f \"$target_files\" \"$expected_fail\" \"$actual_fail\"" EXIT

find tests/valid \( -path "*direct*" -o -path "*trait*" \) -type f -name "*.facet" | sort >"$target_files"

printf "%s\n" \
  tests/valid/function/local_let_rec_direct_call.facet \
  tests/valid/lifetime/hrt_direct_call_unchanged.facet \
  tests/valid/trait/assoc_projection_call_arg_compat.facet \
  tests/valid/type_safety_ready_gap/direct_call.facet \
  >"$expected_fail"

total=0
ok_count=0
fail_count=0
status=0

while IFS= read -r file; do
  tmp=$(mktemp)
  total=$((total + 1))

  if dune exec ocaml/main.exe -- --diagnose-trait-gates "$file" >"$tmp" 2>&1; then
    line=$(grep -E "^trait-no-receiver-body-summary: (ok|fail)$" "$tmp" || true)
    case "$line" in
      "trait-no-receiver-body-summary: ok")
        ok_count=$((ok_count + 1))
        ;;
      "trait-no-receiver-body-summary: fail")
        fail_count=$((fail_count + 1))
        printf "%s\n" "$file" >>"$actual_fail"
        ;;
      *)
        printf "FAIL --diagnose-trait-gates %s: missing diagnostic line\n" "$file"
        cat "$tmp"
        status=1
        ;;
    esac
  else
    printf "FAIL --diagnose-trait-gates %s: command failed\n" "$file"
    cat "$tmp"
    status=1
  fi

  rm -f "$tmp"
done <"$target_files"

if ! diff -u "$expected_fail" "$actual_fail" >/dev/null; then
  printf "FAIL --diagnose-trait-gates: diagnostic frontier changed\n"
  diff -u "$expected_fail" "$actual_fail" || true
  status=1
fi

printf "diagnose-trait-gates: total=%s ok=%s fail=%s\n" "$total" "$ok_count" "$fail_count"
exit "$status"
