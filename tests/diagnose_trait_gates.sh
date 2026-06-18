#!/bin/sh
set -eu

root_dir=$(cd "$(dirname "$0")/.." && pwd)
cd "$root_dir"

target_files=$(mktemp)
expected_fail=$(mktemp)
actual_fail=$(mktemp)
expected_component_fail=$(mktemp)
actual_component_fail=$(mktemp)
trap "rm -f \"$target_files\" \"$expected_fail\" \"$actual_fail\" \"$expected_component_fail\" \"$actual_component_fail\"" EXIT

find tests/valid \( -path "*direct*" -o -path "*trait*" \) -type f -name "*.facet" | sort >"$target_files"

printf "%s\n" \
  tests/valid/function/local_let_rec_direct_call.facet \
  tests/valid/lifetime/hrt_direct_call_unchanged.facet \
  tests/valid/trait/assoc_projection_call_arg_compat.facet \
  tests/valid/type_safety_ready_gap/direct_call.facet \
  >"$expected_fail"

printf "%s\n" \
  tests/valid/function/local_let_rec_direct_call.facet:main \
  tests/valid/lifetime/hrt_direct_call_unchanged.facet:caller \
  tests/valid/trait/assoc_projection_call_arg_compat.facet:main \
  tests/valid/type_safety_ready_gap/direct_call.facet:main \
  >"$expected_component_fail"

total=0
ok_count=0
fail_count=0
direct_present_count=0
component_body_summary_count=0
status=0

while IFS= read -r file; do
  tmp=$(mktemp)
  total=$((total + 1))

  if dune exec ocaml/main.exe -- --diagnose-trait-gates "$file" >"$tmp" 2>&1; then
    for gate in \
      trait-direct-receiver-method-present \
      trait-component-body-summary \
      trait-no-receiver-body-summary
    do
      gate_line=$(grep -E "^${gate}: (ok|fail)$" "$tmp" || true)
      case "$gate_line" in
        "$gate: ok"|"$gate: fail")
          ;;
        *)
          printf "FAIL --diagnose-trait-gates %s: missing or invalid %s line\n" "$file" "$gate"
          cat "$tmp"
          status=1
          ;;
      esac
    done

    direct_line=$(grep -E "^trait-direct-receiver-method-present: (ok|fail)$" "$tmp" || true)
    component_line=$(grep -E "^trait-component-body-summary: (ok|fail)$" "$tmp" || true)
    case "$direct_line" in
      "trait-direct-receiver-method-present: ok")
        direct_present_count=$((direct_present_count + 1))
        ;;
    esac
    case "$component_line" in
      "trait-component-body-summary: ok")
        component_body_summary_count=$((component_body_summary_count + 1))
        ;;
    esac

    component_failures_line=$(grep -E "^trait-component-body-summary-failures: [0-9][0-9]*$" "$tmp" || true)
    case "$component_failures_line" in
      "trait-component-body-summary-failures: "*)
        component_failures=${component_failures_line##*: }
        ;;
      *)
        printf "FAIL --diagnose-trait-gates %s: missing or invalid trait-component-body-summary-failures line\n" "$file"
        cat "$tmp"
        status=1
        component_failures=0
        ;;
    esac
    component_failure_detail_count=$(grep -c "^trait-component-body-summary-failure: " "$tmp" || true)
    if [ "$component_failures" -ne "$component_failure_detail_count" ]; then
      printf "FAIL --diagnose-trait-gates %s: component failure count %s did not match %s detail lines\n" \
        "$file" "$component_failures" "$component_failure_detail_count"
      cat "$tmp"
      status=1
    fi
    case "$component_line" in
      "trait-component-body-summary: ok")
        if [ "$component_failures" -ne 0 ]; then
          printf "FAIL --diagnose-trait-gates %s: component gate ok with %s failures\n" \
            "$file" "$component_failures"
          cat "$tmp"
          status=1
        fi
        ;;
      "trait-component-body-summary: fail")
        if [ "$component_failures" -eq 0 ]; then
          printf "FAIL --diagnose-trait-gates %s: component gate failed without function details\n" "$file"
          cat "$tmp"
          status=1
        fi
        sed -n "s^trait-component-body-summary-failure: ^$file:^p" "$tmp" >>"$actual_component_fail"
        ;;
    esac

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
        :
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

if ! diff -u "$expected_component_fail" "$actual_component_fail" >/dev/null; then
  printf "FAIL --diagnose-trait-gates: component body-summary failure details changed\n"
  diff -u "$expected_component_fail" "$actual_component_fail" || true
  status=1
fi

if [ "$total" -ne 100 ] || [ "$ok_count" -ne 96 ] || [ "$fail_count" -ne 4 ]; then
  printf "FAIL --diagnose-trait-gates: expected total=100 ok=96 fail=4, got total=%s ok=%s fail=%s\n" \
    "$total" "$ok_count" "$fail_count"
  status=1
fi

printf "diagnose-trait-gates: total=%s ok=%s fail=%s direct-present=%s component-body-summary=%s\n" \
  "$total" "$ok_count" "$fail_count" "$direct_present_count" "$component_body_summary_count"
exit "$status"
