#!/bin/sh
set -eu

root_dir=$(cd "$(dirname "$0")/.." && pwd)
cd "$root_dir"

target_files=$(mktemp)
expected_fail=$(mktemp)
actual_fail=$(mktemp)
expected_component_fail=$(mktemp)
actual_component_fail=$(mktemp)
expected_component_reason=$(mktemp)
actual_component_reason=$(mktemp)
expected_local_summary_count=$(mktemp)
actual_local_summary_count=$(mktemp)
expected_local_summary_detail=$(mktemp)
actual_local_summary_detail=$(mktemp)
expected_local_summary_reason=$(mktemp)
actual_local_summary_reason=$(mktemp)
trap "rm -f \"$target_files\" \"$expected_fail\" \"$actual_fail\" \"$expected_component_fail\" \"$actual_component_fail\" \"$expected_component_reason\" \"$actual_component_reason\" \"$expected_local_summary_count\" \"$actual_local_summary_count\" \"$expected_local_summary_detail\" \"$actual_local_summary_detail\" \"$expected_local_summary_reason\" \"$actual_local_summary_reason\"" EXIT

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

printf "%s\n" \
  "tests/valid/function/local_let_rec_direct_call.facet:main: local-bounds-synthetic-direct-call-ready-summary" \
  "tests/valid/lifetime/hrt_direct_call_unchanged.facet:caller: local-bounds-synthetic-direct-call-ready-summary" \
  "tests/valid/trait/assoc_projection_call_arg_compat.facet:main: local-bounds-synthetic-direct-call-ready-summary" \
  "tests/valid/type_safety_ready_gap/direct_call.facet:main: local-bounds-synthetic-direct-call-ready-summary" \
  >"$expected_component_reason"

printf "%s\n" \
  "tests/valid/function/local_let_rec_direct_call.facet:main: 1" \
  "tests/valid/lifetime/hrt_direct_call_unchanged.facet:caller: 1" \
  "tests/valid/trait/assoc_projection_call_arg_compat.facet:main: 1" \
  "tests/valid/type_safety_ready_gap/direct_call.facet:main: 1" \
  >"$expected_local_summary_count"

printf "%s\n" \
  "tests/valid/function/local_let_rec_direct_call.facet:main: __facet_local_rec_0_id_local" \
  "tests/valid/lifetime/hrt_direct_call_unchanged.facet:caller: id" \
  "tests/valid/trait/assoc_projection_call_arg_compat.facet:main: accept_item" \
  "tests/valid/type_safety_ready_gap/direct_call.facet:main: callee" \
  >"$expected_local_summary_detail"

printf "%s\n" \
  "tests/valid/function/local_let_rec_direct_call.facet:main: __facet_local_rec_0_id_local: no-direct-call-target" \
  "tests/valid/lifetime/hrt_direct_call_unchanged.facet:caller: id: no-direct-call-target" \
  "tests/valid/trait/assoc_projection_call_arg_compat.facet:main: accept_item: no-direct-call-target" \
  "tests/valid/type_safety_ready_gap/direct_call.facet:main: callee: no-direct-call-target" \
  >"$expected_local_summary_reason"

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

    component_store_safe_line=$(grep -E "^trait-component-store-safe-summary-functions: [0-9][0-9]*$" "$tmp" || true)
    case "$component_store_safe_line" in
      "trait-component-store-safe-summary-functions: "*)
        component_store_safe_functions=${component_store_safe_line##*: }
        ;;
      *)
        printf "FAIL --diagnose-trait-gates %s: missing or invalid trait-component-store-safe-summary-functions line\n" "$file"
        cat "$tmp"
        status=1
        component_store_safe_functions=0
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
    if [ "$component_failures" -gt "$component_store_safe_functions" ]; then
      printf "FAIL --diagnose-trait-gates %s: component failures %s exceeded base component-summary functions %s\n" \
        "$file" "$component_failures" "$component_store_safe_functions"
      cat "$tmp"
      status=1
    fi
    component_failure_detail_count=$(grep -c "^trait-component-body-summary-failure: " "$tmp" || true)
    component_failure_reason_count=$(grep -c "^trait-component-body-summary-failure-reason: " "$tmp" || true)
    if [ "$component_failures" -ne "$component_failure_detail_count" ]; then
      printf "FAIL --diagnose-trait-gates %s: component failure count %s did not match %s detail lines\n" \
        "$file" "$component_failures" "$component_failure_detail_count"
      cat "$tmp"
      status=1
    fi
    if [ "$component_failures" -ne "$component_failure_reason_count" ]; then
      printf "FAIL --diagnose-trait-gates %s: component failure count %s did not match %s reason lines\n" \
        "$file" "$component_failures" "$component_failure_reason_count"
      cat "$tmp"
      status=1
    fi
    invalid_component_reason_count=$(grep -Ev "^trait-component-body-summary-failure-reason: [^:][^:]*: (local-bounds-synthetic-direct-call-ready-summary|component-store-safe-summary)$" "$tmp" | grep -c "^trait-component-body-summary-failure-reason: " || true)
    if [ "$invalid_component_reason_count" -ne 0 ]; then
      printf "FAIL --diagnose-trait-gates %s: invalid component failure reason line\n" "$file"
      cat "$tmp"
      status=1
    fi

    local_reason_count=$(grep -c "^trait-component-body-summary-failure-reason: [^:][^:]*: local-bounds-synthetic-direct-call-ready-summary$" "$tmp" || true)
    local_summary_count_line_count=$(grep -c "^trait-local-bounds-synthetic-summary-failures: " "$tmp" || true)
    if [ "$local_reason_count" -ne "$local_summary_count_line_count" ]; then
      printf "FAIL --diagnose-trait-gates %s: local synthetic summary count lines %s did not match local reason lines %s\n" \
        "$file" "$local_summary_count_line_count" "$local_reason_count"
      cat "$tmp"
      status=1
    fi
    invalid_local_summary_count=$(grep -Ev "^trait-local-bounds-synthetic-summary-failures: [^:][^:]*: [0-9][0-9]*$" "$tmp" | grep -c "^trait-local-bounds-synthetic-summary-failures: " || true)
    if [ "$invalid_local_summary_count" -ne 0 ]; then
      printf "FAIL --diagnose-trait-gates %s: invalid local synthetic summary count line\n" "$file"
      cat "$tmp"
      status=1
    fi
    local_summary_detail_count=$(grep -c "^trait-local-bounds-synthetic-summary-failure: " "$tmp" || true)
    local_summary_reason_count=$(grep -c "^trait-local-bounds-synthetic-summary-failure-reason: " "$tmp" || true)
    if [ "$local_summary_detail_count" -ne "$local_summary_reason_count" ]; then
      printf "FAIL --diagnose-trait-gates %s: local synthetic summary detail lines %s did not match reason lines %s\n" \
        "$file" "$local_summary_detail_count" "$local_summary_reason_count"
      cat "$tmp"
      status=1
    fi
    invalid_local_summary_detail=$(grep -Ev "^trait-local-bounds-synthetic-summary-failure: [^:][^:]*: [^:][^:]*$" "$tmp" | grep -c "^trait-local-bounds-synthetic-summary-failure: " || true)
    if [ "$invalid_local_summary_detail" -ne 0 ]; then
      printf "FAIL --diagnose-trait-gates %s: invalid local synthetic summary detail line\n" "$file"
      cat "$tmp"
      status=1
    fi
    invalid_local_summary_reason=$(grep -Ev "^trait-local-bounds-synthetic-summary-failure-reason: [^:][^:]*: [^:][^:]*: (no-direct-call-target|direct-call-ready-summary-check)$" "$tmp" | grep -c "^trait-local-bounds-synthetic-summary-failure-reason: " || true)
    if [ "$invalid_local_summary_reason" -ne 0 ]; then
      printf "FAIL --diagnose-trait-gates %s: invalid local synthetic summary reason line\n" "$file"
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
        sed -n "s^trait-component-body-summary-failure-reason: ^$file:^p" "$tmp" >>"$actual_component_reason"
        sed -n "s^trait-local-bounds-synthetic-summary-failures: ^$file:^p" "$tmp" >>"$actual_local_summary_count"
        sed -n "s^trait-local-bounds-synthetic-summary-failure: ^$file:^p" "$tmp" >>"$actual_local_summary_detail"
        sed -n "s^trait-local-bounds-synthetic-summary-failure-reason: ^$file:^p" "$tmp" >>"$actual_local_summary_reason"
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

if ! diff -u "$expected_component_reason" "$actual_component_reason" >/dev/null; then
  printf "FAIL --diagnose-trait-gates: component body-summary failure reasons changed\n"
  diff -u "$expected_component_reason" "$actual_component_reason" || true
  status=1
fi

if ! diff -u "$expected_local_summary_count" "$actual_local_summary_count" >/dev/null; then
  printf "FAIL --diagnose-trait-gates: local synthetic summary failure counts changed\n"
  diff -u "$expected_local_summary_count" "$actual_local_summary_count" || true
  status=1
fi

if ! diff -u "$expected_local_summary_detail" "$actual_local_summary_detail" >/dev/null; then
  printf "FAIL --diagnose-trait-gates: local synthetic summary failure details changed\n"
  diff -u "$expected_local_summary_detail" "$actual_local_summary_detail" || true
  status=1
fi

if ! diff -u "$expected_local_summary_reason" "$actual_local_summary_reason" >/dev/null; then
  printf "FAIL --diagnose-trait-gates: local synthetic summary failure reasons changed\n"
  diff -u "$expected_local_summary_reason" "$actual_local_summary_reason" || true
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
